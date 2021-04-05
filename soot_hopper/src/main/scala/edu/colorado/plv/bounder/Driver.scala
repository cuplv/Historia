package edu.colorado.plv.bounder

import better.files.File
import edu.colorado.plv.bounder.BounderUtil.{Proven, ResultSummary, Timeout, Unreachable, Witnessed}
import edu.colorado.plv.bounder.Driver.{Default, RunMode}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.LifeState.LSSpec
import edu.colorado.plv.bounder.lifestate.{ActivityLifecycle, FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state._
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, SymbolicExecutor, SymbolicExecutorConfig, TransferFunctions}
import scopt.OParser
import soot.SootMethod
import upickle.core.AbortException
import upickle.default.{macroRW, read, write, ReadWriter => RW}

import scala.collection.mutable.ListBuffer
import scala.util.matching.Regex

case class Action(mode:RunMode = Default,
                  baseDirOut: Option[String] = None,
                  baseDirApk:Option[String] = None,
                  config: RunConfig = RunConfig()
                 ){
  val baseDirVar = "${baseDir}"
  val outDirVar = "${baseDirOut}"
  def getApkPath:String = baseDirApk match{
    case Some(baseDir) => {
      assert(config.apkPath.contains(baseDirVar),
        s"Apk path has no $baseDirVar to substitute.  APK path value: ${config.apkPath}")
      config.apkPath.replace(baseDirVar, baseDir)
    }
    case None => {
      assert(!config.apkPath.contains(baseDirVar))
      config.apkPath
    }
  }
  def getOutFolder:String = baseDirOut match{
    case Some(outDirBase) => {
      config.outFolder.map { outF =>
        assert(outF.contains(outDirVar), s"Out dir has no $outDirVar to substitute.  OutDir value: $outF")
        outF.replace(outDirVar, outDirBase)
      }.get
    }
    case None => {
      config.outFolder.map { outF =>
        assert(!outF.contains(baseDirVar))
        outF
      }
    }.get
  }
}

case class RunConfig(apkPath:String = "",
                     outFolder:Option[String] = None,
                     componentFilter:Option[Seq[String]] = None,
                     specSet: SpecSetOption = TopSpecSet,
                     initialQuery: Option[InitialQuery] = None,
                     limit:Int = 100,
                     samples:Int = 5
                    ){
}

object RunConfig{
  implicit val rw:RW[RunConfig] = macroRW
}

object Driver {
  object RunMode{
    implicit val rw:RW[RunMode] = upickle.default.readwriter[String].bimap[RunMode](
      x => x.toString,
      {
        case v if Verify.toString == v => Verify
        case v if Info.toString == v => Info
        case v if Default.toString == v => Default
      }
    )

  }
  sealed trait RunMode
  case object Verify extends RunMode
  case object Info extends RunMode
  case object Default extends RunMode
  case object SampleDeref extends RunMode
  case object ReadDB extends RunMode

  def readDB(cfg: RunConfig, outFolder:File): Unit = {
    val dbPath = outFolder / "paths.db"
    val db = DBOutputMode(dbPath.toString())
    val liveNodes: Set[IPathNode] = db.getTerminal().map(v=>v)
    val pp = new PrettyPrinting(db)
    pp.dumpDebugInfo(liveNodes, "out", Some(outFolder.toString))
  }

  def main(args: Array[String]): Unit = {
    val builder = OParser.builder[Action]
    val parser = {
      import builder._
      OParser.sequence(
        programName("Bounder"),
        opt[String]('m',"mode").optional().text("run mode [verify, info, sampleDeref]").action{
          case ("verify",c) => c.copy(mode = Verify)
          case ("info",c) => c.copy(mode = Info)
          case ("sampleDeref",c) => c.copy(mode = SampleDeref)
          case ("readDB",c) => c.copy(mode = ReadDB)
          case (m,_) => throw new IllegalArgumentException(s"Unsupported mode $m")
        },
        opt[String]('b', "baseDirApk").optional().text("Substitute for ${baseDir} in config file")
          .action((v,c) => c.copy(baseDirApk = Some(v))),
        opt[String]('u', "baseDirOut").optional().text("Substitute for ${baseDirOut} in config file")
          .action((v,c) => c.copy(baseDirOut = Some(v))),
        opt[java.io.File]('c', "config").optional()
          .text("Json config file, use full option names as config keys.").action{(v,c) => {
            try {
              val readConfig = read[RunConfig](v)
//              readConfig.copy(baseDir = c.baseDir, baseDirOut = c.baseDirOut)
              c.copy(config = readConfig)
            }catch{
              case t:AbortException =>
                System.err.println(s"parseing json exception: ${t.clue}")
                System.err.println(s"line: ${t.line}")
                System.err.println(s"index: ${t.index}")
                System.err.println(s"col: ${t.col}")
                t.printStackTrace()
                throw t
            }
          }
        },
//        opt[String]('a', "apkFile").optional().text("Compiled Android application").action{
//          case (v,c) => c.copy(apkPath = v)
//        },
//        opt[String]('o', "outFolder").optional().text("folder to output analysis artifacts").action{
//          case (v,c) => c.copy(outFolder = Some(v))
//        },
//        opt[Seq[String]]('f', "filter").optional()
//          .valueName("com\\.example\\.foo\\.*,com\\.exaple\\.bar.* ...")
//          .action((x, c) => c.copy(componentFilter = Some(x)))
//          .text("Regex matching packages to analyze.  Note: use single back slash for regex escape on CLI."),

//        opt[Int]('l', name="limit").optional().text("Step limit for verify")
//          .action((v,c) => c.copy(limit = v)) ,
//        opt[Int]('s', name="samples").optional().text("Number of samples")
//          .action((v,c) => c.copy(limit = v))
      )
    }
    OParser.parse(parser, args, Action()) match {
      case Some(act@Action(Verify, _, _, cfg)) =>
        val componentFilter = cfg.componentFilter
        val specSet = cfg.specSet
//        val cfgw = write(cfg)
        val apkPath = act.getApkPath
        val outFolder: String = act.getOutFolder
        // Create output directory if not exists
        // TODO: move db creation code to better location
        File(outFolder).createIfNotExists(asDirectory = true)
        val initialQuery = cfg.initialQuery
          .getOrElse(throw new IllegalArgumentException("Initial query must be defined for verify"))
        val stepLimit = cfg.limit
        val outFile = (File(outFolder) / "paths.db")
        if(outFile.exists) {
          implicit val opt = File.CopyOptions(overwrite = true)
          outFile.moveTo(File(outFolder) / "paths.db1")
        }
        DBOutputMode(outFile.canonicalPath)
        val pathMode = DBOutputMode(outFile.canonicalPath)
//        val pathMode:OutputMode = outFolder match{
//          case Some(outF) =>{
//            val outFile = (File(outF) / "paths.db")
//            if(outFile.exists) {
//              implicit val opt = File.CopyOptions(overwrite = true)
//              outFile.moveTo(File(outF) / "paths.db1")
//            }
//            DBOutputMode(outFile.canonicalPath)
//          }
//          case None => MemoryOutputMode$
//        }
        val res = runAnalysis(cfg,apkPath, componentFilter,pathMode, specSet.getSpecSet(),stepLimit, initialQuery)
        val resFile = File(outFolder) / "result.txt"
        resFile.overwrite(res)
      case Some(act@Action(SampleDeref,_,_,cfg)) =>
        //TODO: set base dir
        sampleDeref(cfg, act.getApkPath, act.getOutFolder)
      case Some(act@Action(ReadDB,_,_,cfg)) =>
        readDB(cfg, File(act.getOutFolder))
      case v => throw new IllegalArgumentException(s"Argument parsing failed: $v")
    }
  }
  def detectProguard(apkPath:String):Boolean = {
    import sys.process._
    val cmd = (File(BounderSetupApplication.androidHome) / "tools" /"bin"/"apkanalyzer").toString
//    val stdout = new StringBuilder
    var stdout:List[String] = List()
    val stderr = new StringBuilder

    val status = s"$cmd -h dex packages ${apkPath.replace(" ","\\ ")}".!(ProcessLogger(v => {
      stdout = v::stdout
    }, stderr append _))
    if(status != 0){
      throw new IllegalArgumentException(s"apk: $apkPath  error: $stderr")
//      return true
    }
    stdout.exists(v => v.contains("a.a.a."))

    //    try {
//      val callGraph = CHACallGraph
//      //      val callGraph = FlowdroidCallGraph // flowdroid call graph immediately fails with "unreachable"
//      val w = new JimpleFlowdroidWrapper(apkPath, callGraph)
//      val transfer = (cha: ClassHierarchyConstraints) =>
//        new TransferFunctions[SootMethod, soot.Unit](w, new SpecSpace(Set()), cha)
//      val config = SymbolicExecutorConfig(
//        stepLimit = Some(5), w, transfer, component = None)
//      val symbolicExecutor: SymbolicExecutor[SootMethod, soot.Unit] = config.getSymbolicExecutor
//      val proguardMethod = ".* [a-z][(].*".r
//      val proguardClass = ".*[.][a-z]".r
//      symbolicExecutor.appCodeResolver.appMethods.exists { m =>
//        proguardClass.matches(m.classType) && proguardMethod.matches(m.simpleName)
//      }
//    }finally{
//      BounderSetupApplication.reset()
//    }
  }


  def sampleDeref(cfg: RunConfig, apkPath:String, outFolder:String) = {
//    val apkPath = cfg.getApkPath
    val n = cfg.samples
//    val outFolder = cfg.getOutFolder.getOrElse(
//      throw new IllegalArgumentException("Out folder must be defined for sampling"))
    val callGraph = CHACallGraph
    //      val callGraph = FlowdroidCallGraph // flowdroid call graph immediately fails with "unreachable"
    val w = new JimpleFlowdroidWrapper(apkPath, callGraph)
    val transfer = (cha: ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod, soot.Unit](w, new SpecSpace(Set()), cha)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(n), w, transfer, component = None)
    val symbolicExecutor: SymbolicExecutor[SootMethod, soot.Unit] = config.getSymbolicExecutor

    (0 until n).map{ind =>
      val outName = s"sample$ind"
      val f = File(outFolder) / s"$outName.json"
      val appLoc = symbolicExecutor.appCodeResolver.sampleDeref()
      val name = appLoc.method.simpleName
      val clazz = appLoc.method.classType
      val line = appLoc.line.lineNumber
      val qry = ReceiverNonNull(clazz, name, line)
      val writeCFG = cfg.copy(initialQuery = Some(qry),
        outFolder = cfg.outFolder.map(v => v + "/" + outName))
      if(f.exists()) f.delete()
      f.createFile()
      f.write(write(writeCFG))
    }
  }

  def dotMethod(apkPath:String, matches:Regex) = {
    val callGraph = CHACallGraph
    //      val callGraph = FlowdroidCallGraph // flowdroid call graph immediately fails with "unreachable"
    val w = new JimpleFlowdroidWrapper(apkPath, callGraph)
    val transfer = (cha: ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod, soot.Unit](w, new SpecSpace(Set()), cha)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(0), w, transfer, component = None)
    val symbolicExecutor: SymbolicExecutor[SootMethod, soot.Unit] = config.getSymbolicExecutor
    //TODO:
  }
  def runAnalysis(cfg:RunConfig, apkPath: String, componentFilter:Option[Seq[String]], mode:OutputMode,
                  specSet: Set[LSSpec], stepLimit:Int, initialQuery: InitialQuery): String = {
    val startTime = System.currentTimeMillis()
    try {
      //TODO: read location from json config
      val callGraph = CHACallGraph
//      val callGraph = FlowdroidCallGraph // flowdroid call graph immediately fails with "unreachable"
      val w = new JimpleFlowdroidWrapper(apkPath, callGraph)
      val transfer = (cha: ClassHierarchyConstraints) =>
        new TransferFunctions[SootMethod, soot.Unit](w, new SpecSpace(specSet), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(stepLimit), w, transfer, component = componentFilter, outputMode = mode)
      val symbolicExecutor: SymbolicExecutor[SootMethod, soot.Unit] = config.getSymbolicExecutor
//      val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
//        "de.danoeh.antennapod.fragment.ExternalPlayerFragment",
//        "void updateUi(de.danoeh.antennapod.core.util.playback.Playable)", 200,
//        callinMatches = ".*getActivity.*".r)
      val query: Set[Qry] = initialQuery.make(symbolicExecutor,w)
      val out = new ListBuffer[String]()
      val initialize: IPathNode => Int = mode match{
        case mode@DBOutputMode(_) => (startingNode:IPathNode) =>
          val id = mode.initializeQuery(startingNode, cfg, initialQuery)
          val tOut = s"initial query: $initialQuery   id: $id"
          println(tOut)
          out += tOut
          id
        case _ => (_:IPathNode) => 0
      }

      val results = symbolicExecutor.run(query, initialize)

      results.map{ res =>
        mode match {
          case m@DBOutputMode(_) =>
            val interpretedRes = BounderUtil.interpretResult(res._2)
            val tOut = s"id: ${res._1}   result: ${interpretedRes}"
            println(tOut)
            out += tOut
            m.writeLiveAtEnd(res._2, res._1, interpretedRes.toString)
            interpretedRes
          case _ => BounderUtil.interpretResult(res._2)
        }
      }.reduce{ reduceResults }.toString
    } finally {
      println(s"analysis time: ${(System.currentTimeMillis() - startTime) / 1000} seconds")
    }

  }
  def reduceResults(a:ResultSummary, b:ResultSummary):ResultSummary = {
    (a,b) match {
      case (Witnessed, _) => Witnessed
      case (_, Witnessed) => Witnessed
      case (_, Timeout) => Timeout
      case (Timeout, _) => Timeout
      case (Unreachable, v2) => v2
      case (v1, Unreachable) => v1
      case (v1,v2) if v1 == v2 => v1
    }
  }

}

trait SpecSetOption{
  def getSpecSet():Set[LSSpec]
}
object SpecSetOption{
  val testSpecSet: Map[String, Set[LSSpec]] = Map(
    "AntennaPod" -> Set(FragmentGetActivityNullSpec.getActivityNull,
      FragmentGetActivityNullSpec.getActivityNonNull,
      RxJavaSpec.call,
      RxJavaSpec.subscribeDoesNotReturnNull,
      RxJavaSpec.subscribeIsUniqueAndNonNull,
      ActivityLifecycle.Fragment_activityCreatedOnlyFirst
    ))
  implicit val rw:RW[SpecSetOption] = upickle.default.readwriter[String].bimap[SpecSetOption](
    {
      case SpecFile(fname) => s"file:$fname"
      case TestSpec(name) => s"testSpec:$name"
      case TopSpecSet => s"top"
    },
    str => str.split(":").toList match{
      case "file"::fname::Nil => SpecFile(fname)
      case "testSpec"::name::Nil => TestSpec(name)
      case "top"::Nil => TopSpecSet
      case _ => throw new IllegalArgumentException(s"Failure parsing SpecSetOption: $str")
    }
  )
}
case class SpecFile(fname:String) extends SpecSetOption {
  //TODO: write parser for spec set
  override def getSpecSet(): Set[LSSpec] = ???
}

case class TestSpec(name:String) extends SpecSetOption {
  override def getSpecSet(): Set[LSSpec] = SpecSetOption.testSpecSet(name)
}

case object TopSpecSet extends SpecSetOption {
  override def getSpecSet(): Set[LSSpec] = Set()
}

class ExperimentsDb{

}
