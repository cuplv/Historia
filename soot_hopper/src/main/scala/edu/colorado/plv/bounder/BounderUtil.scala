package edu.colorado.plv.bounder

import java.util.Collections
import better.files.File
import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, CmdNotImplemented, CmdWrapper, FieldReference, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, IRWrapper, If, InternalMethodInvoke, InternalMethodReturn, Invoke, InvokeCmd, Loc, LocalWrapper, MethodLoc, NopCmd, ReturnCmd, SkippedInternalMethodInvoke, SkippedInternalMethodReturn, SpecialInvoke, StaticFieldReference, SwitchCmd, ThrowCmd, VirtualInvoke}
import edu.colorado.plv.bounder.symbolicexecutor.{AppCodeResolver, ExecutorConfig, QueryFinished, QueryInterrupted, QueryResult}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, IPathNode, InitialQuery, Live, NoOutputMode, OutputMode, PathNode, Qry, WitnessedQry}

import scala.annotation.tailrec
import scala.collection.mutable
import scala.sys.process._
import scala.util.matching.Regex
import upickle.default.{macroRW, read, write, ReadWriter => RW}

import scala.jdk.CollectionConverters._

object BounderUtil {
  private var sidCache:Option[String] = None
  def systemID(): String = {
    if(sidCache.isEmpty)
      sidCache = Some(runCmdStdout("uname -a").trim)

    sidCache.get
  }
  def isMac():Boolean = {
    runCmdStdout("uname").trim == "Darwin" //TODO: add other uname results for other mac variants
  }
  sealed trait MaxPathCharacterization
  case object SingleMethod extends MaxPathCharacterization
  case object SingleCallbackMultiMethod extends MaxPathCharacterization
  case object MultiCallback extends MaxPathCharacterization

  case object UnknownCharacterization extends MaxPathCharacterization
  object MaxPathCharacterization{
    implicit val rw:RW[MaxPathCharacterization] = upickle.default.readwriter[String].bimap[MaxPathCharacterization](
      {
        case SingleMethod => "SingleMethod"
        case SingleCallbackMultiMethod => "SingleCallbackMultiMethod"
        case MultiCallback => "MultiCallback"
        case UnknownCharacterization => "UnknownCharacterization"
      },
      {
        case "SingleMethod" => SingleMethod
        case "SingleCallbackMultiMethod" => SingleCallbackMultiMethod
        case "MultiCallback" => MultiCallback
        case "UnknownCharacterization" => UnknownCharacterization
      }
    )
  }

  def reduceCharacterization(c1:MaxPathCharacterization, c2:MaxPathCharacterization):MaxPathCharacterization =
    (c1,c2) match{
      case (SingleMethod,v) => v
      case (v,SingleMethod) => v
      case (SingleCallbackMultiMethod,v) => v
      case (v,SingleCallbackMultiMethod) => v
      case (MultiCallback,MultiCallback) => MultiCallback
    }
  def characterizeMaxPath(result: Set[IPathNode])(implicit mode : OutputMode):MaxPathCharacterization = {
    if(mode == NoOutputMode){
      return UnknownCharacterization
    }

    def characterizePath(node:IPathNode)(implicit mode : OutputMode):MaxPathCharacterization = {
      val methodsInPath:List[Loc] = node.methodsInPath
      methodsInPath.foldLeft(SingleMethod:MaxPathCharacterization){(acc,v) => v match {
        case CallbackMethodInvoke(_,_) => reduceCharacterization(acc,MultiCallback)
        case CallbackMethodReturn(_, _,_) => reduceCharacterization(acc,MultiCallback)
        case InternalMethodReturn(_, _, _) => reduceCharacterization(acc,SingleCallbackMultiMethod)
        case InternalMethodInvoke(_, _, _) => reduceCharacterization(acc,SingleCallbackMultiMethod)
        case _ => acc // callins and skipped internal methods
      }}
    }

    if(result.nonEmpty){
      (result.map(characterizePath)).reduce(reduceCharacterization)
    } else SingleMethod
  }

  trait ResultSummary
  object ResultSummary{
    implicit val rw:RW[ResultSummary] = upickle.default.readwriter[String].bimap[ResultSummary](
      {
        case Proven => "Proven"
        case Witnessed => "Witnessed"
        case Timeout => "Timeout"
        case Unreachable => "Unreachable"
        case Interrupted(reason) if reason == "timeout" => "Timeout"
        case Interrupted(reason) if reason == "Witnessed" => "Witnessed"
        case Interrupted(reason) if reason == "Unreachable" => "Unreachable"
        case Interrupted(reason) => s"I$reason"
      }
      ,
      {
        case "Proven" => Proven
        case "Timeout" => Timeout
        case "Unreachable" => Unreachable
        case "Witnessed" => Witnessed
        case v if v.startsWith("I") => //TODO: figure out why these get nested and fix it, until then this hack un-nests
          val inner = v.dropWhile(c => c == 'I')
          if(inner == "timeout")
            Timeout
          else if(inner == "Witnessed")
            Witnessed
          else if(inner == "Unreachable" )
            Unreachable
          else
            Interrupted(inner)
      }
    )
  }
  case object Proven extends ResultSummary
  case object Witnessed extends ResultSummary
  case object Timeout extends ResultSummary
  case object Unreachable extends ResultSummary
  case class Interrupted(reason:String) extends ResultSummary
  def throwIfStackTrace(result:Set[IPathNode]) = {
    result.foreach{pn =>
      if(pn.getError.isDefined)
        throw pn.getError.get
    }
  }

  case class DepthResult(depth:Int, ordDepth:Int, cbDepth:Int, status:ResultSummary)
  object DepthResult{
    implicit val rw:RW[DepthResult] = macroRW
  }

  def countCb(terminal:List[IPathNode])(implicit mode:OutputMode):Int = {
    val terminalsInd = terminal.map{t => (Some(t), 0)}
    @tailrec
    def iCbCount(terminalsInd: List[(Option[IPathNode], Int)]): List[(Option[IPathNode], Int)] = {
      val upd = terminalsInd.map{
        case (Some(n), ind) => n.qry.loc match{
          case CallbackMethodInvoke(_,_) => (Some(n), ind+1)
          case _ => (Some(n),ind)
        }
        case (None, ind) => (None, ind)
      }
      val succ = upd.flatMap{
        case (Some(n),ind) if n.succ.nonEmpty => n.succ.map(s=> (Some(s),ind))
        case (Some(n),ind)  => List((None, ind)) //if n.succ.isEmpty
        case (None,ind) => List((None,ind))
      }
      if(succ == terminalsInd)
        succ
      else
        iCbCount(succ)
    }
    iCbCount(terminalsInd).map{
      case (None,i) => i
      case v => println(v); throw new IllegalStateException("bad logic in countcb")
    }.min
//    if(terminal.isEmpty)
//      return 0
//    val countContrib = terminal.map { n =>
//      n.qry.loc match {
//        case CallbackMethodInvoke(tgtClazz, fmwName, loc) => 1 + countCb(n.succ)
//        case _ => countCb(n.succ)
//      }
//    }
//    countContrib.min
  }

  def computeDepthOfWitOrLive(terminals: Set[IPathNode], queryResult: QueryResult)(implicit mode: OutputMode):DepthResult = {
    val resultSummary = BounderUtil.interpretResult(terminals, queryResult)
    resultSummary match {
      case Witnessed =>
        val witNodes = terminals.filter(node => node.qry.searchState match {
          case WitnessedQry(_) => true
          case _ => false
        })
        DepthResult(witNodes.map(_.depth).min, witNodes.map(_.ordDepth).min, countCb(witNodes.toList), Witnessed)
      case Timeout =>
        val liveNodes = terminals.filter(node => node.qry.isLive && node.subsumed.isEmpty)
        DepthResult(liveNodes.map(_.depth).min, liveNodes.map(_.ordDepth).min,countCb(liveNodes.toList), Timeout)
      case a  if terminals.nonEmpty =>
        DepthResult(terminals.map(_.depth).max,terminals.map(_.ordDepth).max,terminals.map(v => countCb(List(v))).max, a)
      case a =>
        DepthResult(-1,-1,-1,a)
    }
  }

  def interpretResult(result: Set[IPathNode],
                      queryResult : symbolicexecutor.QueryResult = QueryFinished):ResultSummary = {
    queryResult match {
      case QueryInterrupted(reason) => Interrupted(reason)
      case QueryFinished => {
        val err = result.find(pn => pn.getError.isDefined)
        if(err.isDefined) {
          return Interrupted(err.get.getError.get.toString)
        }
        if(result.forall {
          case PathNode(Qry(_,_,BottomQry), _) => true
          case PathNode(Qry(_,_,WitnessedQry(_)), _) => false
          case PathNode(Qry(_,_,Live), true) => true
          case PathNode(Qry(_,_,Live), false) => false
          case v =>
            throw new IllegalStateException(s"Supress compiler warning, this should be unreachable, pathNode: $v")
        }) {
          return if(result.nonEmpty) Proven else Unreachable
        }
        if(result.exists{
          case PathNode(Qry(_,_, WitnessedQry(_)), _) => true
          case _ => false
        }) {
          return Witnessed
        }
        Timeout
      }
    }
  }

  def allMap[T](n1:Set[T], n2:Set[T], canMap: (T,T) => Boolean):List[Map[T,T]] = {
    if(n1.isEmpty){
      List(n2.map(n => n->n).toMap)
    }else if(n2.isEmpty){
      List(n1.map(n => n->n).toMap)
    }else{
      val h = n1.head
      n2.flatMap{tgt =>
        if(canMap(h,tgt)) {
          val next = allMap(n1.tail, n2 - tgt, canMap)
          next.map(v => v + (h -> tgt))
        }else
          List()
      }.toList
    }
  }
  def repeatingPerm[T](elems:Int=>Iterable[T], genSize: Int): Iterable[List[T]] = {
    val acc = mutable.ListBuffer[List[T]]()
    def repeatingPermRec(elems: Int=>Iterable[T], depth: Int, partResult: List[T]): Unit = depth match {
      case 0 => acc.addOne(List())
      case 1 => for (elem <- elems(0)) acc.addOne(elem :: partResult)
      case n => for (elem <- elems(n-1))
        repeatingPermRec(elems, depth - 1, elem :: partResult)
    }
    if (genSize < 0) throw new IllegalArgumentException("Negative lengths not allowed in repeatingPerm...")
    repeatingPermRec(elems, genSize, Nil)
    acc
  }

  def sanitizeString(s: String): String = {
    s.replaceAll("\\\\", "")
      .replaceAll("\\{", "")
      .replaceAll("\\}", "")
      .replaceAll("\\$", "")
      .replaceAll("\\_", "")
      .replaceAll("\\^", "")
      .replaceAll("\\.", "")
      .replaceAll("\\(", "")
      .replaceAll("\\)", "")
      .replaceAll("\\[", "")
      .replaceAll("\\]", "")
      .replaceAll("\\|", "")
      .replaceAll("\\+", "")
      .replaceAll("\\*", "")
      .replaceAll("\\?", "")
      .replaceAll("\\<", "")
      .replaceAll("\\>", "")
      .replaceAll("\\-", "")
      .replaceAll("\\=", "")
      .replaceAll("\\:", "")
      .replaceAll("\\;", "")
      .replaceAll("\\,", "")
      .replaceAll("\\/", "")
      .replaceAll("\\!", "")
      .replaceAll("\\@", "")
      .replaceAll("\\#", "")
      .replaceAll("\\%", "")
      .replaceAll("\\&", "")
      .replaceAll("\\~", "")
      .replaceAll("\\`", "")
      .replaceAll("\\'", "")
      .replaceAll("\\\"", "")
      .replaceAll("\\ ", "")
  }


  // Abstract interpretation with no widen
  def graphFixpoint[N,V](start: Set[N],
                         startVal: V,
                         botVal: V,
                         next: N=>Iterable[N],
                         comp: (V,N) => V,
                         join: (V,V)=>V ): Map[N,V] = {
    // computed : map from nodes to their outputs
    val initialComp = start.map( a=>(a -> comp(startVal,a))).toMap

    @tailrec
    def iGraphFixpoint(toVisit:Set[N], computed:Map[N,V]) :Map[N,V] = {
      if(toVisit.isEmpty) {
        computed
      } else{
        val c = toVisit.head
        val preV = computed(c)
        val nextNodes = next(c)
        val (addTo, newComp) = nextNodes.foldLeft((List[N](),computed)){
          case ((nextVisit, computed_),cNode) =>
            val oldNextV = computed_.getOrElse(cNode,botVal)
            val newNextV = comp(preV, cNode)
            val joined = join(oldNextV,newNextV)
            val nextVisit2 = if(computed_.contains(cNode) && oldNextV == joined)
              nextVisit else cNode::nextVisit
            (nextVisit2, computed_ + (cNode -> joined))
        }
        iGraphFixpoint(toVisit.tail ++ addTo, newComp)
      }
    }
    iGraphFixpoint(start, initialComp)
  }

  def graphExists[N](start: Set[N],
                       next: N=>Set[N],
                       exists: N=>Boolean
                      ):Boolean = {
    @tailrec
    def iGraphExists(toVisit: Set[N], visited: Set[N]):Boolean = {
      if(toVisit.isEmpty)
        return false
      val c = toVisit.head
      if(exists(c)){
        true
      }else{
        val nextV = next(c) -- visited
        iGraphExists(toVisit.tail.union(nextV), visited + c)
      }
    }
    iGraphExists(start, Set())
  }

  def resolveMethodEntryForAppLoc(resolver : AppCodeResolver, appLoc: AppLoc) :List[Loc]= {
    resolver.resolveCallbackEntry(appLoc.method) match {
      case Some(CallbackMethodInvoke(sig, loc)) =>
        CallbackMethodInvoke(sig, loc)::
          InternalMethodInvoke(appLoc.method.classType, appLoc.method.simpleName, appLoc.method)::Nil
      case None => {
        InternalMethodInvoke(appLoc.method.classType, appLoc.method.simpleName, appLoc.method)::Nil
      }
      case _ =>
        throw new IllegalArgumentException
    }
  }
  def resolveMethodReturnForAppLoc(resolver : AppCodeResolver, appLoc: AppLoc) :List[Loc]= {
    resolver.resolveCallbackEntry(appLoc.method) match {
      case Some(CallbackMethodInvoke(sig, loc)) =>
        CallbackMethodReturn(sig, loc, None)::
          InternalMethodReturn(appLoc.method.classType, appLoc.method.simpleName, appLoc.method)::Nil
      case None => {
        InternalMethodReturn(appLoc.method.classType, appLoc.method.simpleName, appLoc.method)::Nil
      }
      case _ =>
        throw new IllegalArgumentException
    }
  }
  /**
   * Normally we crash on unsupported instructions, but when determining relevance, all we care about is invokes
   * Since relevance scans lots of methods,
   *
   * @param loc
   * @return
   */
  def cmdAtLocationNopIfUnknown[M,C](loc: AppLoc, wrapper:IRWrapper[M,C]): CmdWrapper = {
    try {
      wrapper.cmdAtLocation(loc)
    } catch {
      case CmdNotImplemented(_) => NopCmd(loc)
    }
  }
  def lineForRegex(r:Regex, in:String):Int = {
    val lines = in.split("\n")
    lines.indexWhere(r.matches(_)) + 1 // source code line numbers start at 1
  }

  // Compute a hash of a file
  // The output of this function should match the output of running "md5 -q <file>"
  def computeHash(path: String): String = {
    import java.security.{MessageDigest, DigestInputStream}
    import java.io.{File, FileInputStream}

    val buffer = new Array[Byte](8192)
    val md5 = MessageDigest.getInstance("MD5")

    val dis = new DigestInputStream(new FileInputStream(new File(path)), md5)
    try { while (dis.read(buffer) != -1) { } } finally { dis.close() }

    md5.digest.map("%02x".format(_)).mkString
  }
  // "DYLD_LIBRARY_PATH"->"/Users/shawnmeier/software/z3/build") TODO: set dyld?
  lazy val mac = isMac()
  lazy val dy = scala.util.Properties.envOrElse("DYLD_LIBRARY_PATH",
    scala.util.Properties.envOrElse("Z3_LIB",
      scala.util.Properties.envOrElse("LD_LIBRARY_PATH",
        throw new RuntimeException("Must set DYLD_LIBRARY_PATH for z3.  Mac restrictions may apply." +
          "See https://en.wikipedia.org/wiki/System_Integrity_Protection#Functions"))))
  def runCmdFileOut(cmd:String, runDir:File,
                    outSt:String = "stdout.tct", outEr:String = "stderr.txt"):Boolean = {
    val stdoutF = runDir / outSt
    val stderrF = runDir / outEr
    if(stdoutF.exists()) stdoutF.delete()
    if(stderrF.exists()) stderrF.delete()
    val p = if(mac) {
      Process(cmd, runDir.toJava, "Z3_LIB" -> dy)
    } else {
      println("Not mac")
      Process(cmd)
    }
    val res: Int = p ! ProcessLogger(v => stdoutF.append(v + "\n"), v => stderrF.append(v + "\n"))
    res == 0
  }
  sealed trait RunResult
  case object RunTimeout extends RunResult
  case object RunSuccess extends RunResult
  case object RunFail extends RunResult

  def runCmdTimeout(cmd:String, runDir:File, timeout:Int):RunResult = {
    //TODO: test this and possibly use for exp
    val stdoutF = runDir / "stdout.txt"
    val stderrF = runDir / "stderr.txt"
    if(stdoutF.exists()) stdoutF.delete()
    if(stderrF.exists()) stderrF.delete()
    val cmdTimeout = s"timeout ${timeout}s $cmd"
    val p = if(mac) {
      Process(cmdTimeout, runDir.toJava, "Z3_LIB" -> dy)
    } else {
      println("Not mac")
      Process(cmdTimeout)
    }
    val res: Int = p ! ProcessLogger(v => stdoutF.append(v + "\n"), v => stderrF.append(v + "\n"))
    if(res == 0){
      RunSuccess
    }else if(res == 124){
      RunTimeout
    }else{
      RunFail
    }
  }
  def runCmdStdout(cmd:String):String = {
    val stdout = new StringBuilder
    val stderr = new StringBuilder
    val p = Process(cmd)
    val res = p ! ProcessLogger(v => stdout.append(v + "\n"),v => stderr.append(v + "\n"))
    if(res != 0)
      throw new RuntimeException(s"runnint cmd: ${cmd} failed\n error: ${stderr.toString}")
    stdout.toString
  }

  /**
   * Portable method for setting env vars on both *nix and Windows.
   * @see http://stackoverflow.com/a/7201825/293064
   */
  def setEnv(newEnv: Map[String, String]): Unit = {
    import java.util.{Map => JavaMap}
    try {
      val processEnvironmentClass = Class.forName("java.lang.ProcessEnvironment")
      val theEnvironmentField = processEnvironmentClass.getDeclaredField("theEnvironment")
      theEnvironmentField.setAccessible(true)
      val env = theEnvironmentField.get(null).asInstanceOf[JavaMap[String, String]]
      env.putAll(newEnv.asJava)
      val theCaseInsensitiveEnvironmentField = processEnvironmentClass.getDeclaredField("theCaseInsensitiveEnvironment")
      theCaseInsensitiveEnvironmentField.setAccessible(true)
      val cienv = theCaseInsensitiveEnvironmentField.get(null).asInstanceOf[JavaMap[String, String]]
      cienv.putAll(newEnv.asJava)
    } catch {
      case e: NoSuchFieldException =>
        try {
          val classes = classOf[Collections].getDeclaredClasses()
          val env = System.getenv()
          for (cl <- classes) {
            if (cl.getName() == "java.util.Collections$UnmodifiableMap") {
              val field = cl.getDeclaredField("m")
              field.setAccessible(true)
              val obj = field.get(env)
              val map = obj.asInstanceOf[JavaMap[String, String]]
              map.clear()
              map.putAll(newEnv.asJava)
            }
          }
        } catch {
          case e2: Exception => e2.printStackTrace()
        }

      case e1: Exception => e1.printStackTrace()
    }
  }

  def findInWitnessTree(node: IPathNode, nodeToFind: IPathNode => Boolean)
                       (implicit om: OutputMode): Option[List[IPathNode]] = {
    if(nodeToFind(node))
      Some(List(node))
    else{
      node.succ match{
        case Nil => None
        case v => v.collectFirst{
          case v2 if findInWitnessTree(v2, nodeToFind).isDefined => findInWitnessTree(v2,nodeToFind).get
        }
      }
    }
  }

  /**
   * Find name of thing being dereferenced at a location.
   *
   * @return Some(name) if it exists, None if not a dereference
   */
  def derefNameOf[M,C](loc:AppLoc, ir:IRWrapper[M,C]):Option[String] = {
    def derefNameCmd(cmd:CmdWrapper):Option[String] = cmd match {
        case AssignCmd(_, f: FieldReference, _) => Some(f.name)
        case AssignCmd(_, f: StaticFieldReference, _) => Some(f.fieldName)
        case InvokeCmd(i: SpecialInvoke, _) => Some(i.targetSignature.methodSignature)
        case InvokeCmd(i: VirtualInvoke, _) => Some(i.targetSignature.methodSignature)
        case AssignCmd(target, f: Invoke, loc) => derefNameCmd(InvokeCmd(f, loc))
        case _ => None
      }
    derefNameCmd(ir.cmdAtLocation(loc))
  }

  /**
   * Given an assign command, src, find the next place it may be dereferenced.
   * Ignore chained derefs.
   * e.g.
   * x = ... //src
   * if(?)
   *    x.toString() //find this one
   * x.toString() // find this one
   * x.toString() // don't find this one
   *
   * Only operates within a single method/basic block
   * @param m method containing the assign
   * @param src assign command sourcing the value
   * @return
   */
  def findFirstDerefFor[M,C](m:MethodLoc, src:AppLoc, ir:IRWrapper[M,C]):Set[AppLoc] = {
    val srcCmd = ir.cmdAtLocation(src)
    val srcLocal:LocalWrapper = srcCmd match{
      case AssignCmd(tgt:LocalWrapper, _,_) => tgt
      case _ =>
        throw new IllegalArgumentException(s"Source command must be assign to local, got: ${src}")
    }

    val worklist = mutable.Queue[CmdWrapper]()
    worklist.addOne(srcCmd)
    val assigned = mutable.Set[LocalWrapper]()
    assigned.addOne(srcLocal)
    val visited = mutable.Set[CmdWrapper]()
    val sinks = mutable.Set[CmdWrapper]()
    while(worklist.nonEmpty){
      val current = worklist.dequeue()
      if(!visited.contains(current)){
        visited.addOne(current)

        val successors = ir.commandNext(current)
        successors.map{ loc => ir.cmdAtLocation(loc) match{
          case next@AssignCmd(tgt:LocalWrapper, src:LocalWrapper, _) if assigned.contains(src) =>
            assigned.addOne(tgt)
            worklist.append(next)
          case next@AssignCmd(_, FieldReference(base, _ , _,_), _) if assigned.contains(base) =>
            sinks.addOne(next)
          case next@AssignCmd(_,SpecialInvoke(base, _, _,_), _) if assigned.contains(base) =>
            sinks.addOne(next)
          case next@AssignCmd(_,VirtualInvoke(base, _, _,_), _) if assigned.contains(base) =>
            sinks.addOne(next)
          case next@InvokeCmd(SpecialInvoke(base, _, _, _), _) if assigned.contains(base) =>
            sinks.addOne(next)
          case next@InvokeCmd(VirtualInvoke(base, _, _, _), _) if assigned.contains(base) =>
            sinks.addOne(next)
          case next =>
            worklist.append(next)
        }}
      }
    }
    sinks.toSet.map{(cmd:CmdWrapper) => cmd.getLoc}

//    @tailrec
//    def iFind(assigned:Set[LocalWrapper], current:CmdWrapper, visited:Set[CmdWrapper]):Set[CmdWrapper] = {
//      if(visited.contains(current)) return Set.empty
//      val nextVisited = visited + current
//      val successors = ir.commandNext(current)
//      successors.map{ loc => ir.cmdAtLocation(loc) match{
//        case next@AssignCmd(tgt:LocalWrapper, src:LocalWrapper, _) if assigned.contains(src) =>
//          iFind(assigned + tgt, next, nextVisited)
//        case next@AssignCmd(_, FieldReference(base, _ , _,_), _) if assigned.contains(base) =>
//          Set(next)
//        case next@AssignCmd(_,SpecialInvoke(base, _, _,_), _) if assigned.contains(base) =>
//          Set(next)
//        case next@AssignCmd(_,VirtualInvoke(base, _, _,_), _) if assigned.contains(base) =>
//          Set(next)
//        case next@InvokeCmd(SpecialInvoke(base, _, _, _), _) if assigned.contains(base) =>
//          Set(next)
//        case next@InvokeCmd(VirtualInvoke(base, _, _, _), _) if assigned.contains(base) =>
//          Set(next)
//        case next =>
//          iFind(assigned, next, nextVisited)
//      }}
//    }
//    iFind(Set(srcLocal), srcCmd, Set.empty).map(_.getLoc)
  }
}