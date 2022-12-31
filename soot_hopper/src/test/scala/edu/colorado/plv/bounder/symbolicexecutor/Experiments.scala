package edu.colorado.plv.bounder.symbolicexecutor

import better.files.Dsl.SymbolicOperations
import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{DepthResult, Proven, Timeout, Witnessed, interpretResult}
import edu.colorado.plv.bounder.ir.{CBEnter, CBExit, CIEnter, CIExit, JimpleFlowdroidWrapper, MessageType}
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, Signature}
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LifeState, LifecycleSpec, RxJavaSpec, SAsyncTask, SDialog, SpecSpace, ViewSpec}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.ExperimentSpecs.{row1Specs, row2Specs, row4Specs, row5Specs}
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallinReturnNonNull, DBOutputMode, DisallowedCallin, IPathNode, MemoryOutputMode, PrettyPrinting, Reachable, ReceiverNonNull}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.BeforeAndAfter
import org.scalatest.funsuite.AnyFunSuite
import org.slf4j.LoggerFactory
import upickle.default.{macroRW, read, write, ReadWriter => RW}

import scala.collection.mutable
import soot.{Scene, SootClass, SootMethod}

import scala.jdk.CollectionConverters.{CollectionHasAsScala, ListHasAsScala}
object ExperimentSpecs{
  val row1Specs = Set(FragmentGetActivityNullSpec.getActivityNull,
    LifecycleSpec.Fragment_activityCreatedOnlyFirst,
    RxJavaSpec.call
  )

  val row2Specs = Set[LSSpec](
    ViewSpec.clickWhileNotDisabled,
    LifecycleSpec.Activity_createdOnlyFirst
  )
  val row4Specs = Set(
    ViewSpec.clickWhileActive,
    ViewSpec.viewOnlyReturnedFromOneActivity,
    LifecycleSpec.Activity_createdOnlyFirst
  )
  val row5Specs = Set[LSSpec](
    SDialog.noDupeShow
  )
}
class Experiments extends AnyFunSuite with BeforeAndAfter {
  private val runVerif = true//use this to get cb/ci counts without running verifier
  private val generateTex = false //TODO: flip to generate tex files
  private val logger = LoggerFactory.getLogger("Experiments")
  logger.warn("Starting experiments run")
  private val prettyPrinting = PrettyPrinting
  private val cgMode = SparkCallGraph

  {
    val logF = File("log/logging.log")
    if(logF.exists() && logF.contentAsString.split("\\n").size > 5) {
//      throw new IllegalStateException("Please delete log file before run")
      logF.delete() //TODO: switch to exception when running exp to avoid deleting results
    }

  }
  after{
    println("Ending Experiments run")
  }

  def getSpecName(s:LSSpec):String = s.target.identitySignature match {
    case id if id.contains("onClick") =>
      if(s.pred.toString.contains("finish")) "clickFinish" else "clickDisable"
    case id if id.contains("call") => "call"
    case id if id.contains("dismiss") => "dismiss"
    case id if id.contains("getActivity") => "getActivityNull"
    case id if id.contains("onCreate") => "createOnce"
    case id if id.contains("findView") => "findView"
    case id if id.contains("onActivityCreated") => "onActivityCreated"
    case id if id.contains("Dialog_show") || id.contains("Dialogshow") => "show"
    case id if id.contains("AsyncTask_execute") || id.contains("AsyncTaskexecute") => "execute"
    case id =>
      println(id);???
  }
  val row5Disallow = Set(SDialog.disallowDismiss)
  test("Baseline message count for framework"){
    val specSet = row1Specs ++ row2Specs ++ row5Specs ++ row5Disallow ++ row4Specs ++ Set(SAsyncTask.disallowDoubleExecute)
    val specsByName = specSet.groupBy{getSpecName}.map{s =>
      assert(s._2.size == 1)
      (s._1,s._2.head)
    }

    // Note that "Subscription" is the object of interest from motiv example, but subscriber is
    // the actual class defining unsubscribe.
    val objectsOfInterest =
      ("(android.app.Activity)|(android.app.Fragment)|(rx.Subscriber)|(rx.Single)|(rx.functions.Action1)|" +
        "(rx.Single)|(android.view.View)|(android.view.View.OnClickListener)|(android.app.Dialog)|(android.os.AsyncTask)").r

    val test = (apk:String) => {

      val w = new JimpleFlowdroidWrapper(apk, cgMode,specSet)
      val config = SymbolicExecutorConfig(
        stepLimit = 80, w, new SpecSpace(Set()),
        component = Some(List(".*")))
      implicit val om = config.outputMode
      val symbolicExecutor = config.getSymbolicExecutor
      val resolver = symbolicExecutor.appCodeResolver

      val generatedFile = File("../paper2/generated")
      if(generateTex) {
        val specMacros = specsByName.map {
          case (name, spec) =>
            s"\\newcommand{\\${name}Spec}{${spec.toTex()}}"
        }
        assert(generatedFile.isDirectory)
        val specMacroFile = generatedFile / "specMacros.tex"
        if (specMacroFile.exists) {
          //        throw new IllegalArgumentException(s"file exists: ${specMacroFile.path}")
          specMacroFile.delete()
        }
        val hdr = "%%%Generated by bounder\n"
        specMacroFile.write(hdr + specMacros.mkString("\n"))
      }

      val classes = mutable.HashMap[String, SootClass]()
      var fwkClassCount = 0
      Scene.v().getClasses.forEach{c =>
        if(resolver.isFrameworkClass(c.getName) && !c.getName.startsWith("rx.")){
          fwkClassCount += 1
        }
        val cSignature = c.getName
        if(objectsOfInterest.matches(cSignature)) {
          assert(!classes.contains(cSignature), "Unexpected duplicate")
          classes.addOne(cSignature, c)
        }
      }
      println(fwkClassCount)

      // Helper class to accumulate callins and callbacks
      case class MessageList(callin:Set[Signature] = Set(), callback:Set[Signature] = Set()){
        private def sigOfMethod(sootMethod: SootMethod):Signature = {
          val sig = sootMethod.getSubSignature
          val clazz = sootMethod.getDeclaringClass.getName
          Signature(clazz,sig)
        }
        def addCb(sig:Set[Signature]):MessageList = {
          this.copy(callback = this.callback ++ sig)
        }

        def addCi(sig:Set[Signature]):MessageList = {
//          assert(!sig._2.contains("void call(java.lang.Object)"), s"bad sig for addCi: ${sig}")
          this.copy(callin = this.callin ++ sig)
        }

        def add(sootMethod: SootMethod):MessageList = {
          // Private methods can not be callins or overridden as callbacks
          // Final methods cannot be overridden as callbacks
          val newCb = if(!sootMethod.isFinal && !sootMethod.isPrivate) callback + sigOfMethod(sootMethod) else callback
          // Note: methods on interfaces are considered to be abstract
          val newCallin = if(!sootMethod.isPrivate && !sootMethod.isAbstract) callin + sigOfMethod(sootMethod) else callin
//          assert(!newCallin.contains("void call(java.lang.Object)"))
          MessageList(newCallin, newCb)
        }
        def count:String = {
          val sum = callin.size + callback.size
          sum.toString
        }
      }

      // callins and callbacks for a class can come from super classes
      val classesAndSuperMethods = classes.map{
        case (name,c) if c.isInterface =>
          (name, c.getMethods.asScala)
        case (name, c) =>
          (name, ((Scene.v().getActiveHierarchy.getSuperclassesOf(c).asScala.toSet + c) ++ c.getInterfaces.asScala)
          .flatMap{c => c.getMethods.asScala})
      }

      // Possible messages associated with each class
      val class2MsgL = classesAndSuperMethods.map{
        case (name, methodList) => (name,methodList.foldLeft(MessageList()){case (acc,m) => acc.add(m)})
      }

      /**
       * class name for paper listing
       * !!!! USE FOR DISPLAY ONLY !!!
       * @param clazz fully qualified class name
       * @return simple name used in paper
       */
      def classSmallName(clazz:String):String = {
        val lastElem = clazz.split("\\.").last
        if(lastElem == "Subscriber"){
          // subscriber is the class that defines callins, subscription is interface visible to devs
          // subscriber implements subscription
          // We just use Subscription here as the small name to simplify presentation in the paper
          "Subscription"
        }else if(lastElem.contains("$")) {
          lastElem.split("\\$").last
        } else
          lastElem
      }

      // generate column header list
      val columnNames = class2MsgL.keys.toList.sortBy{c => classSmallName(c)}
      val rowNames = specsByName.keySet.toList.sorted

      def matchesSomeI(msgType:Set[MessageType], lSSpec: LSSpec,className:String,  signature:Signature):Boolean = {
        val classAndSuper = w.getClassHierarchyConstraints.getSupertypesOf(className) + className
        classAndSuper.exists { cc =>
          val allI = SpecSpace.allI(lSSpec.pred) + lSSpec.target
          allI.exists{i =>
            msgType.contains(i.mt) &&
              i.signatures.matches(Signature(cc,signature.methodSignature))(w.getClassHierarchyConstraints)
          }
        }
      }
      val rowEnd = "\\\\"

      // map from class to set of identity signatures matched by some I in spec
      // Use identity signature to avoid double counting
      val totalUsedForClass = mutable.HashMap[String, MessageList]()
      // Generate table body data
      val rows: List[String] = rowNames.map{ specName =>
        columnNames.map{clazz =>
          val cAndSuper = symbolicExecutor.getClassHierarchy.getSubtypesOf(clazz) + clazz
          val ccb =
          println(cAndSuper)
          println(specName)

        }
        val currentSpec = specsByName(specName)
        s"\\ref{spec:$specName}"::columnNames.map{clazz =>
          val currentMessageList = class2MsgL(clazz)
          val callbacks = currentMessageList.callback.filter(ccb =>
            matchesSomeI(Set(CBEnter, CBExit),currentSpec, clazz, ccb))
          val callins = currentMessageList.callin.filter(cci =>
            matchesSomeI(Set(CIEnter, CIExit),currentSpec, clazz, cci))
          val oldMessageList = totalUsedForClass.getOrElse(clazz, MessageList())
          totalUsedForClass.addOne(clazz, oldMessageList.addCb(callbacks).addCi(callins))
//          if(count == 0) "" else count.toString // elide 0 to make table cleaner looking
          (callins.size , callbacks.size)
        }
      }.map{r => r.mkString("&") + rowEnd}

      // Generate summary line
      val summaryLineUsedLabel = "used"
      val summaryLinePosLabel = "possible"

      val rowsWithSummary = rows ++ List(
        "\\midrule",
        (summaryLineUsedLabel :: (columnNames.map{clazz =>
          val totalMsgUsed = totalUsedForClass(clazz)
          s"${totalMsgUsed.count}"
        })).mkString("&") + rowEnd,

        (summaryLinePosLabel :: (columnNames.map{clazz =>
          val msgList = class2MsgL(clazz)
          s"${msgList.count}"
        })).mkString("&") + rowEnd,
        "\\bottomrule"
      )

      // Header containing classes
      val rowsWithHdr = s"& \\multicolumn{${columnNames.size}}{l}{Framework Object}"+rowEnd::
        ("Spec"::columnNames.map(c => s"\\rotatebox{290}{\\codej{${classSmallName(c)}}}")).mkString("&") + rowEnd::
        "\\toprule"::
        rowsWithSummary

      // Table begin and end
      val tableStart = s"\\begin{tabular*}{\\linewidth}{@{\\extracolsep{\\fill}}l " +
        s"${columnNames.indices.map(_ => "r").mkString(" ") } }"
      val tableEnd = "\\end{tabular*}"

      //TODO: uncomment to regen msg count table
      if(generateTex) {
        val msgCountTableFile = generatedFile / "msgCountTable.tex"

        if (msgCountTableFile.exists())
          msgCountTableFile.delete()

        val allRows: List[String] = (tableStart :: rowsWithHdr).appended(tableEnd)
        msgCountTableFile.write(allRows.mkString("\n"))
      }

    }
    makeApkWithSources(Map(), MkApk.RXBase, test)
  }

  test("Row1:Antennapod getActivity returns null") {
    // Experiments row 1
    // Antennapod https://github.com/AntennaPod/AntennaPod/pull/2856
    List(
      ("sub.unsubscribe();", Proven, "withUnsub"),
      ("", Witnessed, "noUnsub")
    ).map { case (destroyLine, expectedResult,fileSuffix) =>
      val src =
        s"""
           |package com.example.createdestroy;
           |import android.app.Activity;
           |import android.content.Context;
           |import android.net.Uri;
           |import android.os.Bundle;
           |
           |import androidx.fragment.app.Fragment;
           |
           |import android.util.Log;
           |import android.view.LayoutInflater;
           |import android.view.View;
           |import android.view.ViewGroup;
           |
           |import rx.Single;
           |import rx.Subscription;
           |import rx.android.schedulers.AndroidSchedulers;
           |import rx.schedulers.Schedulers;
           |import rx.functions.Action1;
           |
           |
           |public class PlayerFragment extends Fragment implements Action1<Object>{
           |    Subscription sub;
           |    //Callback with irrelevant subscribe
           |    @Override
           |    // TODO: change this to onCreated for clarity in paper
           |    public void onViewCreated(View view, Bundle savedInstanceState) {
           |        Single.create(subscriber -> {
           |            subscriber.onSuccess(4);
           |        }).subscribe(r -> {
           |            r.toString();
           |        });
           |    }
           |    @Override
           |    public void onActivityCreated(Bundle savedInstanceState){
           |        sub = Single.create(subscriber -> {
           |            subscriber.onSuccess(3);
           |        }).subscribe(this);
           |    }
           |
           |    @Override
           |    public void call(Object o){
           |         Activity act = getActivity(); //query1 : act != null
           |         act.toString();
           |    }
           |
           |    @Override
           |    public void onDestroy(){
           |        $destroyLine
           |    }
           |}
           |""".stripMargin

      val test: String => Unit = apk => {
        val startTime = System.nanoTime()
        assert(apk != null)
        //Note: subscribeIsUnique rule ommitted from this test to check state relevant to callback
        // TODO: relevance could probably be refined so this isn't necessary
        val w = new JimpleFlowdroidWrapper(apk, cgMode,row1Specs)
        val config = SymbolicExecutorConfig(
          stepLimit = 200, w, new SpecSpace(row1Specs),
          component = Some(List("com.example.createdestroy.*PlayerFragment.*")))
        implicit val om = config.outputMode
        val symbolicExecutor = config.getSymbolicExecutor
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val query = CallinReturnNonNull(
          Signature("com.example.createdestroy.PlayerFragment",
          "void call(java.lang.Object)"), line,
          ".*getActivity.*")

        if(runVerif) {
          val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
          val fname = s"Motiv_$fileSuffix"
          // prettyPrinting.dumpDebugInfo(result, fname)
          //        prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
          assert(result.nonEmpty)
          BounderUtil.throwIfStackTrace(result)
          val interpretedResult = BounderUtil.interpretResult(result, QueryFinished)

          assert(interpretedResult == expectedResult)
          //        val onViewCreatedInTree: Set[List[IPathNode]] = result.flatMap{node =>
          //            findInWitnessTree(node, (p: IPathNode) =>
          //              p.qry.loc.msgSig.exists(m => m.contains("onViewCreated(")))
          //        }
          //        if(onViewCreatedInTree.nonEmpty) {
          //          println("--- witness ---")
          //          onViewCreatedInTree.head.foreach{v =>
          //            println(v.qry.loc)
          //            println(v.qry.getState)
          //            println()
          //          }
          //          println("--- end witness ---")
          //        }
          //        assert(onViewCreatedInTree.isEmpty)
          logger.warn(s"Row 1 ${fileSuffix} time(µs): ${(System.nanoTime() - startTime) / 1000.0}")
          val depthInfo = BounderUtil.computeDepthOfWitOrLive(result, QueryFinished)
          logger.warn(s"Row 1 ${fileSuffix} : ${write[DepthResult](depthInfo)} ")
        }else{
          val em = s"Row 1 skipped due to runVerif param!!!!!!!"
          println(em)
          logger.warn(em)
        }
        val messages = w.getMessages(symbolicExecutor.controlFlowResolver, new SpecSpace(row1Specs),
          symbolicExecutor.getClassHierarchy)
        logger.warn(s"Row 1 ${fileSuffix} : ${write(messages)}")
      }

      makeApkWithSources(Map("PlayerFragment.java" -> src), MkApk.RXBase, test)
    }
  }

  test("Row2: Antennapod execute") {
    // https://github.com/AntennaPod/AntennaPod/issues/1304
    // https://github.com/AntennaPod/AntennaPod/pull/1306
    // Simplified version of Experiments row 2 (ecoop 19 meier motivating example)
    List(
//      ("button.setEnabled(true);", Witnessed, "badDisable"), //test for boolean handling, works so commented out for exp run
      ("button.setEnabled(false);", Proven, "disable"),
      ("", Witnessed, "noDisable")
    ).map { case (cancelLine, expectedResult,fileSuffix) =>
      val src =
        s"""
           |package com.example.createdestroy;
           |import android.app.Activity;
           |import android.content.Context;
           |import android.net.Uri;
           |import android.os.Bundle;
           |import android.os.AsyncTask;
           |import android.app.ProgressDialog;
           |
           |import android.app.Fragment;
           |
           |import android.util.Log;
           |import android.view.LayoutInflater;
           |import android.view.View;
           |import android.view.ViewGroup;
           |import android.view.View.OnClickListener;
           |
           |
           |
           |public class RemoverActivity extends Activity implements OnClickListener{
           |    FeedRemover remover = null;
           |    View button = null;
           |    @Override
           |    public void onCreate(Bundle b){
           |        remover = new FeedRemover();
           |        button = findViewById(3);
           |        button.setOnClickListener(this);
           |    }
           |    @Override
           |    public void onClick(View v){
           |        remover.execute();
           |        $cancelLine
           |    }
           |
           |
           |    class FeedRemover extends AsyncTask<String, Void, String> {
           |		  @Override
           |		  protected void onPreExecute() {
           |		  }
           |
           |		  @Override
           |		  protected String doInBackground(String... params) {
           |			  return "";
           |		  }
           |
           |		  @Override
           |		  protected void onPostExecute(String result) {
           |        RemoverActivity.this.finish();
           |		  }
           |	  }
           |}
           |""".stripMargin

      val test: String => Unit = apk => {
        val startTime = System.nanoTime()
        assert(apk != null)

        val w = new JimpleFlowdroidWrapper(apk, cgMode,row2Specs)
        val specSpace = new SpecSpace(row2Specs, Set(SAsyncTask.disallowDoubleExecute))
        val config = SymbolicExecutorConfig(
          stepLimit = 200, w,specSpace,
          component = Some(List("com.example.createdestroy.*RemoverActivity.*")))
        implicit val om = config.outputMode
        val symbolicExecutor = config.getSymbolicExecutor

        val query = DisallowedCallin(
          "com.example.createdestroy.RemoverActivity",
          "void onClick(android.view.View)",
          SAsyncTask.disallowDoubleExecute)

        if(runVerif) {
          val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
          val fname = s"Antennapod_AsyncTask_$fileSuffix"
          // prettyPrinting.dumpDebugInfo(result, fname)
          prettyPrinting.printWitness(result)
          assert(result.nonEmpty)
          BounderUtil.throwIfStackTrace(result)
          val interpretedResult = BounderUtil.interpretResult(result, QueryFinished)
          logger.warn(s"Row 2 ${fileSuffix} time(µs): ${(System.nanoTime() - startTime) / 1000.0}")
          val depthInfo = BounderUtil.computeDepthOfWitOrLive(result, QueryFinished)
          logger.warn(s"Row 2 ${fileSuffix} : ${write[DepthResult](depthInfo)} ")
          assert(interpretedResult == expectedResult)
        }else{
          val em = s"Row 2 skipped due to runVerif param!!!!!!!"
          println(em)
          logger.warn(em)
        }
        val messages = w.getMessages(symbolicExecutor.controlFlowResolver, specSpace,
          symbolicExecutor.getClassHierarchy)
        logger.warn(s"Row 2 ${fileSuffix} : ${write(messages)}")
      }

      makeApkWithSources(Map("RemoverActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  ignore("Row3: fragment start/stop can cycle"){
    // https://github.com/AntennaPod/AntennaPod/issues/3112
    //TODO:===== not implemented yet
    ???
    val src =
      s"""
         |package com.example.createdestroy;
         |import android.app.Activity;
         |import android.content.Context;
         |import android.net.Uri;
         |import android.os.Bundle;
         |
         |import android.app.Fragment;
         |
         |import android.util.Log;
         |import android.view.LayoutInflater;
         |import android.view.View;
         |import android.view.ViewGroup;
         |
         |import rx.Single;
         |import rx.Subscription;
         |import rx.android.schedulers.AndroidSchedulers;
         |import rx.schedulers.Schedulers;
         |import rx.functions.Action1;
         |
         |
         |public class MyFragment extends Fragment implements Action1<Object>{
         |    Subscription sub;
         |    String s = null;
         |    @Override
         |    public void onActivityCreated(Bundle savedInstanceState){
         |        sub = Single.create(subscriber -> {
         |            subscriber.onSuccess(3);
         |        }).subscribe(this);
         |        s = "";
         |    }
         |
         |    @Override
         |    public void call(Object o){
         |         s.toString(); //query1 : reachable
         |    }
         |
         |}
         |""".stripMargin
    ??? // TODO: ==== implement

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        LifecycleSpec.Fragment_activityCreatedOnlyFirst
      ) ++ RxJavaSpec.spec
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val config = SymbolicExecutorConfig(
        stepLimit = 80, w,new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.*MyFragment.*")))
      implicit val om = config.outputMode

      // line in call is reachable
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = Reachable(Signature("com.example.createdestroy.MyFragment",
        "void call(java.lang.Object)"),line)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      val fname = s"UnreachableLocation"
      // prettyPrinting.dumpDebugInfo(result, fname)
      //      prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
      assert(interpretedResult == Witnessed)

      //line in call cannot throw npe since s is initialized
      val query2 = ReceiverNonNull(Signature("com.example.createdestroy.MyFragment",
        "void call(java.lang.Object)"),line)
      val result2 = symbolicExecutor.run(query2).flatMap(a => a.terminals)
      val interpretedResult2 = BounderUtil.interpretResult(result2,QueryFinished)
      assert(interpretedResult2 == Proven)
    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }

  test("row 5: Yamba dismiss") {
    // Yamba https://github.com/learning-android/Yamba/pull/1/commits/90c1fe3e5e58fb87c3c59b1a271c6e43c9422eb6
    List(
      ("if(resumed) {","}", Proven, "withCheck"),
      ("","", Witnessed, "noCheck")
    ).map { case (line1, line2, expectedResult,fileSuffix) =>
      val src =
        s"""
           |package com.example.createdestroy;
           |import android.app.Activity;
           |import android.content.Context;
           |import android.net.Uri;
           |import android.os.Bundle;
           |import android.os.AsyncTask;
           |import android.app.ProgressDialog;
           |
           |import android.util.Log;
           |import android.view.LayoutInflater;
           |import android.view.View;
           |import android.view.ViewGroup;
           |
           |import rx.Single;
           |import rx.Subscription;
           |import rx.android.schedulers.AndroidSchedulers;
           |import rx.schedulers.Schedulers;
           |import rx.functions.Action1;
           |
           |
           |public class StatusActivity extends Activity{
           |    boolean resumed = false;
           |    @Override
           |    public void onResume(){
           |      PostTask p = new PostTask();
           |      p.execute();
           |      resumed = true;
           |    }
           |
           |
           |    @Override
           |    public void onPause(){
           |      resumed = false;
           |    }
           |    class PostTask extends AsyncTask<String, Void, String> {
           |		  private ProgressDialog progress;
           |
           |		  @Override
           |		  protected void onPreExecute() {
           |			  progress = ProgressDialog.show(StatusActivity.this, "Posting",
           |					"Please wait...");
           |			  progress.setCancelable(true);
           |		  }
           |
           |		  // Executes on a non-UI thread
           |		  @Override
           |		  protected String doInBackground(String... params) {
           |			  return "Successfully posted";
           |		  }
           |
           |		  @Override
           |		  protected void onPostExecute(String result) {
           |			  $line1
           |				  progress.dismiss(); //query1
           |			  $line2
           |		  }
           |	  }
           |}
           |""".stripMargin

      val test: String => Unit = apk => {
        val startTime = System.nanoTime()
        assert(apk != null)
        //Note: subscribeIsUnique rule ommitted from this test to check state relevant to callback
        // TODO: relevance could probably be refined so this isn't necessary
        val w = new JimpleFlowdroidWrapper(apk, cgMode,row5Specs)

//        val dbFile = File("yamba_paths.db")
//
//        println(dbFile)
//        implicit val dbMode = DBOutputMode(dbFile.toString, truncate = false)
//        dbMode.startMeta()
        implicit val dbMode = MemoryOutputMode
        val specSpace = new SpecSpace(row5Specs, row5Disallow)
        val config = SymbolicExecutorConfig(
          stepLimit = 2000, w, specSpace,
          component = Some(List("com.example.createdestroy.*StatusActivity.*")), outputMode = dbMode)
        implicit val om = config.outputMode
        val symbolicExecutor = config.getSymbolicExecutor
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val cb = symbolicExecutor.appCodeResolver.getCallbacks
        val am = symbolicExecutor.appCodeResolver.appMethods

        val query = DisallowedCallin(
          "com.example.createdestroy.StatusActivity$PostTask",
          "void onPostExecute(java.lang.String)",
          SDialog.disallowDismiss)


        if(runVerif) {
          val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
          val fname = s"Yamba_$fileSuffix"
          // prettyPrinting.dumpDebugInfo(result, fname)
          prettyPrinting.printWitness(result)
          //        prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
          assert(result.nonEmpty)
          BounderUtil.throwIfStackTrace(result)
          val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
          logger.warn(s"Row 5 ${fileSuffix} time(µs): ${(System.nanoTime() - startTime)/1000.0}")
          val depthInfo = BounderUtil.computeDepthOfWitOrLive(result, QueryFinished)
          logger.warn(s"Row 5 ${fileSuffix} : ${write[DepthResult](depthInfo)} ")
          assert(interpretedResult == expectedResult)
        }else{
          val em = s"Row 5 skipped due to runVerif param!!!!!!!"
          println(em)
          logger.warn(em)
        }
        val messages = w.getMessages(symbolicExecutor.controlFlowResolver, specSpace,
          symbolicExecutor.getClassHierarchy)
        logger.warn(s"Row 5 ${fileSuffix} : ${write(messages)}")
      }

      makeApkWithSources(Map("StatusActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Row4: Connect bot click/finish") {
    val startTime = System.nanoTime()
    List(
      ("", Witnessed, "bug"),
      ("v.setOnClickListener(null);", Timeout, "fix"),
    ).foreach {
      case (disableClick, expected, fileSuffix) =>
        //Click attached to different activity
        //TODO: probably need to write specification for null preventing click
        val src =
          s"""package com.example.createdestroy;
             |import android.app.Activity;
             |import android.os.Bundle;
             |import android.util.Log;
             |import android.view.View;
             |import android.os.Handler;
             |import android.view.View.OnClickListener;
             |
             |
             |public class MyActivity extends Activity implements Runnable {
             |    String s = null;
             |    View v = null;
             |    @Override
             |    protected void onCreate(Bundle b){
             |        v = findViewById(3);
             |        v.setOnClickListener(new OnClickListener(){
             |           @Override
             |           public void onClick(View v){
             |             s.toString(); // query1
             |           }
             |        });
             |        (new Handler()).postDelayed(this, 3000);
             |    }
             |    @Override
             |    public void run(){
             |      MyActivity.this.finish();
             |      ${disableClick}
             |    }
             |    @Override
             |    protected void onResume() {
             |        s = "";
             |    }
             |
             |    @Override
             |    protected void onPause() {
             |        s = null;
             |    }
             |}""".stripMargin
        val test: String => Unit = apk => {
          File.usingTemporaryDirectory() { tmpDir =>
            val startTime = System.nanoTime()
            assert(apk != null)
            val dbFile = tmpDir / "paths.db"
            println(dbFile)
            // implicit val dbMode = DBOutputMode(dbFile.toString, truncate = false)
            // dbMode.startMeta()
            implicit val dbMode = MemoryOutputMode

            //            implicit val dbMode = MemoryOutputMode
            //        val specs = new SpecSpace(LifecycleSpec.spec + ViewSpec.clickWhileActive)
            val w = new JimpleFlowdroidWrapper(apk, cgMode, row4Specs)

            val specSpace = new SpecSpace(row4Specs)
            val config = SymbolicExecutorConfig(
              stepLimit = 2000, w, specSpace,
              component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode)
            val symbolicExecutor = config.getSymbolicExecutor
            val line = BounderUtil.lineForRegex(".*query1.*".r, src)

            val nullUnreach = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity$1",
              "void onClick(android.view.View)"), line, Some(".*toString.*"))

            if(runVerif){
              val nullUnreachRes = symbolicExecutor.run(nullUnreach, dbMode).flatMap(a => a.terminals)
              // prettyPrinting.dumpDebugInfo(nullUnreachRes, s"ConnectBotRow4_${expected}")
              assert(nullUnreachRes.nonEmpty)
              BounderUtil.throwIfStackTrace(nullUnreachRes)
              prettyPrinting.printWitness(nullUnreachRes)
              val interpretedResult: BounderUtil.ResultSummary = BounderUtil.interpretResult(nullUnreachRes, QueryFinished)
//              interpretedResult match {
//                case Timeout =>
//                  val live = nullUnreachRes.filter( a => a.qry.isLive && a.subsumed.isEmpty)
//                  val provedTo = live.map(_.ordDepth).min
//                  logger.warn(s"Row 4 ${expected} proved to ${provedTo}")
//
//              }
              val depthInfo = BounderUtil.computeDepthOfWitOrLive(nullUnreachRes, QueryFinished)
              logger.warn(s"Row 4 ${fileSuffix} : ${write[DepthResult](depthInfo)} ")
              assert(interpretedResult == expected)
              //dbFile.copyTo(File(s"/Users/shawnmeier/Desktop/Row4_${fileSuffix}.db"),true)
              logger.warn(s"Row 4 expected: ${expected} actual: ${interpretedResult}")
              logger.warn(s"Row 4 ${expected} time(µs): ${(System.nanoTime() - startTime)/1000.0}")
            }else{
              val em = s"Row 4 skipped due to runVerif param!!!!!!!"
              println(em)
              logger.warn(em)
            }
            val messages = w.getMessages(symbolicExecutor.controlFlowResolver, specSpace,
              symbolicExecutor.getClassHierarchy)
            logger.warn(s"Row 4 ${fileSuffix} : ${write(messages)}")
          }

        }
        makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase,
          test)
    }
  }

}
