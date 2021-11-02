package edu.colorado.plv.bounder.symbolicexecutor

import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.LifeState.LSSpec
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LifeState, LifecycleSpec, RxJavaSpec, SAsyncTask, SDialog, SpecSpace, ViewSpec}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallinReturnNonNull, DBOutputMode, DisallowedCallin, PrettyPrinting, Reachable, ReceiverNonNull}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite
import org.slf4j.LoggerFactory
import soot.SootMethod

class Experiments extends AnyFunSuite {
  private val logger = LoggerFactory.getLogger("Experiments")
  logger.warn("Starting experiments run")
  private val prettyPrinting = new PrettyPrinting()
  private val cgMode = SparkCallGraph

  val row1Specs = Set(FragmentGetActivityNullSpec.getActivityNull,
    //          FragmentGetActivityNullSpec.getActivityNonNull, //note: not needed because non-null implies not of prev
    LifecycleSpec.Fragment_activityCreatedOnlyFirst,
    RxJavaSpec.call
  ) //++ RxJavaSpec.spec // Full RxJava spec includes no duplicate subscribe, not needed here, but still sound

  val row2Specs = Set[LSSpec](
    ViewSpec.clickWhileNotDisabled,
    LifecycleSpec.Activity_createdOnlyFirst
  )
  val row4Specs = Set(
    ViewSpec.clickWhileActive,
    ViewSpec.viewOnlyReturnedFromOneActivity,
    //              LifecycleSpec.noResumeWhileFinish,
    LifecycleSpec.Activity_createdOnlyFirst
  )
  val row5Specs = Set[LSSpec](
    SDialog.noDupeShow
  )
  def getSpecName(s:LSSpec):String = s.target.identitySignature match {
    case id if id.contains("onClick") => ???
    case id if id.contains("call") => "spec:call"
  }
  val row5Disallow = Set(SDialog.disallowDismiss)
  test("Baseline message count for framework"){
    def getCb():List[String] = ???
    val specSet = row1Specs ++ row2Specs ++ row5Specs ++ row5Disallow ++ row4Specs
    val specsByName = specSet.groupBy{s => s.target.identitySignature}.map{s =>
      if(s._2.size != 1) {
        println()
      }
      s
    }
    val specs = new SpecSpace(specSet)
    val allI = specSet.flatMap{case LSSpec(_ , _, pred, target, _) => SpecSpace.allI(pred) + target}
      .map(a => a.signatures)
    val test = (apk:String) => {

      val w = new JimpleFlowdroidWrapper(apk, cgMode,specSet)
      val resolver = new DefaultAppCodeResolver[SootMethod,soot.Unit](w)




      ???
    }
    makeApkWithSources(Map(), MkApk.RXBase, test)
  }

  test("Row1:Minimal motivating example") {
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
        val startTime = System.currentTimeMillis()
        assert(apk != null)
        //Note: subscribeIsUnique rule ommitted from this test to check state relevant to callback
        // TODO: relevance could probably be refined so this isn't necessary
        val w = new JimpleFlowdroidWrapper(apk, cgMode,row1Specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(row1Specs), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 80, w, transfer,
          component = Some(List("com.example.createdestroy.*PlayerFragment.*")))
        implicit val om = config.outputMode
        val symbolicExecutor = config.getSymbolicExecutor
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val query = CallinReturnNonNull(
          "com.example.createdestroy.PlayerFragment",
          "void call(java.lang.Object)", line,
          ".*getActivity.*")

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        val fname = s"Motiv_$fileSuffix"
        prettyPrinting.dumpDebugInfo(result, fname)
        //        prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
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
        logger.warn(s"Row 1 ${fileSuffix} time: ${System.currentTimeMillis() - startTime}")
      }

      makeApkWithSources(Map("PlayerFragment.java" -> src), MkApk.RXBase, test)
    }
  }

  test("Row2: Antennapod execute") {
    // https://github.com/AntennaPod/AntennaPod/issues/1304
    // https://github.com/AntennaPod/AntennaPod/pull/1306
    // Simplified version of Experiments row 2 (ecoop 19 meier motivating example)
    List(
      ("button.setEnabled(true);", Witnessed, "badDisable"),
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
           |import androidx.fragment.app.Fragment;
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
        val startTime = System.currentTimeMillis()
        assert(apk != null)

        val w = new JimpleFlowdroidWrapper(apk, cgMode,row2Specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(row2Specs, Set(SAsyncTask.disallowDoubleExecute)), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 200, w, transfer,
          component = Some(List("com.example.createdestroy.*RemoverActivity.*")))
        implicit val om = config.outputMode
        val symbolicExecutor = config.getSymbolicExecutor

        val query = DisallowedCallin(
          "com.example.createdestroy.RemoverActivity",
          "void onClick(android.view.View)",
          SAsyncTask.disallowDoubleExecute)

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        val fname = s"Antennapod_AsyncTask_$fileSuffix"
        prettyPrinting.dumpDebugInfo(result, fname)
        prettyPrinting.printWitness(result)
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
        assert(interpretedResult == expectedResult)
        logger.warn(s"Row 2 ${fileSuffix} time: ${System.currentTimeMillis() - startTime}")
      77}

      makeApkWithSources(Map("RemoverActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Row3: fragment start/stop can cycle"){
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
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 80, w, transfer,
        component = Some(List("com.example.createdestroy.*MyFragment.*")))
      implicit val om = config.outputMode

      // line in call is reachable
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = Reachable("com.example.createdestroy.MyFragment",
        "void call(java.lang.Object)",line)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      val fname = s"UnreachableLocation"
      prettyPrinting.dumpDebugInfo(result, fname)
      //      prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
      assert(interpretedResult == Witnessed)

      //line in call cannot throw npe since s is initialized
      val query2 = ReceiverNonNull("com.example.createdestroy.MyFragment",
        "void call(java.lang.Object)",line)
      val result2 = symbolicExecutor.run(query2).flatMap(a => a.terminals)
      val interpretedResult2 = BounderUtil.interpretResult(result2,QueryFinished)
      assert(interpretedResult2 == Proven)
    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }

  test("row 5: Yamba dismiss") {
    // Yamba https://github.com/learning-android/Yamba/pull/1/commits/90c1fe3e5e58fb87c3c59b1a271c6e43c9422eb6
    //TODO: why does this take 30 min?
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
        val startTime = System.currentTimeMillis()
        assert(apk != null)
        //Note: subscribeIsUnique rule ommitted from this test to check state relevant to callback
        // TODO: relevance could probably be refined so this isn't necessary
        val w = new JimpleFlowdroidWrapper(apk, cgMode,row5Specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(row5Specs, row5Disallow), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 200, w, transfer,
          component = Some(List("com.example.createdestroy.*StatusActivity.*")))
        implicit val om = config.outputMode
        val symbolicExecutor = config.getSymbolicExecutor
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val cb = symbolicExecutor.appCodeResolver.getCallbacks
        val am = symbolicExecutor.appCodeResolver.appMethods

        val query = DisallowedCallin(
          "com.example.createdestroy.StatusActivity$PostTask",
          "void onPostExecute(java.lang.String)",
          SDialog.disallowDismiss)

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        val fname = s"Yamba_$fileSuffix"
        prettyPrinting.dumpDebugInfo(result, fname)
        prettyPrinting.printWitness(result)
        //        prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
        assert(interpretedResult == expectedResult)
        logger.warn(s"Row 5 ${fileSuffix} time: ${System.currentTimeMillis() - startTime}")
      }

      makeApkWithSources(Map("StatusActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Row4: Connect bot click/finish") {
    val startTime = System.currentTimeMillis()
    List(
      ("", Witnessed),
      ("v.setOnClickListener(null);", Proven),
    ).foreach {
      case (disableClick, expected) =>
        //Click attached to different activity
        //TODO: probably need to write specification for null preventing click
        val src =
          s"""package com.example.createdestroy;
             |import androidx.appcompat.app.AppCompatActivity;
             |import android.os.Bundle;
             |import android.util.Log;
             |import android.view.View;
             |import android.os.Handler;
             |import android.view.View.OnClickListener;
             |
             |
             |public class MyActivity extends AppCompatActivity implements Runnable {
             |    String s = null;
             |    static OnClickListener listener2 = null;
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
          val startTime = System.currentTimeMillis()
          File.usingTemporaryDirectory() { tmpDir =>
            assert(apk != null)
            val dbFile = tmpDir / "paths.db"
            println(dbFile)
            implicit val dbMode = DBOutputMode(dbFile.toString, truncate = false)
            dbMode
              .startMeta()
            //            implicit val dbMode = MemoryOutputMode
            //        val specs = new SpecSpace(LifecycleSpec.spec + ViewSpec.clickWhileActive)
            val w = new JimpleFlowdroidWrapper(apk, cgMode, row4Specs)

            val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
              new SpecSpace(row4Specs), cha)
            val config = SymbolicExecutorConfig(
              stepLimit = 600, w, transfer,
              component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode)
            val symbolicExecutor = config.getSymbolicExecutor
            val line = BounderUtil.lineForRegex(".*query1.*".r, src)

            val nullUnreach = ReceiverNonNull("com.example.createdestroy.MyActivity$1",
              "void onClick(android.view.View)", line, Some(".*toString.*"))
            val nullUnreachRes = symbolicExecutor.run(nullUnreach, dbMode).flatMap(a => a.terminals)
            prettyPrinting.dumpDebugInfo(nullUnreachRes, s"ConnectBotRow4_${expected}")
            assert(nullUnreachRes.nonEmpty)
            BounderUtil.throwIfStackTrace(nullUnreachRes)
            prettyPrinting.printWitness(nullUnreachRes)
            assert(BounderUtil.interpretResult(nullUnreachRes, QueryFinished) == expected)
            //  dbFile.copyToDirectory(File("/Users/shawnmeier/Desktop/Row3"))
          }

          logger.warn(s"Row 4 ${expected} time: ${System.currentTimeMillis() - startTime}")
        }
        makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase,
          test)
    }
    println(s"Test took ${startTime - System.currentTimeMillis()} milliseconds")
  }

}
