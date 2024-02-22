package edu.colorado.plv.bounder.symbolicexecutor.state

import better.files.File
import edu.colorado.plv.bounder.{BounderUtil, PickleSpec, RunConfig}
import edu.colorado.plv.bounder.BounderUtil.{Proven, ResultSummary, Unreachable, Witnessed}
import edu.colorado.plv.bounder.ir.{CIExit, SootWrapper}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, ExactClassMatcher, LSSpec, Not, Signature}
import edu.colorado.plv.bounder.lifestate.SpecSignatures.{Activity_onResume_entry, Button_init}
import edu.colorado.plv.bounder.lifestate.ViewSpec.setOnClickListenerI
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LifecycleSpec, RxJavaSpec, SAsyncTask, SDialog, SpecSignatures, SpecSpace, ViewSpec}
import org.scalatest.funsuite.FixtureAnyFunSuite
import edu.colorado.plv.bounder.symbolicexecutor.{ApproxMode, ExecutorConfig, PreciseApproxMode, QueryFinished}
import edu.colorado.plv.bounder.synthesis.EnumModelGeneratorTest.onClickReach
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import soot.Scene
import upickle.default.write

import scala.jdk.CollectionConverters.CollectionHasAsScala

class IncorrectnessInterpreterTest extends FixtureAnyFunSuite{

  case class FixtureParam(approxMode: ApproxMode,
                          expectUnreachable: ResultSummary => Unit,
                          expectReachable: ResultSummary => Unit)

  override def withFixture(test:OneArgTest) = {
    test.apply(FixtureParam(PreciseApproxMode(true),
      expectUnreachable = r => assert(r == Proven || r == Unreachable),
      expectReachable = r => assert(r == Witnessed))
    )
  }

  test("Test initial query stack trace guided") { f =>
    val src =
      """package com.example.createdestroy;
        |import androidx.appcompat.app.AppCompatActivity;
        |import android.os.Bundle;
        |import android.util.Log;
        |import java.lang.Runnable;
        |
        |import rx.Single;
        |import rx.Subscription;
        |import rx.android.schedulers.AndroidSchedulers;
        |import rx.schedulers.Schedulers;
        |import java.util.Random;
        |
        |
        |public class MyActivity extends AppCompatActivity {
        |    static Random rand = new Random();
        |    Object o = null;
        |    Subscription subscription;
        |    Runnable target = null;
        |    static void irrelevant(){
        |      Log.i("irrelevant","app method call");
        |    }
        |    void relevant(){
        |      if(rand.nextInt(10)<5){
        |        o = new Object();
        |      }
        |    }
        |
        |    protected void doThing(){
        |       relevant();
        |       irrelevant();
        |       Log.i("b", o.toString()); //query1
        |    }
        |
        |    public class Run1 implements Runnable{
        |       @Override
        |       public void run(){
        |         MyActivity.this.doThing();
        |       }
        |    }
        |
        |    public class Run2 implements Runnable{
        |       @Override
        |       public void run(){
        |         MyActivity.this.doThing();
        |       }
        |    }
        |
        |
        |    @Override
        |    protected void onResume() {
        |       if(rand.nextInt(10)<5){ // source of non-determinism
        |         target = new Run2();
        |       }else{
        |         target = new Run1();
        |       }
        |    }
        |
        |    @Override
        |    protected void onPause() {
        |       irrelevant();
        |       if(rand.nextInt(10)<5){ // source of non-determinism
        |         o.toString(); // query2
        |       }else{
        |         target.run();
        |       }
        |    }
        |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set[LSSpec]()
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 200, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
      val symbolicExecutor = config.getAbstractInterpreter
      val iquery = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void doThing()"), BounderUtil.lineForRegex(".*query1.*".r, src), Some(".*toString.*"))

      val query = InitialQueryWithStackTrace(
        List(
          ExactClassMatcher(".*",".*", "BogoAny"),
          ExactClassMatcher(".*MyActivity\\$Run1", "void run.*", "Bogo1Run"),
          ExactClassMatcher(".*MyActivity", "void onPause.*", "BogoPause")
        )
        ,iquery)
      val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)

//      val appClasses = Scene.v().getClasses.asScala.filter{c =>
//        c.getName.contains("com.example.createdestroy")
//      }

//      PrettyPrinting.dumpDebugInfo(result, "reachStackTrace")

//      val witnessedQry = result.filter { qry => qry.qry.isWitnessed }.zipWithIndex
//
//      witnessedQry.foreach{
//        case (node, i) =>
//          println(s"Witness number: ${i}")
//          println("-----")
//          PrettyPrinting.witnessToTrace(List(node), false).foreach{tr =>
//            println(s"  ${tr}")
//          }
//      }

      assert(result.count { qry => qry.qry.isWitnessed } == 1)

      BounderUtil.throwIfStackTrace(result)
      f.expectReachable(BounderUtil.interpretResult(result, QueryFinished))

      val iquery2 = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onPause()"), BounderUtil.lineForRegex(".*query2.*".r, src), Some(".*toString.*"))
      val query2 = InitialQueryWithStackTrace(
        List(ExactClassMatcher(".*MyActivity", "void onPause.*", "BogoPause")),
        iquery2
      )

      val result2: Set[IPathNode] = symbolicExecutor.run(query2).flatMap(a => a.terminals)

      assert(result2.count { qry => qry.qry.isWitnessed } == 1)

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("convert stack to query with stack trace"){ f =>
    val trace = """	at de.danoeh.antennapod.core.service.playback.PlaybackServiceStateManager.startForeground(SourceFile:21)
                  |	at de.danoeh.antennapod.core.service.playback.PlaybackService$3.statusChanged(SourceFile:795)
                  |	at de.danoeh.antennapod.playback.base.PlaybackServiceMediaPlayer.setPlayerStatus(SourceFile:323)
                  |	at de.danoeh.antennapod.playback.base.PlaybackServiceMediaPlayer.setPlayerStatus(SourceFile:335)
                  |	at de.danoeh.antennapod.core.service.playback.LocalPSMP.resumeSync(SourceFile:343)
                  |	at de.danoeh.antennapod.core.service.playback.LocalPSMP.lambda$resume$3(SourceFile:318)
                  |	at de.danoeh.antennapod.core.service.playback.LocalPSMP.lambda$resume$3$LocalPSMP(Unknown Source:0)
                  |	at de.danoeh.antennapod.core.service.playback.-$$Lambda$LocalPSMP$J90tbi0_tjXUyTTozVsfBv3Gynw.run(Unknown Source:2)
                  |	at de.danoeh.antennapod.core.service.playback.LocalPSMP$PlayerExecutor.submit(SourceFile:95)
                  |	at de.danoeh.antennapod.core.service.playback.LocalPSMP.resume(SourceFile:316)
                  |	at de.danoeh.antennapod.core.service.playback.PlaybackService.resume(SourceFile:1523)
                  |	at de.danoeh.antennapod.core.service.playback.PlaybackService$9.onPlay(SourceFile:1680)
                  |""".stripMargin

    val iquery2 = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
      "void onPause()"), 2, Some(".*toString.*"))
    val initial = InitialQueryWithStackTrace.fromStackTrace(trace, iquery2)
    println(initial)
  }

  test("Antennapod execute reach paper motiv (Row2 Historia modified)") { f =>
    val row2Specs = Set[LSSpec](
      ViewSpec.clickWhileNotDisabled,
      LifecycleSpec.Activity_createdOnlyFirst
    )
    val row2SpecsUnsound = Set[LSSpec](
      ViewSpec.clickWhileNotDisabled.copy(existQuant = NamedPureVar("v")::NamedPureVar("a")::Nil,
        pred=And(
          And(setOnClickListenerI,  Button_init.copy(lsVars = TopVal::NamedPureVar("v")::NamedPureVar("a")::Nil)),
        Not(AbsMsg(CIExit, SpecSignatures.Activity_finish, TopVal::NamedPureVar("a")::Nil)))
      ),
      LifecycleSpec.Activity_createdOnlyFirst
    )
    val soundSpecSpace = new SpecSpace(row2Specs, Set(SAsyncTask.disallowDoubleExecute))
    val unsoundSpecSpace = new SpecSpace(row2SpecsUnsound, Set(SAsyncTask.disallowDoubleExecute))
    List(
      ("button.setEnabled(false);", Proven, soundSpecSpace),
      ("", Witnessed, soundSpecSpace),
      ("", Proven, unsoundSpecSpace),
    ).map { case (cancelLine, expectedResult, specSpace) =>
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
           |import android.widget.Button;
           |
           |public class RemoverActivity extends Activity implements OnClickListener{
           |    FeedRemover remover = null;
           |    View button = null;
           |    @Override
           |    public void onCreate(Bundle b){
           |        remover = new FeedRemover();
           |        //button = findViewById(3);
           |        button = new Button(this);
           |        button.setOnClickListener(this);
           |    }
           |    @Override
           |    public void onClick(View v){
           |        remover.execute();
           |        RemoverActivity.this.finish();
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
           |		  }
           |	  }
           |}
           |""".stripMargin

      val test: String => Unit = apk => {
        val startTime = System.nanoTime()
        assert(apk != null)

        val row2Specs = Set[LSSpec](
          ViewSpec.clickWhileNotDisabled,
          LifecycleSpec.Activity_createdOnlyFirst
        )
        val w = new SootWrapper(apk, row2Specs)

        val config = ExecutorConfig(
          stepLimit = 200, w, specSpace,
          component = Some(List("com.example.createdestroy.*")))
        implicit val om = config.outputMode
        val symbolicExecutor = config.getAbstractInterpreter

        val query = DisallowedCallin(
          "com.example.createdestroy.RemoverActivity",
          "void onClick(android.view.View)",
          SAsyncTask.disallowDoubleExecute)

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        //val fname = s"Antennapod_AsyncTask_$fileSuffix"
        //prettyPrinting.dumpDebugInfo(result, fname)
        //prettyPrinting.printWitness(result)
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        val interpretedResult = BounderUtil.interpretResult(result, QueryFinished)
        assert(interpretedResult == expectedResult)
      }

      makeApkWithSources(Map("RemoverActivity.java" -> src), MkApk.RXBase, test)
    }
  }

  test("Test reachability with irrelevant loop") { f =>
    List(
      ("!=", f.expectReachable),
    ).map { case (op, expectedResult) =>
      val src =
        s"""package com.example.createdestroy;
           |import androidx.appcompat.app.AppCompatActivity;
           |import android.os.Bundle;
           |import android.util.Log;
           |
           |import rx.Single;
           |import rx.Subscription;
           |import rx.android.schedulers.AndroidSchedulers;
           |import rx.schedulers.Schedulers;
           |
           |
           |public class MyActivity extends AppCompatActivity {
           |    Object o = null;
           |    Subscription subscription;
           |    public class Node{
           |      Node next = null;
           |    }
           |    private Node list = null;
           |
           |    @Override
           |    protected void onResume() {
           |        super.onResume();
           |
           |        subscription = Single.create(subscriber -> {
           |            try {
           |                Thread.sleep(2000);
           |            } catch (InterruptedException e) {
           |                e.printStackTrace();
           |            }
           |            subscriber.onSuccess(3);
           |        }).subscribeOn(Schedulers.newThread())
           |                .observeOn(AndroidSchedulers.mainThread())
           |                .subscribe(a -> {
           |                    while(null != list){
           |                       list = list.next;
           |                    }
           |                    Log.i("b", o.toString()); //query1
           |                });
           |        while(this.getCallingActivity() !=null){ // using gca as havoc (w/o framework model no way to know)
           |          Node tmp = new Node();
           |          tmp.next = list;
           |          list = tmp;
           |        }
           |    }
           |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
        ) ++ RxJavaSpec.spec
        val w = new SootWrapper(apk, specs)

        //TODO: set to under approx ===
        val config = ExecutorConfig(
          stepLimit = 200, w, new SpecSpace(specs, matcherSpace = Set(Activity_onResume_entry)),
          component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
        val symbolicExecutor = config.getAbstractInterpreter
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        //        val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        //          "void onCreate(android.os.Bundle)"), line, Some(".*toString.*"))

        val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
          "void lambda$onResume$1$MyActivity(java.lang.Object)"), line, Some(".*toString.*"))

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)

        //TODO: rm debug code
        //        val relClasses = Scene.v().getClasses.asScala.filter{c =>
        //          val name = c.getName
        //          name.contains("com.example.createdestroy")
        //        }

        //        println()
        //TODO:
        PrettyPrinting.dumpDebugInfo(result, "whileTest", truncate = false)
        PrettyPrinting.printWitness(result)

        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        expectedResult(BounderUtil.interpretResult(result, QueryFinished))

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("config write"){ f =>
    import upickle.default.{macroRW, read, write, ReadWriter => RW}
    val cfg = RunConfig(apkPath = "inputapk",
      outFolder = Some("outputdir"),
      initialQuery = List(), truncateOut = false,
      specSet = PickleSpec(Set(), Set(SAsyncTask.disallowDoubleExecute)),
      approxMode = PreciseApproxMode(true)
    )

    val cfgPath = File("cfg.json")
    cfgPath.overwrite(write(cfg))
  }
  test("Test switch") { f =>
    List(
      (".*query1.*".r,Witnessed),
    ).map { case (queryL, expectedResult) =>
      //TODO: This generates way way way too many states, figure out what is going on
      //TODO: Version of this test with "Runnable" instead of "SomethingAble"
      val src =
        s"""package com.example.createdestroy;
           |import androidx.appcompat.app.AppCompatActivity;
           |import android.os.Bundle;
           |import android.util.Log;
           |
           |import rx.Single;
           |import rx.Subscription;
           |import rx.android.schedulers.AndroidSchedulers;
           |import rx.schedulers.Schedulers;
           |
           |
           |public class MyActivity extends AppCompatActivity {
           |    String o = null;
           |    Subscription subscription;
           |    interface SomethingAble{
           |      void run();
           |    }
           |    public enum StupidEnum{
           |      DUMB(10),
           |      ALSODUMB(20);
           |
           |      private static final StupidEnum[] fromOrdinalLookup;
           |      static {
           |         fromOrdinalLookup = StupidEnum.values();
           |      }
           |      private final int statusValue;
           |      StupidEnum(int i){statusValue = i;}
           |    }
           |    StupidEnum stupid = StupidEnum.DUMB;
           |    SomethingAble r = null;
           |
           |    @Override
           |    protected void onCreate(Bundle savedInstanceState) {
           |        super.onCreate(savedInstanceState);
           |        r = new SomethingAble(){
           |          @Override
           |          public void run(){
           |            MyActivity.this.stupid = StupidEnum.ALSODUMB;
           |            o = null;
           |          }
           |        };
           |    }
           |
           |    @Override
           |    protected void onDestroy() {
           |        super.onDestroy();
           |        r.run();
           |        stupid = StupidEnum.ALSODUMB;
           |        if(stupid == StupidEnum.ALSODUMB){
           |        switch (stupid){
           |          case DUMB:
           |            break;
           |          case ALSODUMB:
           |            o.toString(); //query1 no NPE
           |            break;
           |        }
           |        }
           |    }
           |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val specs:Set[LSSpec] = Set()
        val w = new SootWrapper(apk, specs)
        val config = ExecutorConfig(
          stepLimit = 400, w, new SpecSpace(specs),
          component = Some(List("com.example.createdestroy.MyActivity.*")),
          outputMode = MemoryOutputMode, approxMode = PreciseApproxMode(false), printAAProgress = true)
        //outputMode = DBOutputMode("/Users/shawnmeier/Desktop/bounder_debug_data/deref2.db"))
        val symbolicExecutor = config.getAbstractInterpreter
        val i = BounderUtil.lineForRegex(queryL, src)
        val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
          "void onDestroy()"), i, Some(".*toString.*"))
        val qs = write[InitialQuery](query)

        val relClasses = Scene.v().getClasses.asScala.filter{c =>
          val name = c.getName
          name.contains("com.example.createdestroy")
        }

        val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
        PrettyPrinting.dumpDebugInfo(result, "dynamicDispatchTest2")
        //        prettyPrinting.dotWitTree(result, "dynamicDispatchTest2", true)
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        assert(BounderUtil.interpretResult(result,QueryFinished) == expectedResult)

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
      println(s"test: $queryL done")
    }
  }
}
