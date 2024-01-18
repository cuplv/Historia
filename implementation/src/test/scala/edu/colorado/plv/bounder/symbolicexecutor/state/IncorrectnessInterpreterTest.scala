package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, ResultSummary, Unreachable, Witnessed}
import edu.colorado.plv.bounder.ir.{CIExit, SootWrapper}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, LSSpec, Not, Signature}
import edu.colorado.plv.bounder.lifestate.SpecSignatures.{Activity_onResume_entry, Button_init}
import edu.colorado.plv.bounder.lifestate.ViewSpec.setOnClickListenerI
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LifecycleSpec, RxJavaSpec, SAsyncTask, SDialog, SpecSignatures, SpecSpace, ViewSpec}
import org.scalatest.funsuite.FixtureAnyFunSuite
import edu.colorado.plv.bounder.symbolicexecutor.{ApproxMode, ExecutorConfig, PreciseApproxMode, QueryFinished}
import edu.colorado.plv.bounder.synthesis.EnumModelGeneratorTest.onClickReach
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources

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

}
