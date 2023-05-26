package edu.colorado.plv.bounder.synthesis

import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed, interpretResult}
import edu.colorado.plv.bounder.ir.{CIEnter, CIExit, SootWrapper}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, LSAnyPred, LSSpec, NS, Not, OAbsMsg, Or, Signature}
import edu.colorado.plv.bounder.lifestate.SAsyncTask.executeI
import edu.colorado.plv.bounder.lifestate.SDialog.dismissSignature
import edu.colorado.plv.bounder.lifestate.SpecSignatures.{Activity_onPause_entry, Activity_onPause_exit, Activity_onResume_entry, Button_init}
import edu.colorado.plv.bounder.lifestate.ViewSpec.{buttonEnabled, onClickI, setEnabled, setOnClickListenerI, setOnClickListenerINull}
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LSPredAnyOrder, LifecycleSpec, SAsyncTask, SDialog, SpecSignatures, SpecSpace, ViewSpec}
import edu.colorado.plv.bounder.solver.Z3StateSolver
import edu.colorado.plv.bounder.symbolicexecutor.ExperimentSpecs.row1Specs
import edu.colorado.plv.bounder.symbolicexecutor.{ExecutorConfig, LimitMaterializationApproxMode, PreciseApproxMode, QueryFinished}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoolVal, CallinReturnNonNull, DisallowedCallin, InitialQuery, MemoryOutputMode, NamedPureVar, NullVal, PrettyPrinting, Reachable, ReceiverNonNull, TopVal}
import edu.colorado.plv.bounder.synthesis.EnumModelGeneratorTest.{allReach, buttonEqReach, nullReach, onClickAfterOnCreateAndOnClick, onClickCanHappenTwice, onClickReachableNoSetEnable, onResumeFirstReach, queryOnActivityCreatedBeforeCall, queryOnClickAfterOnCreate, queryOnClickAfterOnResume, resumeFirstQ, resumeReachAfterPauseQ, resumeTwiceReachQ, row1, row1ActCreatedFirst, row1BugReach, row2, row4, row5, srcReach, srcReachFrag}
import edu.colorado.plv.bounder.synthesis.SynthTestUtil.{cha, targetIze, toConcGraph, witTreeFromMsgList}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite

object EnumModelGeneratorTest{
  /*
  Need to be careful about the contribution we claim.
  If we say this cuts down the search space, synthetic apps undercuts the argument that this works.
  First priority is still micro benchmarks
  Target: one "real" benchmark - just do as much "hacky" get it to work stuff as possible

  We set up a new problem where you only specify reachable and unreachable locations.
  We only want to synthesize the specs required for some given assertion.
  We develop a technique for this.

  Key technical idea: track the data dependency. = we should formalize this.

  High level idea: we can synthesize specs for reachable and unreachable.
  In comparison to related work: not just frequency patterns driving this, its the behavior of the analysis on the code.
  Can we synthesize something that is sound with respect to input.
   */
  val row1 = (destroyLine: String) =>
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
       |public class PlayerFragment extends Fragment {
       |    Subscription sub;
       |    //Callback with irrelevant subscribe
       |    @Override
       |    public View onCreateView(LayoutInflater inflater, ViewGroup container,
       |                             Bundle savedInstanceState) {
       |      return inflater.inflate(0, container, false);
       |    }
       |    @Override
       |    public void onCreate(Bundle savedInstanceState){
       |      super.onCreate(savedInstanceState);
       |    }
       |
       |    @Override
       |    public void onActivityCreated(Bundle savedInstanceState){
       |        super.onActivityCreated(savedInstanceState);
       |        sub = Single.create(subscriber -> {
       |            subscriber.onSuccess(3);
       |        }).subscribeOn(Schedulers.newThread())
       |        .observeOn(AndroidSchedulers.mainThread())
       |        .subscribe(new Action1<Object>(){
       |           @Override
       |           public void call(Object o){
       |             Activity act = getActivity(); //query1 : act != null
       |             act.toString();
       |           }
       |       });
       |    }
       |
       |    @Override
       |    public void onDestroy(){
       |        $destroyLine
       |    }
       |}
       |""".stripMargin

  val row2 = (cancelLine:String) =>
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
       |public class RemoverActivity extends Activity{
       |    FeedRemover remover = null;
       |    View button = null;
       |    @Override
       |    public void onCreate(Bundle b){
       |        remover = new FeedRemover();
       |        button = findViewById(3);
       |        button.setOnClickListener(new OnClickListener(){
       |            @Override
       |            public void onClick(View v){
       |                remover.execute();
       |                $cancelLine
       |            }
       |        });
       |    }
       |
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
  val row5 =
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
       |			  if(resumed){
       |				  progress.dismiss(); //query1
       |        }
       |		  }
       |	  }
       |}
       |""".stripMargin

  val row4 = (disableClick: String) =>
    s"""package com.example.createdestroy;
       |import android.app.Activity;
       |import android.os.Bundle;
       |import android.util.Log;
       |import android.view.View;
       |import android.widget.Button;
       |import android.os.Handler;
       |import android.view.View.OnClickListener;
       |
       |
       |public class MyActivity extends Activity {
       |    String s = null;
       |    View v = null; //TODO: move new button here and say similar to findview
       |    @Override
       |    protected void onResume(){
       |        s = "";
       |        //v = findViewById(3);
       |        v = new Button(this);
       |        v.setOnClickListener(new OnClickListener(){
       |           @Override
       |           public void onClick(View v){
       |             s.toString(); // query1 null unreachable
       |             MyActivity.this.finish();
       |           }
       |        });
       |    }
       |
       |    @Override
       |    protected void onPause() {
       |        s = null;
       |        ${disableClick}
       |        //v.setOnClickListener(null);
       |    }
       |}""".stripMargin


  val row6 =
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
       |import io.reactivex.disposables.Disposable;
       |import io.reactivex.schedulers.Schedulers;
       |import io.reactivex.android.schedulers.AndroidSchedulers;
       |import io.reactivex.Maybe;
       |
       |
       |public class ChaptersFragment extends Fragment {
       |  private Object controller;
       |  private Disposable disposable;
       |  @Override
       |  public void onStart() {
       |    super.onStart();
       |    if(disposable != null){
       |      disposable.dispose();
       |    }
       |
       |    controller = new Object();
       |
       |    disposable = Maybe.create(emitter -> {
       |      emitter.onSuccess(controller.toString()); //query1
       |    })
       |    .subscribeOn(Schedulers.io())
       |    .observeOn(AndroidSchedulers.mainThread())
       |    .subscribe(media -> Log.i("",""),
       |          error -> Log.e("",""));
       |  }
       |  public void onStop() {
       |    disposable.dispose();
       |    controller = null;
       |  }
       |}
       |""".stripMargin
  val srcReachFrag =
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
       |public class PlayerFragmentReach extends Fragment {
       |    Subscription sub;
       |    Object createOrDestroyHappened=null;
       |    Object onActivityCreatedHappened=null;
       |    //Callback with irrelevant subscribe
       |    @Override
       |    public View onCreateView(LayoutInflater inflater, ViewGroup container,
       |                             Bundle savedInstanceState) {
       |      return inflater.inflate(0, container, false);
       |    }
       |    @Override
       |    public void onCreate(Bundle savedInstanceState){
       |      super.onCreate(savedInstanceState);
       |    }
       |
       |    @Override
       |    public void onActivityCreated(Bundle savedInstanceState){
       |        onActivityCreatedHappened=new Object();
       |        if(createOrDestroyHappened == null){
       |            "".toString(); //queryActCreatedFirst
       |        }
       |        createOrDestroyHappened = new Object();
       |        super.onActivityCreated(savedInstanceState);
       |        sub = Single.create(subscriber -> {
       |            subscriber.onSuccess(3);
       |        }).subscribeOn(Schedulers.newThread())
       |        .observeOn(AndroidSchedulers.mainThread())
       |        .subscribe(new Action1<Object>(){
       |            @Override
       |            public void call(Object o){
       |              if(onActivityCreatedHappened!=null){
       |                "".toString(); //queryOnActivityCreatedBeforeCall
       |              }
       |              Activity act = getActivity(); //queryReachFrag : act != null
       |              act.toString();
       |            }
       |        });
       |    }
       |
       |    @Override
       |    public void onDestroy(){
       |        createOrDestroyHappened = new Object();
       |    }
       |}
       |""".stripMargin



  val queryOnActivityCreatedBeforeCall_line = BounderUtil.lineForRegex(".*queryOnActivityCreatedBeforeCall.*".r, srcReachFrag)
  val queryOnActivityCreatedBeforeCall = Reachable(Signature("com.example.createdestroy.PlayerFragmentReach$1",
    "void call(java.lang.Object)"),queryOnActivityCreatedBeforeCall_line)

  val row1ActCreatedFirst_line = BounderUtil.lineForRegex(".*queryActCreatedFirst.*".r, srcReachFrag)
  val row1ActCreatedFirst = Reachable(Signature("com.example.createdestroy.PlayerFragmentReach",
    "void onActivityCreated(android.os.Bundle)"), row1ActCreatedFirst_line)

  val row1BugReach_line = BounderUtil.lineForRegex(".*queryReachFrag.*".r, srcReachFrag)
  val row1BugReach = CallinReturnNonNull(
    Signature("com.example.createdestroy.PlayerFragment$1",
      "void call(java.lang.Object)"), row1BugReach_line ,
    ".*getActivity.*")
  val srcReach =
    s"""package com.example.createdestroy;
       |import android.app.Activity;
       |import android.os.Bundle;
       |import android.util.Log;
       |import android.view.View;
       |import android.widget.Button;
       |import android.os.Handler;
       |import android.view.View.OnClickListener;
       |
       |
       |public class OtherActivity extends Activity implements OnClickListener {
       |    String s = "";
       |    View button = null;
       |    Object createResumedHappened = null;
       |    Object pausedHappened = null;
       |    Object resumeHappened = null;
       |    Object onCreateHappened = null;
       |    Object onClickHappened = null;
       |    @Override
       |    protected void onCreate(Bundle b){
       |        onCreateHappened = new Object();
       |        button = new Button(this);
       |        button.setOnClickListener(this);
       |        button.setEnabled(false);
       |        button.setEnabled(true);
       |
       |        Button button2 = new Button(this);
       |        button2.setOnClickListener(new OnClickListener(){
       |          @Override
       |          public void onClick(View v){
       |             "".toString(); // onClickReachableNoSetEnable
       |          }
       |        });
       |
       |    }
       |    @Override
       |    protected void onResume(){
       |      if(createResumedHappened == null){
       |         "".toString(); //query4 reachable
       |      }
       |      if(pausedHappened != null){
       |        "".toString(); //query5 reachable
       |      }
       |      if(resumeHappened != null){
       |        "".toString(); // query6 reachable
       |      }
       |      if(pausedHappened == null){
       |       "".toString(); //query7 reachable
       |      }
       |      createResumedHappened = new Object();
       |      resumeHappened = new Object();
       |    }
       |    @Override
       |    public void onClick(View v){
       |      if(onCreateHappened != null && onClickHappened != null) {
       |        "".toString(); // onClickAfterOnCreateAndOnClick
       |      }
       |      if(onCreateHappened != null){
       |        "".toString(); // queryOnClickAfterOnCreate
       |      }
       |      if(resumeHappened != null){
       |        "".toString(); // queryOnClickAfterOnResume
       |      }
       |      s.toString(); // query2 reachable
       |      OtherActivity.this.finish();
       |      if(v == button){
       |        s.toString(); //query3 reachable
       |      }
       |      if(onClickHappened != null){
       |       "".toString(); // onClickCanHappenTwice
       |      }
       |      onClickHappened = new Object();
       |    }
       |
       |    @Override
       |    protected void onPause() {
       |        s = null;
       |        createResumedHappened = new Object();
       |        pausedHappened = new Object();
       |    }
       |}""".stripMargin

  val onClickReach = Signature("com.example.createdestroy.OtherActivity",
    "void onClick(android.view.View)")
  val line_reach = BounderUtil.lineForRegex(".*query2.*".r, srcReach)
  val nullReach = ReceiverNonNull(onClickReach, line_reach, Some(".*toString.*"))

  val onClickReachableNoSetEnable_line = BounderUtil.lineForRegex(".*onClickReachableNoSetEnable.*".r, srcReach)
  val onClickReachableNoSetEnable = Reachable(onClickReach.copy(base = onClickReach.base +"$1"),
    onClickReachableNoSetEnable_line)

  val onClickCanHappenTwice_line = BounderUtil.lineForRegex(".*onClickCanHappenTwice.*".r, srcReach)
  val onClickCanHappenTwice = Reachable(onClickReach, onClickCanHappenTwice_line)

  val queryOnClickAfterOnCreate_line = BounderUtil.lineForRegex(".*queryOnClickAfterOnCreate.*".r, srcReach)
  val queryOnClickAfterOnCreate = Reachable(onClickReach, queryOnClickAfterOnCreate_line)

  val onClickAfterOnCreateAndOnClick_line = BounderUtil.lineForRegex(".*queryOnClickAfterOnCreate.*".r, srcReach)
  val onClickAfterOnCreateAndOnClick = Reachable(onClickReach, onClickAfterOnCreateAndOnClick_line)

  val queryOnClickAfterOnResume_line = BounderUtil.lineForRegex(".*queryOnClickAfterOnResume.*".r, srcReach)
  val queryOnClickAfterOnResume = Reachable(onClickReach, queryOnClickAfterOnResume_line)

  val button_eq_reach = BounderUtil.lineForRegex(".*query3.*".r, srcReach)
  val buttonEqReach = Reachable(onClickReach, button_eq_reach)

  val onRes = onClickReach.copy(methodSignature = "void onResume()")
  val onResumeFirst_reach = BounderUtil.lineForRegex(".*query4.*".r, srcReach)
  val onResumeFirstReach =
    Reachable(onRes, onResumeFirst_reach)

  val resumeReachAfterPause = BounderUtil.lineForRegex(".*query5.*".r, srcReach)
  val resumeReachAfterPauseQ =
    Reachable(onRes, resumeReachAfterPause)


  val resumeTwiceReach = BounderUtil.lineForRegex(".*query6.*".r, srcReach)
  val resumeTwiceReachQ =
    Reachable(onRes, resumeTwiceReach)

  val resumeFirst = BounderUtil.lineForRegex(".*query7.*".r, srcReach)
  val resumeFirstQ = Reachable(onRes, resumeFirst)

  val allReach = Set[InitialQuery](
    buttonEqReach,
    nullReach,
    onResumeFirstReach,
    queryOnActivityCreatedBeforeCall,
    queryOnClickAfterOnCreate,
    resumeFirstQ,
    resumeReachAfterPauseQ,
    resumeTwiceReachQ,
    row1ActCreatedFirst,
    onClickCanHappenTwice,
    onClickAfterOnCreateAndOnClick
  )
}
class EnumModelGeneratorTest extends AnyFunSuite {
  val DUMP_DBG = true //Uncomment to skip writing out paths from historia

  val a = NamedPureVar("a")
  val f = NamedPureVar("f")
  val l = NamedPureVar("l")
  val s = NamedPureVar("s")
  val t = NamedPureVar("t")
  val v = NamedPureVar("v")
  val a_onCreate = SpecSignatures.Activity_onCreate_entry
  val a_onDestroy = SpecSignatures.Activity_onDestroy_exit
  val s_a_subscribe = SpecSignatures.RxJava_subscribe_exit.copy(lsVars = s::TopVal::a::Nil)
  val s_unsubscribe = SpecSignatures.RxJava_unsubscribe_exit
  val t_create = SpecSignatures.RxJava_create_exit
  val a_call = SpecSignatures.RxJava_call_entry.copy(lsVars = TopVal::a::Nil)

  ignore("Encode Node Reachability motivating example - ConcGraph"){
    implicit val ord = new DummyOrd
    //TODO: may need to declare vars distinct
    val unreachSeq = toConcGraph(
      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, s_unsubscribe, a_call)))
    val reachSeq = toConcGraph(
      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, a_call)))
    val gen = new EnumModelGenerator(???,???,???,???)
    val spec = new SpecSpace(Set(
      LSSpec(a::Nil,Nil,  LSAnyPred , a_call)
    ), matcherSpace = Set())
//    implicit val solver = new Z3StateSolver(cha)
//    val res = gen.learnRulesFromConcGraph(Set(unreachSeq), Set(reachSeq), spec)
    ???



  }
  ignore("Encode Node Reachability motivating example - witTree"){
    implicit val ord = new DummyOrd
    implicit val outputMode = MemoryOutputMode
    //TODO: may need to declare vars distinct
    val unreachSeq = SynthTestUtil.witTreeFromMsgList(
      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, s_unsubscribe, a_call)))
    val reachSeq = witTreeFromMsgList(
      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, a_call)))
    val gen = new EnumModelGenerator(???,???,???,???)
    val spec = new SpecSpace(Set(
      LSSpec(a::Nil,Nil,  LSAnyPred , a_call)
    ), matcherSpace = Set())
    val res = gen.learnRulesFromExamples(unreachSeq, reachSeq, spec)
    ???



  }
  ignore("Specification enumeration"){
    val hi:LSSpec = LSSpec(l::v:: Nil, Nil, LSAnyPred, onClickI)
    val startingSpec = Set(hi)
    val iSet = Set(onClickI, setOnClickListenerI, setOnClickListenerINull,
      Activity_onResume_entry, Activity_onPause_exit)

    val specSpace = new SpecSpace(startingSpec, matcherSpace = iSet)
    val test: String => Unit = apk => {
      val w = new SootWrapper(apk, toOverride = startingSpec ++ iSet)

      implicit val dbMode = MemoryOutputMode
      val config = ExecutorConfig(
        stepLimit = 2000, w, specSpace,
        component = Some(List("com.example.createdestroy.(MyActivity|OtherActivity)")),
        outputMode = dbMode, timeLimit = 30)

      val line = BounderUtil.lineForRegex(".*query1.*".r, row4("v.setOnClickListener(null);"))
      val clickSignature = Signature("com.example.createdestroy.MyActivity$1",
        "void onClick(android.view.View)")
      val nullUnreach = ReceiverNonNull(clickSignature, line, Some(".*toString.*"))

      //val firstClickCbReach = Reachable(clickSignature, line)


      val onClickReach = Signature("com.example.createdestroy.OtherActivity",
        "void onClick(android.view.View)")
      val line_reach = BounderUtil.lineForRegex(".*query2.*".r, srcReach)
      val nullReach = ReceiverNonNull(onClickReach, line_reach, Some(".*toString.*"))

      val button_eq_reach = BounderUtil.lineForRegex(".*query3.*".r, srcReach)
      val buttonEqReach = Reachable(onClickReach, button_eq_reach)

      val onResumeFirst_reach = BounderUtil.lineForRegex(".*query4.*".r, srcReach)
      val onResumeFirstReach =
        Reachable(onClickReach.copy(methodSignature = "void onResume()"), onResumeFirst_reach)

      val gen = new EnumModelGenerator(nullUnreach, Set(nullReach, buttonEqReach, onResumeFirstReach /*firstClickCbReach*/), specSpace, config)
      var i = 0
      var c = List(hi)
      while(i < 10){
        c = gen.stepSpec(c.head, Map())._1
        println(c)
        //TODO:
      }
    }
    makeApkWithSources(Map("MyActivity.java" -> row4("v.setOnClickListener(null);"),
      "OtherActivity.java" -> srcReach), MkApk.RXBase,
      test)


  }

  test("Synthesis Row 1: Antennapod getActivity returns null") {

    val row1Src = row1("sub.unsubscribe();")
    val startingSpec = Set[LSSpec](
      LSSpec(l::Nil, Nil, LSAnyPred, SpecSignatures.RxJava_call_entry),
//      LifecycleSpec.Fragment_activityCreatedOnlyFirst,
      LSSpec(f :: Nil, Nil,
        LSAnyPred,
        SpecSignatures.Fragment_onActivityCreated_entry),
      FragmentGetActivityNullSpec.getActivityNull
    )

    val test: String => Unit = apk => {
      File.usingTemporaryDirectory() { tmpDir =>
        assert(apk != null)
        // val dbFile = tmpDir / "paths.db"
        // println(dbFile)
        // implicit val dbMode = DBOutputMode(dbFile.toString, truncate = false)
        // dbMode.startMeta()
        implicit val dbMode = MemoryOutputMode

        val iSet = Set(
          SpecSignatures.Fragment_onDestroy_exit,
          SpecSignatures.Fragment_onActivityCreated_entry,
          SpecSignatures.RxJava_call_entry,
          SpecSignatures.RxJava_unsubscribe_exit,
          SpecSignatures.RxJava_subscribe_exit,
        )

        val w = new SootWrapper(apk, toOverride = startingSpec ++ iSet)
        //val dbg = w.dumpDebug("com.example")

        val specSpace = new SpecSpace(startingSpec, matcherSpace = iSet)
        val config = ExecutorConfig(
          stepLimit = 2000, w, specSpace,
          component = Some(List("com.example.createdestroy.*")),
          outputMode = dbMode, timeLimit = 30)

        val line = BounderUtil.lineForRegex(".*query1.*".r, row1Src)


        val query = CallinReturnNonNull(
          Signature("com.example.createdestroy.PlayerFragment$1",
            "void call(java.lang.Object)"), line,
          ".*getActivity.*")

        val queryLocReach = Reachable(query.sig, query.line)


        val reachLoc = Set[InitialQuery](queryLocReach, nullReach, buttonEqReach, onResumeFirstReach,
          resumeReachAfterPauseQ, resumeTwiceReachQ, resumeFirstQ, row1ActCreatedFirst, queryOnActivityCreatedBeforeCall)


        val gen = new EnumModelGenerator(query, reachLoc, specSpace, config)
        val res = gen.run()
        res match {
          case LearnSuccess(space) =>
            println("final specification Row 1")
            println("-------------------")
            val spaceStr = space.toString
            println(spaceStr)
            println("dumping debug info")
            val newConfig = config.copy(specSpace = space)
            val ex = newConfig.getAbstractInterpreter
            val nullReachWit = ex.run(nullReach).flatMap(_.terminals)
            if (DUMP_DBG)
              PrettyPrinting.dumpSpec(space, "cbSpec")
            assert(interpretResult(nullReachWit) == Witnessed)
            if (DUMP_DBG) {
              PrettyPrinting.printWitness(nullReachWit)
              PrettyPrinting.dumpDebugInfo(nullReachWit, "cbNullReachSynth")
            }

            val nullUnreachWit = ex.run(query).flatMap(_.terminals)
            assert(interpretResult(nullUnreachWit) == Proven)
            if (DUMP_DBG)
              PrettyPrinting.dumpDebugInfo(nullUnreachWit, "cbNullUnreachSynth")
          case LearnFailure => throw new IllegalStateException("failed to learn a sufficient spec")
        }
      }
    }
    makeApkWithSources(Map("PlayerFragment.java" -> row1Src, "OtherActivity.java" -> srcReach,
      "PlayerFragmentReach.java" -> srcReachFrag), MkApk.RXBase,
      test)
  }
  test("Synthesis Row 2: Antennapod execute") {

    val row2Src = row2("button.setEnabled(false);")
    val startingSpec = Set[LSSpec](
      ViewSpec.clickWhileNotDisabled.copy(pred = LSAnyPred, existQuant = Nil),
      LifecycleSpec.Activity_createdOnlyFirst //.copy(pred=LSAnyPred) //TODO======
    )

    val test: String => Unit = apk => {
      File.usingTemporaryDirectory() { tmpDir =>
        assert(apk != null)
        // val dbFile = tmpDir / "paths.db"
        // println(dbFile)
        // implicit val dbMode = DBOutputMode(dbFile.toString, truncate = false)
        // dbMode.startMeta()
        implicit val dbMode = MemoryOutputMode

        val iSet = Set(
          setOnClickListenerI,
          AbsMsg(CIExit, setEnabled, TopVal::v::BoolVal(false)::Nil),
          AbsMsg(CIExit, setEnabled, TopVal::v::BoolVal(true)::Nil),
          SpecSignatures.Activity_onCreate_entry,
          executeI
        )

        val w = new SootWrapper(apk, toOverride = startingSpec ++ iSet)
        //val dbg = w.dumpDebug("com.example")

        val specSpace = new SpecSpace(startingSpec, Set(SAsyncTask.disallowDoubleExecute), matcherSpace = iSet)
        val config = ExecutorConfig(
          stepLimit = 2000, w, specSpace,
          component = Some(List("com.example.createdestroy.*")),
          outputMode = dbMode, timeLimit = 30, z3InstanceLimit = 3)

        val query = DisallowedCallin(
          "com.example.createdestroy.RemoverActivity$1",
          "void onClick(android.view.View)",
          SAsyncTask.disallowDoubleExecute)

        //TODO: remove one at a time and figure out smallest set needed for the evaluation
        val gen = new EnumModelGenerator(query, Set(nullReach, buttonEqReach, onResumeFirstReach,
          resumeReachAfterPauseQ, resumeTwiceReachQ, resumeFirstQ, queryOnClickAfterOnCreate,
          onClickCanHappenTwice, onClickReachableNoSetEnable, onClickAfterOnCreateAndOnClick), specSpace, config)

        //Unused: queryOnClickAfterOnCreate
        val res = gen.run()
        res match {
          case LearnSuccess(space) =>
            println("final specification Row 2")
            println("-------------------")
            val spaceStr = space.toString
            println(spaceStr)
            println("dumping debug info")
            val newConfig = config.copy(specSpace = space)
            val ex = newConfig.getAbstractInterpreter
            val nullReachWit = ex.run(nullReach).flatMap(_.terminals)
            if (DUMP_DBG)
              PrettyPrinting.dumpSpec(space, "cbSpec")
            assert(interpretResult(nullReachWit) == Witnessed)
            if (DUMP_DBG) {
              PrettyPrinting.printWitness(nullReachWit)
              PrettyPrinting.dumpDebugInfo(nullReachWit, "cbNullReachSynth")
            }

            val nullUnreachWit = ex.run(query).flatMap(_.terminals)
            assert(interpretResult(nullUnreachWit) == Proven)
            if (DUMP_DBG)
              PrettyPrinting.dumpDebugInfo(nullUnreachWit, "cbNullUnreachSynth")
          case LearnFailure => throw new IllegalStateException("failed to learn a sufficient spec")
        }
      }
    }
    makeApkWithSources(Map("RemoverActivity.java" -> row2Src, "OtherActivity.java" -> srcReach,
      "PlayerFragmentReach.java" -> srcReachFrag), MkApk.RXBase,
      test)
  }

  test("Synthesis Row 5: Antennapod dismiss") {
    val startingSpec = Set[LSSpec](
      SDialog.noDupeShow.copy(pred = LSAnyPred)
    )

    val test: String => Unit = apk => {
      File.usingTemporaryDirectory() { tmpDir =>
        assert(apk != null)
        // val dbFile = tmpDir / "paths.db"
        // println(dbFile)
        // implicit val dbMode = DBOutputMode(dbFile.toString, truncate = false)
        // dbMode.startMeta()
        implicit val dbMode = MemoryOutputMode

        val d = NamedPureVar("d")
        val iSet = Set[OAbsMsg](
          SDialog.showI2,
          AbsMsg(CIEnter, dismissSignature, TopVal::d::Nil),
          SpecSignatures.Activity_onResume_entry,
          SpecSignatures.Activity_onPause_exit
        )

        val w = new SootWrapper(apk, toOverride = startingSpec ++ iSet)
        //val dbg = w.dumpDebug("com.example")

        val specSpace = new SpecSpace(startingSpec, Set(SDialog.disallowDismiss), matcherSpace = iSet)
        val config = ExecutorConfig(
          stepLimit = 2000, w, specSpace,
          component = Some(List("com.example.createdestroy.*")),
          outputMode = dbMode, timeLimit = 60, z3InstanceLimit = 3)


        val query = DisallowedCallin(
          "com.example.createdestroy.StatusActivity$PostTask",
          "void onPostExecute(java.lang.String)",
          SDialog.disallowDismiss)

        // TODO: Set(nullReach, buttonEqReach, onResumeFirstReach,
        //          resumeReachAfterPauseQ, resumeTwiceReachQ, resumeFirstQ, queryOnClickAfterOnCreate,
        //          onClickCanHappenTwice, onClickReachableNoSetEnable, onClickAfterOnCreateAndOnClick)
        //TODO: remove one at a time and figure out smallest set needed for the evaluation
        val gen = new EnumModelGenerator(query, Set.empty, specSpace, config)

        //Unused: queryOnClickAfterOnCreate
        val res = gen.run()
        res match {
          case LearnSuccess(space) =>
            println("final specification Row 2")
            println("-------------------")
            val spaceStr = space.toString
            println(spaceStr)
            println("dumping debug info")
            val newConfig = config.copy(specSpace = space)
            val ex = newConfig.getAbstractInterpreter
            val nullReachWit = ex.run(nullReach).flatMap(_.terminals)
            if (DUMP_DBG)
              PrettyPrinting.dumpSpec(space, "cbSpec")
            assert(interpretResult(nullReachWit) == Witnessed)
            if (DUMP_DBG) {
              PrettyPrinting.printWitness(nullReachWit)
              PrettyPrinting.dumpDebugInfo(nullReachWit, "cbNullReachSynth")
            }

            val nullUnreachWit = ex.run(query).flatMap(_.terminals)
            assert(interpretResult(nullUnreachWit) == Proven)
            if (DUMP_DBG)
              PrettyPrinting.dumpDebugInfo(nullUnreachWit, "cbNullUnreachSynth")
          case LearnFailure => throw new IllegalStateException("failed to learn a sufficient spec")
        }
      }
    }
    makeApkWithSources(Map("StatusActivity.java" -> row5, "OtherActivity.java" -> srcReach,
      "PlayerFragmentReach.java" -> srcReachFrag), MkApk.RXBase,
      test)
  }
  //TODO: other rows from small exp historia
  test("Synthesis Row 4: simplification of Connect bot click/finish") {

    //Or(NS(SpecSignatures.Activity_onPause_exit, SpecSignatures.Activity_onResume_entry),
    //          Not(SpecSignatures.Activity_onResume_entry))
    //TODO: try replacing v in template for _
    val startingSpec = Set[LSSpec](
      LSSpec(a :: Nil, Nil, LSAnyPred, SpecSignatures.Activity_onResume_entry),
      LSSpec(l::v:: Nil, Nil, LSAnyPred, onClickI)
    )

    val test: String => Unit = apk => {
      File.usingTemporaryDirectory() { tmpDir =>
        assert(apk != null)
        // val dbFile = tmpDir / "paths.db"
        // println(dbFile)
        // implicit val dbMode = DBOutputMode(dbFile.toString, truncate = false)
        // dbMode.startMeta()
        implicit val dbMode = MemoryOutputMode

        val iSet = Set(onClickI, setOnClickListenerI, setOnClickListenerINull,
          Activity_onResume_entry, Activity_onPause_exit)

        val w = new SootWrapper(apk, toOverride = startingSpec ++ iSet)
        //val dbg = w.dumpDebug("com.example")

        val specSpace = new SpecSpace(startingSpec, matcherSpace = iSet)
        val config = ExecutorConfig(
          stepLimit = 2000, w, specSpace,
          component = Some(List("com.example.createdestroy.(MyActivity|OtherActivity)")),
          outputMode = dbMode, timeLimit = 30)

        val line = BounderUtil.lineForRegex(".*query1.*".r, row4("v.setOnClickListener(null);"))
        val clickSignature = Signature("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)")
        val nullUnreach = ReceiverNonNull(clickSignature, line, Some(".*toString.*"))



        val gen = new EnumModelGenerator(nullUnreach,Set(nullReach, buttonEqReach, onResumeFirstReach,
          resumeReachAfterPauseQ, resumeTwiceReachQ, resumeFirstQ , queryOnClickAfterOnCreate), specSpace, config) //
        val res = gen.run()
        res match {
          case LearnSuccess(space) =>
            println("final specification Row 4")
            println("-------------------")
            val spaceStr = space.toString
            println(spaceStr)
            println("dumping debug info")
            assert(space.getSpecs.forall{spec => //TODO:dbg code ====
              gen.connectedSpec(spec)
            })
            val newConfig = config.copy(specSpace = space)
            val ex = newConfig.getAbstractInterpreter
            val nullReachWit = ex.run(nullReach).flatMap(_.terminals)
            if(DUMP_DBG)
              PrettyPrinting.dumpSpec(space, "cbSpec")
            assert(interpretResult(nullReachWit) == Witnessed)
            if(DUMP_DBG) {
              PrettyPrinting.printWitness(nullReachWit)
              PrettyPrinting.dumpDebugInfo(nullReachWit, "cbNullReachSynth")
            }
            //val firstClickCbReachWit = ex.run(firstClickCbReach).flatMap(_.terminals)
            //assert(interpretResult(firstClickCbReachWit) == Witnessed)
            //if(DUMP_DBG){
            //  PrettyPrinting.dumpDebugInfo(firstClickCbReachWit, "cbFirstClickReach")
            //}
            val nullUnreachWit = ex.run(nullUnreach).flatMap(_.terminals)
            assert(interpretResult(nullUnreachWit) == Proven)
            if(DUMP_DBG)
              PrettyPrinting.dumpDebugInfo(nullUnreachWit, "cbNullUnreachSynth")
          case LearnFailure => throw new IllegalStateException("failed to learn a sufficient spec")
        }
      }
    }
    makeApkWithSources(Map("MyActivity.java" -> row4("v.setOnClickListener(null);"), "OtherActivity.java" -> srcReach), MkApk.RXBase,
      test)
  }


}
