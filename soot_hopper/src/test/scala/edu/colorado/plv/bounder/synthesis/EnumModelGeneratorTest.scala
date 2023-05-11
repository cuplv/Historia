package edu.colorado.plv.bounder.synthesis

import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed, interpretResult}
import edu.colorado.plv.bounder.ir.{CIExit, SootWrapper}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, LSAnyPred, LSSpec, NS, Not, Or, Signature}
import edu.colorado.plv.bounder.lifestate.SAsyncTask.executeI
import edu.colorado.plv.bounder.lifestate.SpecSignatures.{Activity_onPause_entry, Activity_onPause_exit, Activity_onResume_entry, Button_init}
import edu.colorado.plv.bounder.lifestate.ViewSpec.{buttonEnabled, onClickI, setEnabled, setOnClickListenerI, setOnClickListenerINull}
import edu.colorado.plv.bounder.lifestate.{LSPredAnyOrder, LifecycleSpec, SAsyncTask, SpecSignatures, SpecSpace, ViewSpec}
import edu.colorado.plv.bounder.solver.Z3StateSolver
import edu.colorado.plv.bounder.symbolicexecutor.{ExecutorConfig, QueryFinished}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoolVal, CallinReturnNonNull, DisallowedCallin, MemoryOutputMode, NamedPureVar, NullVal, PrettyPrinting, Reachable, ReceiverNonNull, TopVal}
import edu.colorado.plv.bounder.synthesis.EnumModelGeneratorTest.{buttonEqReach, nullReach, onResumeFirstReach, resumeFirstQ, resumeReachAfterPauseQ, resumeTwiceReachQ, row1, row1BugReach, row2, row4, srcReach, srcReachFrag}
import edu.colorado.plv.bounder.synthesis.SynthTestUtil.{cha, targetIze, toConcGraph, witTreeFromMsgList}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite

object EnumModelGeneratorTest{
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
       |public class PlayerFragment extends Fragment implements Action1<Object>{
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
       |        .subscribe(this);
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
       |    View v = null;
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
       |public class PlayerFragmentReach extends Fragment implements Action1<Object>{
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
       |        .subscribe(this);
       |    }
       |
       |    @Override
       |    public void call(Object o){
       |         Activity act = getActivity(); //queryReachFrag : act != null
       |         act.toString();
       |    }
       |
       |    @Override
       |    public void onDestroy(){
       |    }
       |}
       |""".stripMargin




  val row1BugReach_line = BounderUtil.lineForRegex(".*queryReachFrag.*".r, srcReachFrag)
  val row1BugReach = CallinReturnNonNull(
    Signature("com.example.createdestroy.PlayerFragment",
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
       |    @Override
       |    protected void onCreate(Bundle b){
       |        button = new Button(this);
       |        button.setOnClickListener(this);
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
       |      s.toString(); // query2 reachable
       |      OtherActivity.this.finish();
       |      if(v == button){
       |        s.toString(); //query3 reachable
       |      }
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
    //Or(NS(SpecSignatures.Activity_onPause_exit, SpecSignatures.Activity_onResume_entry),
    //          Not(SpecSignatures.Activity_onResume_entry))
    val startingSpec = Set[LSSpec](
      LSSpec(l::Nil, s::Nil, LSAnyPred, SpecSignatures.RxJava_call_entry),
      LSSpec(f :: Nil, Nil,
        LSAnyPred,
        SpecSignatures.Fragment_onActivityCreated_entry),
      LSSpec(f :: Nil, Nil,
        LSAnyPred, SpecSignatures.Fragment_get_activity_exit.copy(lsVars = NullVal::f::Nil),
        Set.empty)
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
          SpecSignatures.Fragment_get_activity_exit,
          SpecSignatures.RxJava_call_entry,
          SpecSignatures.RxJava_unsubscribe_exit,
          SpecSignatures.RxJava_subscribe_exit,
        )

        val w = new SootWrapper(apk, toOverride = startingSpec ++ iSet)
        //val dbg = w.dumpDebug("com.example")

        val specSpace = new SpecSpace(startingSpec, matcherSpace = iSet)
        val config = ExecutorConfig(
          stepLimit = 2000, w, specSpace,
          component = Some(List("com.example.createdestroy.PlayerFragment")),
          outputMode = dbMode, timeLimit = 30)

        val line = BounderUtil.lineForRegex(".*query1.*".r, row1Src)


        val query = CallinReturnNonNull(
          Signature("com.example.createdestroy.PlayerFragment",
            "void call(java.lang.Object)"), line,
          ".*getActivity.*")


        //TODO:==== add reachable back in one at a time
        //Set

        val gen = new EnumModelGenerator(query, Set(nullReach, buttonEqReach, onResumeFirstReach,
          resumeReachAfterPauseQ, resumeTwiceReachQ, resumeFirstQ), specSpace, config)
        val res = gen.run()
        res match {
          case LearnSuccess(space) =>
            println("final specification")
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
      ViewSpec.clickWhileNotDisabled.copy(pred = LSAnyPred),
      LifecycleSpec.Activity_createdOnlyFirst.copy(pred=LSAnyPred)
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
          component = Some(List("com.example.createdestroy.*RemoverActivity.*")),
          outputMode = dbMode, timeLimit = 30, z3InstanceLimit = 3)

//        val line = BounderUtil.lineForRegex(".*query1.*".r, row2Src)
//
//
//        val query = CallinReturnNonNull(
//          Signature("com.example.createdestroy.PlayerFragment",
//            "void call(java.lang.Object)"), line,
//          ".*getActivity.*")


        //TODO:==== add reachable back in one at a time
        //Set(nullReach, buttonEqReach, onResumeFirstReach,
        //          resumeReachAfterPauseQ, resumeTwiceReachQ, resumeFirstQ)


        val query = DisallowedCallin(
          "com.example.createdestroy.RemoverActivity$1",
          "void onClick(android.view.View)",
          SAsyncTask.disallowDoubleExecute)

        val gen = new EnumModelGenerator(query, Set(nullReach, buttonEqReach, onResumeFirstReach,
          resumeReachAfterPauseQ, resumeTwiceReachQ, resumeFirstQ), specSpace, config)
        val res = gen.run()
        res match {
          case LearnSuccess(space) =>
            println("final specification")
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
          resumeReachAfterPauseQ, resumeTwiceReachQ, resumeFirstQ), specSpace, config)
        val res = gen.run()
        res match {
          case LearnSuccess(space) =>
            println("final specification")
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
