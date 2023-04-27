package edu.colorado.plv.bounder.synthesis

import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed, interpretResult}
import edu.colorado.plv.bounder.ir.SootWrapper
import edu.colorado.plv.bounder.lifestate.LifeState.{And, LSAnyPred, LSSpec, NS, Not, Or, Signature}
import edu.colorado.plv.bounder.lifestate.SpecSignatures.{Activity_onPause_entry, Activity_onPause_exit, Activity_onResume_entry, Button_init}
import edu.colorado.plv.bounder.lifestate.ViewSpec.{onClickI, setOnClickListenerI, setOnClickListenerINull}
import edu.colorado.plv.bounder.lifestate.{LSPredAnyOrder, SpecSignatures, SpecSpace}
import edu.colorado.plv.bounder.solver.Z3StateSolver
import edu.colorado.plv.bounder.symbolicexecutor.{ExecutorConfig, QueryFinished}
import edu.colorado.plv.bounder.symbolicexecutor.state.{MemoryOutputMode, NamedPureVar, PrettyPrinting, Reachable, ReceiverNonNull, TopVal}
import edu.colorado.plv.bounder.synthesis.SynthTestUtil.{cha, targetIze, toConcGraph, witTreeFromMsgList}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite

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

  test("Specification comparitor should order specifications with holes"){
    val p1 = onClickI
    val p2 = And(LSAnyPred, LSAnyPred)
    assert(LSPredAnyOrder.compare(p1,p2) < 0)
    assert(LSPredAnyOrder.compare(p2,p1) > 0)
    assert(LSPredAnyOrder.compare(p1,p1) == 0)
  }

  val srcUnreach =
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
       |        v.setOnClickListener(null);
       |    }
       |}""".stripMargin
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
       |public class OtherActivity extends Activity implements OnClickListener{
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
  ignore("Specification enumeration"){
    val hi = LSSpec(l::v:: Nil, Nil, LSAnyPred, onClickI)
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

      val line = BounderUtil.lineForRegex(".*query1.*".r, srcUnreach)
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
      while(i < 10){
        //gen.step(hi, )
        //TODO:
      }
    }
    makeApkWithSources(Map("MyActivity.java" -> srcUnreach, "OtherActivity.java" -> srcReach), MkApk.RXBase,
      test)


  }
  test("Synthesis example - simplification of Connect bot click/finish") {
    //TODO==== Non-determinism seems less, but now gives wrong spec, probably need to include traces or something

    //Or(NS(SpecSignatures.Activity_onPause_exit, SpecSignatures.Activity_onResume_entry),
    //          Not(SpecSignatures.Activity_onResume_entry))
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

        val line = BounderUtil.lineForRegex(".*query1.*".r, srcUnreach)
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

        val onRes = onClickReach.copy(methodSignature = "void onResume()")
        val onResumeFirst_reach = BounderUtil.lineForRegex(".*query4.*".r, srcReach)
        val onResumeFirstReach =
          Reachable(onRes, onResumeFirst_reach)

        val resumeReachAfterPause = BounderUtil.lineForRegex(".*query5.*".r, srcReach)
        val resumeReachAfterPauseQ =
          Reachable(onRes, resumeReachAfterPause)


        val resumeTwiceReach= BounderUtil.lineForRegex(".*query6.*".r, srcReach)
        val resumeTwiceReachQ =
            Reachable(onRes, resumeTwiceReach)

        val gen = new EnumModelGenerator(nullUnreach,Set(nullReach, buttonEqReach, onResumeFirstReach,
          resumeReachAfterPauseQ, resumeTwiceReachQ), specSpace, config)
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
    makeApkWithSources(Map("MyActivity.java" -> srcUnreach, "OtherActivity.java" -> srcReach), MkApk.RXBase,
      test)
  }


}
