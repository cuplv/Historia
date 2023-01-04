package edu.colorado.plv.bounder.synthesis

import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{MultiCallback, Proven, Witnessed}
import edu.colorado.plv.bounder.ir.{AppLoc, CBEnter, CallbackMethodInvoke, CallbackMethodReturn, JimpleFlowdroidWrapper, LocalWrapper, SerializedIRMethodLoc}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, Exists, LSPred, LSSingle, LSSpec, NS, AbsMsg, PredicateSpace, SetSignatureMatcher, SignatureMatcher}
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LifeState, LifecycleSpec, RxJavaSpec, SpecSignatures, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.{QueryFinished, SparkCallGraph, ExecutorConfig, TransferFunctions}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, CallStackFrame, CallinReturnNonNull, DBOutputMode, IPathNode, MemoryOutputMode, NamedPureVar, OrdCount, OutputMode, PathNode, PrettyPrinting, PureExpr, PureVal, PureVar, Qry, StackVar, State, StateFormula, TopVal, Unknown}
import edu.colorado.plv.bounder.synthesis.SynthTestUtil.{cha, hierarchy, intToClass, targetIze, top, witTreeFromMsgList}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod
//import edu.colorado.plv.bounder.symbolicexecutor.SymbolicExecutor.LexicalStackThenTopo

//class Z3ModelGeneratorTest extends AnyFunSuite {
//
//  implicit def listToAbsTr(l:List[LSSingle]):AbstractTrace = AbstractTrace(l)
//  implicit def set2SigMat(s:Set[(String,String)]):SignatureMatcher = SetSignatureMatcher(s)
//  val fooMethod = SerializedIRMethodLoc("","foo", List(Some(LocalWrapper("@this","Object"))))
//  private val prettyPrinting = new PrettyPrinting()
//  val cgMode = SparkCallGraph
//  ignore("Synthesize model based on bug and fix pair"){
//    //TODO
//    List(
//      ("sub.unsubscribe();", Proven, "withUnsub"),
//      ("", Witnessed, "noUnsub")
//    ).map { case (destroyLine, expectedResult,fileSuffix) =>
//      val src =
//        s"""
//           |package com.example.createdestroy;
//           |import android.app.Activity;
//           |import android.content.Context;
//           |import android.net.Uri;
//           |import android.os.Bundle;
//           |
//           |import androidx.fragment.app.Fragment;
//           |
//           |import android.util.Log;
//           |import android.view.LayoutInflater;
//           |import android.view.View;
//           |import android.view.ViewGroup;
//           |
//           |import rx.Single;
//           |import rx.Subscription;
//           |import rx.android.schedulers.AndroidSchedulers;
//           |import rx.schedulers.Schedulers;
//           |import rx.functions.Action1;
//           |
//           |
//           |public class ExternalPlayerFragment extends Fragment implements Action1<Object>{
//           |    Subscription sub;
//           |    @Override
//           |    public void onActivityCreated(Bundle savedInstanceState){
//           |        sub = Single.create(subscriber -> {
//           |            subscriber.onSuccess(3);
//           |        }).subscribe(this);
//           |    }
//           |
//           |    @Override
//           |    public void call(Object o){
//           |         Activity act = getActivity(); //query1 : act != null
//           |         act.toString();
//           |    }
//           |
//           |    @Override
//           |    public void onDestroy(){
//           |        $destroyLine
//           |    }
//           |}
//           |""".stripMargin
//      val src2 =
//        """
//          |package com.example.createdestroy;
//          |import android.app.Activity;
//          |import android.content.Context;
//          |import android.net.Uri;
//          |import android.os.Bundle;
//          |
//          |import androidx.fragment.app.Fragment;
//          |
//          |import android.util.Log;
//          |import android.view.LayoutInflater;
//          |import android.view.View;
//          |import android.view.ViewGroup;
//          |
//          |import rx.Single;
//          |import rx.Subscription;
//          |import rx.android.schedulers.AndroidSchedulers;
//          |import rx.schedulers.Schedulers;
//          |import rx.functions.Action1;
//          |
//          |public class  ItemDescriptionFragment extends Fragment {
//          |    Subscription otherSub;
//          |    @Override
//          |    public void onViewCreated(View view, Bundle savedInstanceState) {
//          |        otherSub = Single.create(subscriber -> {
//          |            subscriber.onSuccess(4);
//          |        }).subscribe(r -> {
//          |            r.toString();
//          |        });
//          |    }
//          |    @Override
//          |    public void onDestroy(){
//          |        otherSub.unsubscribe();
//          |    }
//          |}""".stripMargin
//
//      val test: String => Unit = apk => {
//        assert(apk != null)
//        val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
//          FragmentGetActivityNullSpec.getActivityNonNull,
//          LifecycleSpec.Fragment_activityCreatedOnlyFirst,
//        ) ++ RxJavaSpec.spec
//        val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
//        val specSpace = new SpecSpace(specs)
//        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
//          specSpace, cha)
//        File.usingTemporaryDirectory() { tmpDir =>
//          assert(!(tmpDir / "paths.db").exists)
//          implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString)
//          dbMode.startMeta()
//          val config = SymbolicExecutorConfig(
//            stepLimit = 200, w, specSpace,
//            component = Some(Seq("com.example.createdestroy.ItemDescriptionFragment",
//              "com.example.createdestroy.ExternalPlayerFragment")),
//            outputMode = dbMode)
//          //          implicit val om = config.outputMode
//          val symbolicExecutor = config.getSymbolicExecutor
//          val line = BounderUtil.lineForRegex(".*query1.*".r, src)
//          val query = CallinReturnNonNull(
//            "com.example.createdestroy.ExternalPlayerFragment",
//            "void call(java.lang.Object)", line,
//            ".*getActivity.*")
//
//
//          val result = symbolicExecutor.run(query, dbMode)
//          val fname = s"IrrelevantUnsub_$fileSuffix"
//          //          prettyPrinting.dumpDebugInfo(result.flatMap(a => a.terminals), fname)
//          //          prettyPrinting.dotWitTree(result.flatMap(_.terminals),s"$fname.dot",includeSubsEdges = true, skipCmd = true)
//          assert(result.nonEmpty)
//          BounderUtil.throwIfStackTrace(result.flatMap(a => a.terminals))
//          val interpretedResult = BounderUtil.interpretResult(result.flatMap(a => a.terminals), QueryFinished)
//          //assert(interpretedResult == expectedResult)
//          //assert(BounderUtil.characterizeMaxPath(result.flatMap(a => a.terminals)) == MultiCallback)
//        }
//      }
//
//      makeApkWithSources(Map("ExternalPlayerFragment.java" -> src,
//        "ItemDescriptionFragment.java" -> src2), MkApk.RXBase, test)
//    }
//  }
//
//  val a = NamedPureVar("a")
//  val f = NamedPureVar("f")
//  val l = NamedPureVar("l")
//  val s = NamedPureVar("s")
//  val t = NamedPureVar("t")
//  val v = NamedPureVar("v")
//  val a_onCreate = SpecSignatures.Activity_onCreate_entry
//  val a_onDestroy = SpecSignatures.Activity_onDestroy_exit
//  val s_a_subscribe = SpecSignatures.RxJava_subscribe_exit.copy(lsVars = s::TopVal::a::Nil)
//  val s_unsubscribe = SpecSignatures.RxJava_unsubscribe_exit
//  val t_create = SpecSignatures.RxJava_create_exit
//  val a_call = SpecSignatures.RxJava_call_entry.copy(lsVars = TopVal::a::Nil)
//
//  implicit val ord = new DummyOrd
//  implicit val outputMode = MemoryOutputMode
//
//  //Depricated (uses old encoding)
//  test("positive bexp excludes init"){
//    //TODO: may want toemove this if we go with aut encode
//    def testWithState(state:State, exclInitExpected:Boolean, containsInitExpected:Boolean) = {
//
//      val cha = new ClassHierarchyConstraints(hierarchy, Set("java.lang.Runnable"), intToClass)
//      val gen = new Z3ModelGenerator(cha)
//      val state = top.copy(sf = top.sf.copy(traceAbstraction = targetIze(List(a_call))))
//      implicit val ctx = gen.getSolverCtx
//      try {
//        ctx.acquire()
//        implicit val space = new SpecSpace(Set(LSSpec(a :: Nil, Nil, a_onCreate, a_call)))
//        implicit val mt = gen.MessageTranslator(Set(state), space)
//
//        val enc = gen.encodeExcludesInit(state)
//        ctx.mkAssert(enc)
//        val res = gen.checkSAT(mt)
//        assert(res == exclInitExpected)
//        ctx.release()
//        ctx.acquire()
//        val enc2 = gen.encodeMayContainInit(state)
//        ctx.mkAssert(enc2)
//        val res2 = gen.checkSAT(mt)
//        assert(res == containsInitExpected)
//      } finally {
//        ctx.release()
//      }
//    }
//
//  }
//  ignore("Simple encode node reachability"){
//
//    //TODO: may need to declare vars distinct
//    val unreachSeq = witTreeFromMsgList(
//      targetIze(List(a_onCreate, a_call)))
//    val reachSeq = witTreeFromMsgList(
//      targetIze(List(a_call)))
//    val gen = new Z3ModelGenerator(cha)
//    val spec = new SpecSpace(Set(
//      LSSpec(a::Nil,Nil,  UComb("call", a_onCreate::Exists(s::l::Nil,NS(s_a_subscribe, s_unsubscribe))::Nil) , a_call)
//    ))
//    val res = gen.learnRulesFromExamples(unreachSeq, reachSeq, spec)
//    ???
//  }
//  ignore("Encode Node Reachability motivating example"){
//    implicit val ord = new DummyOrd
//    implicit val outputMode = MemoryOutputMode
//    //TODO: may need to declare vars distinct
//    val unreachSeq = witTreeFromMsgList(
//      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, s_unsubscribe, a_call)))
//    val reachSeq = witTreeFromMsgList(
//      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, a_call)))
//    val cha = new ClassHierarchyConstraints(hierarchy,Set("java.lang.Runnable"),intToClass)
//    val gen = new Z3ModelGenerator(cha)
//    val spec = new SpecSpace(Set(
//      LSSpec(a::Nil,Nil,  UComb("call", a_onDestroy::Exists(s::l::Nil,NS(s_a_subscribe, s_unsubscribe))::Nil) , a_call)
//    ))
//    val res = gen.learnRulesFromExamples(unreachSeq, reachSeq, spec)
//    ???
//
//
//
//  }
//}
