package edu.colorado.plv.bounder.synthesis

import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{MultiCallback, Proven, Witnessed}
import edu.colorado.plv.bounder.ir.{CBEnter, CallbackMethodInvoke, JimpleFlowdroidWrapper, LocalWrapper, TestIRMethodLoc}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, LSPred, NS, Once, PredicateSpace, SetSignatureMatcher, SignatureMatcher}
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LifecycleSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.{QueryFinished, SparkCallGraph, SymbolicExecutorConfig, TransferFunctions}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, CallStackFrame, CallinReturnNonNull, DBOutputMode, IPathNode, NamedPureVar, PrettyPrinting, PureVar, Qry, StackVar, State, StateFormula}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

class Z3ModelGeneratorTest extends AnyFunSuite {

  implicit def set2SigMat(s:Set[(String,String)]):SignatureMatcher = SetSignatureMatcher(s)
  val fooMethod = TestIRMethodLoc("","foo", List(Some(LocalWrapper("@this","Object"))))
  private val prettyPrinting = new PrettyPrinting()
  val cgMode = SparkCallGraph
  test("generate paths for test"){
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
           |public class ExternalPlayerFragment extends Fragment implements Action1<Object>{
           |    Subscription sub;
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
      val src2 =
        """
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
          |public class  ItemDescriptionFragment extends Fragment {
          |    Subscription otherSub;
          |    @Override
          |    public void onViewCreated(View view, Bundle savedInstanceState) {
          |        otherSub = Single.create(subscriber -> {
          |            subscriber.onSuccess(4);
          |        }).subscribe(r -> {
          |            r.toString();
          |        });
          |    }
          |    @Override
          |    public void onDestroy(){
          |        otherSub.unsubscribe();
          |    }
          |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          LifecycleSpec.Fragment_activityCreatedOnlyFirst,
        ) ++ RxJavaSpec.spec
        val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
        val specSpace = new SpecSpace(specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          specSpace, cha)
        File.usingTemporaryDirectory() { tmpDir =>
          assert(!(tmpDir / "paths.db").exists)
          implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString)
          dbMode.startMeta()
          val config = SymbolicExecutorConfig(
            stepLimit = 200, w, specSpace,
            component = Some(Seq("com.example.createdestroy.ItemDescriptionFragment",
              "com.example.createdestroy.ExternalPlayerFragment")),
            outputMode = dbMode)
          //          implicit val om = config.outputMode
          val symbolicExecutor = config.getSymbolicExecutor
          val line = BounderUtil.lineForRegex(".*query1.*".r, src)
          val query = CallinReturnNonNull(
            "com.example.createdestroy.ExternalPlayerFragment",
            "void call(java.lang.Object)", line,
            ".*getActivity.*")


          val result = symbolicExecutor.run(query, dbMode)
          val fname = s"IrrelevantUnsub_$fileSuffix"
          //          prettyPrinting.dumpDebugInfo(result.flatMap(a => a.terminals), fname)
          //          prettyPrinting.dotWitTree(result.flatMap(_.terminals),s"$fname.dot",includeSubsEdges = true, skipCmd = true)
          assert(result.nonEmpty)
          BounderUtil.throwIfStackTrace(result.flatMap(a => a.terminals))
          val interpretedResult = BounderUtil.interpretResult(result.flatMap(a => a.terminals), QueryFinished)
          //assert(interpretedResult == expectedResult)
          //assert(BounderUtil.characterizeMaxPath(result.flatMap(a => a.terminals)) == MultiCallback)
        }
      }

      makeApkWithSources(Map("ExternalPlayerFragment.java" -> src,
        "ItemDescriptionFragment.java" -> src2), MkApk.RXBase, test)
    }
  }
  test("Encode Node Reachability"){
    // TODO: implement model generator
    val a = NamedPureVar("a")
    val gen = new Z3ModelGenerator(???)
    val dummyLoc = CallbackMethodInvoke(tgtClazz = "",
      fmwName="void foo()", fooMethod)
    val pureVar = PureVar(1)
    val frame = CallStackFrame(dummyLoc, None, Map(StackVar("this") -> pureVar))
    val state = State(StateFormula(List(frame), Map(), Set(),Map(),AbstractTrace(Nil)),0)
    val qryR1 = Qry(state, dummyLoc, ???)

    val barPred = Once(CBEnter,Set(("","void bar()")), List(a))
    val fooPred = Once(CBEnter,Set(("","void foo()")), List(a))
    val pred = barPred

    val theta = Map(
      "a" -> pureVar
    )
    val predSpace = new PredicateSpace(Set(fooPred, barPred))
    ???

  }
}
