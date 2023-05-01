package edu.colorado.plv.bounder.symbolicexecutor

import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{MultiCallback, Proven, ResultSummary, SingleCallbackMultiMethod, SingleMethod, Timeout, Unreachable, Witnessed, interpretResult}
import edu.colorado.plv.bounder.ir.{CIExit, SootWrapper}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, Exists, LSConstraint, LSSpec, LSTrue, NS, Not, Or, Signature, SubClassMatcher}
import edu.colorado.plv.bounder.lifestate.SpecSignatures.{Activity_onPause_entry, Activity_onResume_entry, Button_init}
import edu.colorado.plv.bounder.lifestate.ViewSpec.{a, b, b2, l, onClick, onClickI, setOnClickListener, setOnClickListenerI, setOnClickListenerINull, v}
import edu.colorado.plv.bounder.lifestate.{Dummy, FragmentGetActivityNullSpec, LifeState, LifecycleSpec, RxJavaSpec, SAsyncTask, SDialog, SpecSignatures, SpecSpace, ViewSpec}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.ExperimentSpecs.row4Specs
import edu.colorado.plv.bounder.symbolicexecutor.state.{AllReceiversNonNull, BottomQry, CallinReturnNonNull, DBOutputMode, DisallowedCallin, FieldPtEdge, IPathNode, MemoryOutputMode, NamedPureVar, NoOutputMode, NotEquals, OutputMode, PrettyPrinting, Qry, Reachable, ReceiverNonNull, TopVal}
import edu.colorado.plv.bounder.synthesis.{EnumModelGenerator, EnumModelGeneratorTest}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.{AnyFunSuite, FixtureAnyFunSuite}
import soot.{Scene, SootMethod}
import upickle.default.write

import scala.jdk.CollectionConverters._

class AbstractInterpreterTest extends FixtureAnyFunSuite  {

  case class FixtureParam(approxMode: ApproxMode,
                          expectUnreachable:ResultSummary => Unit,
                          expectReachable:ResultSummary => Unit)
  override def withFixture(test:OneArgTest) = {
    test(FixtureParam(LimitMaterializationApproxMode(), //TODO: why does dropping heap cells make this slower???
      expectUnreachable = r => assert(r == Proven || r == Unreachable), //Note: no output mode cannot distinguish unreach/proven
      expectReachable = r => assert(r == Witnessed))) //Note: may need to switch witness/timeout
    test(FixtureParam(PreciseApproxMode(true),
      expectUnreachable = r => assert(r == Proven || r == Unreachable),
      expectReachable = r => assert(r == Witnessed))) //Note: may need to switch witness/timeout

  }

  //implicit val om: OutputMode = NoOutputMode
  implicit val om: OutputMode = MemoryOutputMode

  test("Symbolic Executor should prove an intraprocedural deref"){ f =>
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath
    assert(test_interproc_1 != null)
    val specs:Set[LSSpec] = Set()
    val w = new SootWrapper(test_interproc_1,specs)
    val config = ExecutorConfig(
      stepLimit = 8, w, new SpecSpace(specs), printAAProgress = true, approxMode = f.approxMode, outputMode = om)
    val symbolicExecutor = config.getAbstractInterpreter
    val query = ReceiverNonNull(
      Signature("com.example.test_interproc_1.MainActivity", "java.lang.String objectString()"),21,None)
    // Call symbolic executor
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//    prettyPrinting.dumpDebugInfo(result, "test_interproc_1_derefSafe")
    if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) {
      assert(result.size == 1)
      assert(result.iterator.next.qry.searchState == BottomQry)
      assert(BounderUtil.characterizeMaxPath(result)== SingleMethod)
    }
    f.expectUnreachable(BounderUtil.interpretResult(result,QueryFinished))
  }


  test("Symbolic Executor should prove an inter-callback deref"){ f =>
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new SootWrapper(test_interproc_1, LifecycleSpec.spec)

    val config = ExecutorConfig(
      stepLimit = 200, w,new SpecSpace(LifecycleSpec.spec),  z3Timeout = Some(30),
      component = Some(List("com\\.example\\.test_interproc_2\\.MainActivity.*")), approxMode = f.approxMode,
      outputMode = om)
    val symbolicExecutor = config.getAbstractInterpreter
    val query = ReceiverNonNull(
      Signature("com.example.test_interproc_2.MainActivity", "void onPause()"),27,None)
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
    // prettyPrinting.dumpDebugInfo(result, "inter-callback", truncate = false)
    BounderUtil.throwIfStackTrace(result)

    f.expectUnreachable(BounderUtil.interpretResult(result,QueryFinished))
    if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
  }
  test("Symbolic executor should witness onPause"){ f =>
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new SootWrapper(test_interproc_1, LifecycleSpec.spec)
    val config = ExecutorConfig(
      stepLimit = 50, w,new SpecSpace(LifecycleSpec.spec),  z3Timeout = Some(30),
      component = Some(List("com\\.example\\.test_interproc_2\\.MainActivity.*")), approxMode = f.approxMode,
      outputMode = om)
    //      component = Some(List("com\\.example\\.test_interproc_2\\.*"))
    val symbolicExecutor = new AbstractInterpreter[SootMethod, soot.Unit](config)
    val query = Reachable(
      Signature("com.example.test_interproc_2.MainActivity", "void onPause()"),25)
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/witnessOnPause.dot")
//    prettyPrinting.dumpDebugInfo(result, "test_interproc_2_onPauseReach")
    BounderUtil.throwIfStackTrace(result)
    f.expectReachable(BounderUtil.interpretResult(result,QueryFinished))
  }
  test("Symbolic executor should witness onResume"){ f =>
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new SootWrapper(test_interproc_1,  LifecycleSpec.spec)
    val config = ExecutorConfig(
      stepLimit = 50, w,new SpecSpace(LifecycleSpec.spec),  z3Timeout = Some(30), approxMode = f.approxMode,
      outputMode = om)
    val symbolicExecutor = config.getAbstractInterpreter
    val query = Reachable(
      Signature("com.example.test_interproc_2.MainActivity", "void onResume()"),20)
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//    prettyPrinting.dumpDebugInfo(result, "test_interproc_2_onResumeReach")
    BounderUtil.throwIfStackTrace(result)
    f.expectReachable(BounderUtil.interpretResult(result,QueryFinished))
  }
  test("Test clinit") { f =>
    val src =
      """package com.example.createdestroy;
        |import androidx.appcompat.app.AppCompatActivity;
        |import android.os.Bundle;
        |import android.util.Log;
        |import java.io.File;
        |
        |import rx.Single;
        |import rx.Subscription;
        |import rx.android.schedulers.AndroidSchedulers;
        |import rx.schedulers.Schedulers;
        |
        |
        |public class MyActivity extends AppCompatActivity {
        |    Object o = null;
        |    static Object o2 = new Object();
        |
        |    @Override
        |    protected void onCreate(Bundle savedInstanceState) {
        |        if(o2 != null){
        |         Log.i("b", o.toString()); //query1
        |        }
        |    }
        |
        |    @Override
        |    protected void onDestroy() {
        |    }
        |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 50, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode, outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter

      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)"), BounderUtil.lineForRegex(".*query1.*".r, src), Some(".*toString.*"))
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      //PrettyPrinting.dumpDebugInfo(result, "clinit")

      if (om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) {
        assert(result.nonEmpty)
      }
      BounderUtil.throwIfStackTrace(result)
      f.expectReachable(BounderUtil.interpretResult(result, QueryFinished))

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Test array return from callin") { f =>
    val src =
      """package com.example.createdestroy;
        |import androidx.appcompat.app.AppCompatActivity;
        |import android.os.Bundle;
        |import android.util.Log;
        |import java.io.File;
        |
        |import rx.Single;
        |import rx.Subscription;
        |import rx.android.schedulers.AndroidSchedulers;
        |import rx.schedulers.Schedulers;
        |
        |
        |public class MyActivity extends AppCompatActivity {
        |    Object o = new Object();
        |
        |    @Override
        |    protected void onCreate(Bundle savedInstanceState) {
        |        File f = new File("");
        |        File[] files = f.listFiles();
        |        File f2 = files[0];
        |        o = f2.getName();
        |        Log.i("b", o.toString()); //query1
        |    }
        |
        |    @Override
        |    protected void onDestroy() {
        |       Object[] foo = {new Object()};
        |    }
        |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk,  specs)
      val config = ExecutorConfig(
        stepLimit = 50, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode, outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter

      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)"), BounderUtil.lineForRegex(".*query1.*".r,src), Some(".*toString.*"))
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      PrettyPrinting.dumpDebugInfo(result, "ci_ret_array")

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) {
        assert(result.nonEmpty)
      }
      BounderUtil.throwIfStackTrace(result)
      f.expectReachable(BounderUtil.interpretResult(result,QueryFinished))

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Test direct framework field read") { f =>
    val src =
      """package com.example.createdestroy;
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
        |
        |    @Override
        |    protected void onCreate(Bundle savedInstanceState) {
        |        System.out.println("");  // out is a public static field, app only cg should provide something to it.
        |        Log.i("b", o.toString()); //query1
        |    }
        |
        |    @Override
        |    protected void onDestroy() {
        |        o = null;
        |    }
        |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 50, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode, outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter
      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)"), BounderUtil.lineForRegex(".*query1.*".r, src), Some(".*toString.*"))
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      //      prettyPrinting.dumpDebugInfo(result, "readLiteral")

      if (om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) {
        assert(result.nonEmpty)
      }
      BounderUtil.throwIfStackTrace(result)
      f.expectReachable(BounderUtil.interpretResult(result, QueryFinished))

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Test read string literal") { f =>
    val src =
      """package com.example.createdestroy;
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
        |
        |    @Override
        |    protected void onCreate(Bundle savedInstanceState) {
        |        o = "";
        |        Log.i("b", o.toString()); //query1
        |    }
        |
        |    @Override
        |    protected void onDestroy() {
        |        o = null;
        |    }
        |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk,  specs)
      val config = ExecutorConfig(
        stepLimit = 50, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode, outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter
      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)"), BounderUtil.lineForRegex(".*query1.*".r,src), Some(".*toString.*"))
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result, "readLiteral")

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) {
        assert(result.nonEmpty)
      }
      BounderUtil.throwIfStackTrace(result)
      f.expectUnreachable(BounderUtil.interpretResult(result,QueryFinished))

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Test for each loop") { f =>
    // This test is just to check if we terminate properly on a foreach.
    // TODO: we may want to specify the behavior of the list iterator and test it here
    val src =
      """package com.example.createdestroy;
        |import androidx.appcompat.app.AppCompatActivity;
        |import android.os.Bundle;
        |import android.util.Log;
        |import java.util.List;
        |import java.util.ArrayList;
        |
        |import rx.Single;
        |import rx.Subscription;
        |import rx.android.schedulers.AndroidSchedulers;
        |import rx.schedulers.Schedulers;
        |
        |
        |public class MyActivity extends AppCompatActivity {
        |    String o = null;
        |    Boolean o2 = null;
        |    Subscription subscription;
        |
        |    @Override
        |    protected void onResume() {
        |        List<String> l = new ArrayList<String>(); //query0
        |        l.add("hi there");
        |        String s2 = null;
        |        for(String s : l){
        |            s.toString(); //query1
        |        }
        |    }
        |
        |    @Override
        |    protected void onPause() {
        |    }
        |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs:Set[LSSpec] = Set()
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 200, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode, outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter

      // Entry of onCreate should be reachable (debugging spark issue)
      val queryEntry = Reachable(
        Signature("com.example.createdestroy.MyActivity","void onResume()"),
        BounderUtil.lineForRegex(".*query0.*".r,src))
      val resultEntry = symbolicExecutor.run(queryEntry).flatMap(a => a.terminals)

      BounderUtil.throwIfStackTrace(resultEntry)
      f.expectReachable(BounderUtil.interpretResult(resultEntry,QueryFinished) )

      // Dereference in loop should witness since we do not have a spec for the list
      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onResume()"), BounderUtil.lineForRegex(".*query1.*".r,src), Some(".*toString.*"))

      // prettyPrinting.dotMethod( query.head.loc, symbolicExecutor.controlFlowResolver, "onPauseCond.dot")

      val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
      //prettyPrinting.dumpDebugInfo(result, "forEach")

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) {
        assert(result.nonEmpty)
      }
      BounderUtil.throwIfStackTrace(result)
      f.expectReachable(BounderUtil.interpretResult(result,QueryFinished))

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }

  test("Test simple alloc then deref.") { f =>
    // TODO:  This test [should] exercises some of the substitution behavior of State (line 282)
    val src =
      """package com.example.createdestroy;
        |import androidx.appcompat.app.AppCompatActivity;
        |import android.os.Bundle;
        |import android.util.Log;
        |import java.util.List;
        |import java.util.ArrayList;
        |
        |
        |
        |public class MyActivity extends AppCompatActivity {
        |    String o = null;
        |    Boolean o2 = null;
        |    class Foo{
        |        String method(){
        |            return "";
        |        }
        |    }
        |    @Override
        |    protected void onResume() {
        |        List<String> l = new ArrayList<String>();
        |        l.add("hi there");
        |        Foo s = new Foo(); //query0
        |        String s2 = null;
        |        s.method(); //query1
        |    }
        |
        |    @Override
        |    protected void onPause() {
        |    }
        |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs: Set[LSSpec] = Set()
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 200, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode, outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter
      val resSig = Signature("com.example.createdestroy.MyActivity", "void onResume()")
      val query0 = ReceiverNonNull(resSig, BounderUtil.lineForRegex(".*query0.*".r,src), None)
      val result0 = symbolicExecutor.run(query0).flatMap(a => a.terminals)

      //if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result0.nonEmpty)
      BounderUtil.throwIfStackTrace(result0)
      f.expectUnreachable(BounderUtil.interpretResult(result0,QueryFinished))

      // Dereference in loop should witness since we do not have a spec for the list
      val query = ReceiverNonNull(resSig, BounderUtil.lineForRegex(".*query1.*".r, src), Some(".*method.*"))

      // prettyPrinting.dotMethod( query.head.loc, symbolicExecutor.controlFlowResolver, "onPauseCond.dot")

      val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
      //prettyPrinting.dumpDebugInfo(result, "forEach")

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) {
        assert(result.nonEmpty)
      }
      BounderUtil.throwIfStackTrace(result)
      f.expectUnreachable(BounderUtil.interpretResult(result, QueryFinished))

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }

  test("Test irrelevant condition") { f =>
    //TODO: add assertion that "useless" should not materialize and uncomment "doNothing" call
    val src =
      """package com.example.createdestroy;
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
        |    static class Useless{
        |       Useless(){
        |         // Does nothing
        |       }
        |       void doNothing(){
        |         // Does more nothing
        |       }
        |    }
        |    String o = null;
        |    Boolean o2 = null;
        |    Useless useless = null;
        |    Subscription subscription;
        |
        |    @Override
        |    protected void onCreate(Bundle b){
        |        useless = new Useless();
        |        // Do some expensive things
        |    }
        |
        |    @Override
        |    protected void onResume() {
        |       o = "someString";
        |    }
        |
        |    @Override
        |    protected void onPause() {
        |        if (o2 == null){
        |           o2 = true;
        |        }else{
        |           //useless.doNothing();
        |        }
        |        o.toString(); //query1
        |        o = null;
        |    }
        |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        LifecycleSpec.Activity_onPause_onlyafter_onResume
      )
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 60, w,new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode, outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter
      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onPause()"), BounderUtil.lineForRegex(".*query1.*".r,src), Some(".*toString.*"))

      // prettyPrinting.dotMethod( query.head.loc, symbolicExecutor.controlFlowResolver, "onPauseCond.dot")

      val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
      // prettyPrinting.dumpDebugInfo(result, "irrelevantConditional", truncate = false)
      // prettyPrinting.dotWitTree(result, "irrelevantConditional.dot",true)

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      f.expectUnreachable(BounderUtil.interpretResult(result,QueryFinished))
      // Search refutation state for materialized "o2" field
      // Should not be in there since conditional is not relevant
      val o2ExistsInRef = result.exists((p:IPathNode) => BounderUtil.findInWitnessTree(p,
        {pn => pn.qry.state.heapConstraints.exists{
          case (FieldPtEdge(_,fieldName),_) if fieldName == "o2" =>
            println(pn.qry.state)
            true
          case _ => false
        }}).isDefined)
      assert(!o2ExistsInRef)

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Test assign refute") { f =>
    val tests = List(
      ("==", f.expectUnreachable, "unreachable"),
      ("!=",f.expectReachable, "reachable"),
    )
    tests.foreach { case (comp, expected, expectedPrint) =>
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
          |    static class Foo{
          |       String s = null;
          |    }
          |    int i = 5; // we lose precision on integers, using this as source of non determinism
          |
          |    @Override
          |    protected void onCreate(Bundle savedInstanceState) {
          |       Foo f = new Foo();
          |       f.s = new String();
          |       //{x -> v^ * v^.s -> null} //not possible because the next new must have created v^
          |       Foo x = new Foo();
          |       // (skipped if case){f -> v^ * x -> v^ * v^.s -> null}
          |       if(i < 5){
          |         x = f;
          |       }
          |       // s1{f -> v^ * x -> v^ * v^.s -> null}
          |       if(f ${comp} x){
          |         //{x -> v^ * v^.s -> null}
          |         x.s.toString(); //query1
          |       }
          |    }
          |
          |    @Override
          |    protected void onDestroy() {
          |    }
          |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
        ) ++ RxJavaSpec.spec
        val w = new SootWrapper(apk, specs)
        val config = ExecutorConfig(
          stepLimit = 200, w, new SpecSpace(specs),
          component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = om)
        val symbolicExecutor = config.getAbstractInterpreter
        val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
          "void onCreate(android.os.Bundle)"), BounderUtil.lineForRegex(".*query1.*".r, src), Some(".*toString.*"))
        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        //PrettyPrinting.dumpDebugInfo(result, s"alias_${expectedPrint}", truncate = false)

        if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        expected(BounderUtil.interpretResult(result,QueryFinished))

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Test internal object method call") { f =>
    val src = """package com.example.createdestroy;
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
                |
                |    @Override
                |    protected void onCreate(Bundle savedInstanceState) {
                |        super.onCreate(savedInstanceState);
                |        setO();
                |        Log.i("b", o.toString()); //query1
                |    }
                |    protected void setO() {
                |        this.o = new Object();
                |    }
                |
                |    @Override
                |    protected void onDestroy() {
                |        super.onDestroy();
                |        o = null;
                |    }
                |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      implicit val outputMode = MemoryOutputMode
      val config = ExecutorConfig(
        stepLimit = 200, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = outputMode)
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)"),line, Some(".*toString.*"))
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      // prettyPrinting.dumpDebugInfo(result,"setField")

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) {
        assert(result.nonEmpty)
      }
      BounderUtil.throwIfStackTrace(result)
      f.expectUnreachable(BounderUtil.interpretResult(result,QueryFinished))
      assert(BounderUtil.characterizeMaxPath(result)(outputMode) == SingleCallbackMultiMethod)

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  //TODO: problem with org.andstatus
  // src/main/java/org/andstatus/app/service/MyServiceManager.java line 47 ish
  test("Test static method") { f =>
    val tests = List(
      ("true", f.expectUnreachable),
      ("false", f.expectReachable)
    )
    tests.foreach { case (bval, expected) =>
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
          |    public Object o = null;
          |    Subscription subscription;
          |
          |    @Override
          |    protected void onCreate(Bundle savedInstanceState) {
          |        super.onCreate(savedInstanceState);
          |        SillyInnerClass.setO(this);
          |        Log.i("b", o.toString()); //query1
          |    }
          |    static class SillyInnerClass{
          |       private volatile boolean foo = ${bval};
          |       static void setO(MyActivity that) {
          |           SillyInnerClass s = new SillyInnerClass();
          |           if(s.foo){
          |             that.o = new Object();
          |           }
          |       }
          |    }
          |
          |    @Override
          |    protected void onDestroy() {
          |        super.onDestroy();
          |        o = null;
          |    }
          |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
        ) ++ RxJavaSpec.spec
        val w = new SootWrapper(apk, specs)

        implicit val outputMode = MemoryOutputMode
        val config = ExecutorConfig(
          stepLimit = 200, w, new SpecSpace(specs),
          component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode,
          outputMode = outputMode)
        val symbolicExecutor = config.getAbstractInterpreter
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
          "void onCreate(android.os.Bundle)"), line, Some(".*toString.*"))
        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        //PrettyPrinting.dumpDebugInfo(result, s"setField_${bval}_${expected}") //==========

        if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        val interpretedResult = BounderUtil.interpretResult(result, QueryFinished)
        expected(interpretedResult)
        if(interpretedResult == Proven)
          assert(BounderUtil.characterizeMaxPath(result)(outputMode) == SingleCallbackMultiMethod)
      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }

  test("Test assign from") { f =>
    val src = """package com.example.createdestroy;
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
                |
                |    @Override
                |    protected void onCreate(Bundle savedInstanceState) {
                |        super.onCreate(savedInstanceState);
                |        Object o1 = new Object();
                |        o = o1;
                |        o1 = o;
                |        Log.i("b", o1.toString()); //query1
                |    }
                |    protected void setO() {
                |        while (this.o == null){
                |            this.o = new Object();
                |        }
                |    }
                |
                |    @Override
                |    protected void onDestroy() {
                |        super.onDestroy();
                |        o = null;
                |    }
                |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 200, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)"),line, Some(".*toString.*"))
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      // prettyPrinting.dumpDebugInfo(result,"assignFromTest")
      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      f.expectUnreachable(BounderUtil.interpretResult(result,QueryFinished))
    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  test("Test all dereferences") { f =>
    // This test checks the behavior of the AllReceiversNonNull query
    val src =
    """package com.example.createdestroy;
      |import androidx.appcompat.app.AppCompatActivity;
      |import android.os.Bundle;
      |import android.util.Log;
      |import java.util.List;
      |import java.util.ArrayList;
      |
      |import rx.Single;
      |import rx.Subscription;
      |import rx.android.schedulers.AndroidSchedulers;
      |import rx.schedulers.Schedulers;
      |
      |
      |public class MyActivity extends AppCompatActivity {
      |    String o = null;
      |    Boolean o2 = null;
      |    Subscription subscription;
      |
      |    @Override
      |    protected void onResume() {
      |        List<String> l = new ArrayList<String>(); //query0
      |        l.add("hi there");
      |        String s2 = null;
      |        for(String s : l){
      |            s.toString(); //query1
      |        }
      |    }
      |
      |    @Override
      |    protected void onPause() {
      |    }
      |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs:Set[LSSpec] = Set()
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 50, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
      //implicit val om = config.outputMode
      val symbolicExecutor = config.getAbstractInterpreter

      // Entry of oncreate should be reachable (debugging spark issue)
      val qrys = AllReceiversNonNull("com.example.createdestroy.MyActivity").make(symbolicExecutor)
      //qrys.foreach(println)
      val queryEntry = Reachable(Signature("com.example.createdestroy.MyActivity","void onResume()"),
        BounderUtil.lineForRegex(".*query0.*".r,src))
      val resultEntry = symbolicExecutor.run(queryEntry).flatMap(a => a.terminals)
      BounderUtil.throwIfStackTrace(resultEntry)
      f.expectReachable(BounderUtil.interpretResult(resultEntry, QueryFinished))
      // Dereference in loop should witness since we do not have a spec for the list
      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onResume()"), BounderUtil.lineForRegex(".*query1.*".r,src),Some(".*toString.*"))

      // prettyPrinting.dotMethod( query.head.loc, symbolicExecutor.controlFlowResolver, "onPauseCond.dot")

      val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
      // prettyPrinting.dumpDebugInfo(result, "forEach")

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      f.expectReachable(BounderUtil.interpretResult(result, QueryFinished))
    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Test loop") { f =>
    List(
      ("!=",f.expectReachable),
      ("==", f.expectUnreachable)
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
          |
          |    @Override
          |    protected void onCreate(Bundle savedInstanceState) {
          |        super.onCreate(savedInstanceState);
          |        setO();
          |        Log.i("b", o.toString()); //query1
          |    }
          |    protected void setO() {
          |        while (this.o $op null){
          |            this.o = new Object(); //initializeabc
          |        }
          |    }
          |
          |    @Override
          |    protected void onDestroy() {
          |        super.onDestroy();
          |        o = null;
          |    }
          |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
        ) ++ RxJavaSpec.spec
        val w = new SootWrapper(apk, specs)
        val config = ExecutorConfig(
          stepLimit = 200, w,new SpecSpace(specs),
          component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
        val symbolicExecutor = config.getAbstractInterpreter
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
          "void onCreate(android.os.Bundle)"), line, Some(".*toString.*"))

        //val i = BounderUtil.lineForRegex(".*initializeabc.*".r, src)
        //Dump dot of while method
        //val query2 = Qry.makeReach(symbolicExecutor,
        //  Signature("com.example.createdestroy.MyActivity", "void setO()"),i )
        // prettyPrinting.dotMethod(query2.head.loc,symbolicExecutor.controlFlowResolver, "setO.dot")

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        // prettyPrinting.dumpDebugInfo(result, "whileTest")

        if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        expectedResult(BounderUtil.interpretResult(result,QueryFinished))

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Test dynamic dispatch") { f =>
    List(
      (".*query2.*".r,f.expectReachable),
      (".*query1.*".r, f.expectUnreachable)
    ).map { case (queryL, expectedResult) =>
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
           |    Object o2 = new Object();
           |    Subscription subscription;
           |    Runnable r1 = null;
           |    Runnable r2 = null;
           |
           |    @Override
           |    protected void onCreate(Bundle savedInstanceState) {
           |        super.onCreate(savedInstanceState);
           |        o = new Object();
           |        r1 = new Runnable(){
           |          @Override
           |          public void run(){
           |            o.toString(); //query1
           |          }
           |        };
           |        o2 = null;
           |        r2 = new Runnable(){
           |          @Override
           |          public void run(){
           |            o2.toString(); //query2
           |          }
           |        };
           |    }
           |
           |    @Override
           |    protected void onDestroy() {
           |        super.onDestroy();
           |        r1.run();
           |        //r2.run();
           |    }
           |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val specs:Set[LSSpec] = Set()
        val w = new SootWrapper(apk, specs)
        val config = ExecutorConfig(
          stepLimit = 200, w, new SpecSpace(specs),
          component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
        val symbolicExecutor = config.getAbstractInterpreter
        val i = BounderUtil.lineForRegex(queryL, src)
        val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity.*",
          ".*run()"), i, Some(".*toString.*"))


        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        // prettyPrinting.dumpDebugInfo(result, s"dynamicDispatchTest${expectedResult}")
        //        prettyPrinting.dotWitTree(result, "dynamicDispatchTest", true)

        if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        expectedResult(BounderUtil.interpretResult(result,QueryFinished))

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }

  test("Test method call on disaliased object") { f =>
    val src = """package com.example.createdestroy;
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
                |
                |    @Override
                |    protected void onCreate(Bundle savedInstanceState) {
                |        super.onCreate(savedInstanceState);
                |        (new MyActivity()).setO();
                |        Log.i("b", o.toString()); //query1
                |    }
                |    protected void setO() {
                |        this.o = new Object();
                |    }
                |    class Foo{
                |        void run(){
                |            o = new Object();
                |        }
                |    }
                |
                |    @Override
                |    protected void onDestroy() {
                |        Foo f = new Foo(); // Test for object sensitivity
                |        if(o != null){
                |             f.run();
                |        }
                |        super.onDestroy();
                |        o = null;
                |    }
                |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 120, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)"),line, Some(".*toString.*"))
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      // prettyPrinting.dumpDebugInfo(result,"DisaliasedObj")
      // prettyPrinting.dotWitTree(result, "DisaliasedObj.dot",true)

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      f.expectReachable(BounderUtil.interpretResult(result,QueryFinished))

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  test("Boolean conditional") { f =>
    List(
      (true,f.expectReachable),
      (false, f.expectUnreachable)
    ).map { case (initial, expectedResult) =>
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
          |    boolean initialized = $initial;
          |    Subscription subscription;
          |
          |    @Override
          |    protected void onCreate(Bundle savedInstanceState) {
          |        super.onCreate(savedInstanceState);
          |        o = new Object();
          |        initialized = true;
          |    }
          |
          |    @Override
          |    protected void onDestroy() {
          |        super.onDestroy();
          |        if(initialized){
          |            Log.i("b", o.toString()); //query1
          |        }
          |        o = null;
          |        initialized = false;
          |    }
          |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val specs:Set[LSSpec] = Set()
        val w = new SootWrapper(apk, specs)
        val config = ExecutorConfig(
          stepLimit = 200, w, new SpecSpace(specs),
          component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
        val symbolicExecutor = config.getAbstractInterpreter
        val line = BounderUtil.lineForRegex(".*query1.*".r,src)
        val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
          "void onDestroy()"), line, Some(".*toString.*"))

//        prettyPrinting.dotMethod(query.head.loc, symbolicExecutor.controlFlowResolver, "onDestroy_if_not_drop.dot")

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//        prettyPrinting.dumpDebugInfo(result, s"BoolTest_initial_$initial")
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        expectedResult(BounderUtil.interpretResult(result,QueryFinished))

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }

  test("Test dereference with subscribe/unsubscribe and non null subscribe") { f =>
    val src = """package com.example.createdestroy;
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
                |
                |    @Override
                |    protected void onCreate(Bundle savedInstanceState) {
                |        super.onCreate(savedInstanceState);
                |        setContentView(R.layout.activity_main);
                |        o = new Object();
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
                |                    Log.i("b", o.toString()); //query1
                |                });
                |    }
                |
                |    @Override
                |    protected void onDestroy() {
                |        super.onDestroy();
                |        o = null;
                |        if(subscription != null){
                |            subscription.unsubscribe();
                |        }
                |    }
                |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull, RxJavaSpec.subscribeNonNull
      ) ++ LifecycleSpec.spec ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val specSpace = new SpecSpace(specs)

      File.usingTemporaryDirectory() { tmpDir =>
        implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString)
        val config = ExecutorConfig(
          stepLimit = 300, w, specSpace,z3Timeout = Some(30),
          component = Some(List("com\\.example\\.createdestroy\\.*MyActivity.*")), approxMode = f.approxMode)
        val symbolicExecutor = config.getAbstractInterpreter
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
          "void lambda$onCreate$1$MyActivity(java.lang.Object)"), line, Some(".*toString.*"))
        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        //PrettyPrinting.dumpDebugInfo(result, "ProveFieldDerefWithSubscribe")
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        //PrettyPrinting.printWitness(result)
        f.expectUnreachable(BounderUtil.interpretResult(result, QueryFinished))
      }
    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  test("Test witness dereference with subscribe and possibly null field") { f =>
    //Note: this test has caught an unsound subsumption in past versions
    val src = """package com.example.createdestroy;
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
                |
                |    @Override
                |    protected void onCreate(Bundle savedInstanceState) {
                |        super.onCreate(savedInstanceState);
                |        setContentView(R.layout.activity_main);
                |        o = new Object();
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
                |                    Log.i("b", o.toString()); //query1
                |                });
                |    }
                |
                |    @Override
                |    protected void onDestroy() {
                |        o = null;
                |    }
                |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        LifecycleSpec.Fragment_activityCreatedOnlyFirst
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)

      val specSpace = new SpecSpace(specs)
      val config = ExecutorConfig(
        stepLimit = 200, w, specSpace,
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode, outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void lambda$onCreate$1$MyActivity(java.lang.Object)"),line, Some(".*toString.*"))
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      //PrettyPrinting.dumpDebugInfo(result,"WitnessFieldDerefWithSubscribe")
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      f.expectReachable(BounderUtil.interpretResult(result,QueryFinished))

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Test prove dereference of act field with unsubscribe and lambda") { f =>
    val src =
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
        |
        |
        |public class MyFragment extends Fragment {
        |    Subscription subscription;
        |    Object b = null;
        |
        |    public MyFragment() {
        |        // Required empty public constructor
        |    }
        |
        |
        |    @Override
        |    public void onActivityCreated(Bundle savedInstanceState){
        |        super.onActivityCreated(savedInstanceState);
        |        b = new Object();
        |        subscription = Single.create(subscriber -> {
        |            try {
        |                Thread.sleep(2000);
        |            } catch (InterruptedException e) {
        |                e.printStackTrace();
        |            }
        |            subscriber.onSuccess(3);
        |        })
        |                .subscribeOn(Schedulers.newThread())
        |                .observeOn(AndroidSchedulers.mainThread())
        |                .subscribe(a -> {
        |                    Log.i("b", b.toString());// query1
        |                });
        |    }
        |
        |
        |    @Override
        |    public void onDestroy(){
        |        super.onDestroy();
        |        b = null;
        |        subscription.unsubscribe();
        |    }
        |}
        |""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        LifecycleSpec.Fragment_activityCreatedOnlyFirst
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val specSpace = new SpecSpace(specs)
      val config = ExecutorConfig(
        stepLimit = 300, w, specSpace,
        component = Some(List("com.example.createdestroy.MyFragment.*")), approxMode = f.approxMode)
      val symbolicExecutor = config.getAbstractInterpreter
      val query = ReceiverNonNull(
        Signature("com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)"),
        BounderUtil.lineForRegex(".*query1.*".r, src), Some(".*toString.*"))


      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      //prettyPrinting.dumpDebugInfo(result,"ProveFieldWithSubscribeUnsubLambda")
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      f.expectUnreachable(BounderUtil.interpretResult(result,QueryFinished))

    }

    makeApkWithSources(Map("MyFragment.java"->src), MkApk.RXBase, test)
  }

  test("Test prove dereference of return from getActivity") { f =>
    val src =
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
        |
        |
        |public class MyFragment extends Fragment {
        |    Subscription subscription;
        |
        |    public MyFragment() {
        |        // Required empty public constructor
        |    }
        |
        |
        |    @Override
        |    public void onActivityCreated(Bundle savedInstanceState){
        |        super.onActivityCreated(savedInstanceState);
        |        subscription = Single.create(subscriber -> {
        |            try {
        |                Thread.sleep(2000);
        |            } catch (InterruptedException e) {
        |                e.printStackTrace();
        |            }
        |            subscriber.onSuccess(3);
        |        })
        |                .subscribeOn(Schedulers.newThread())
        |                .observeOn(AndroidSchedulers.mainThread())
        |                .subscribe(a -> {
        |                    Activity b = getActivity();// query1
        |                    Log.i("b", b.toString());
        |                });
        |    }
        |
        |
        |    @Override
        |    public void onDestroy(){
        |        super.onDestroy();
        |        subscription.unsubscribe();
        |    }
        |}
        |""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        LifecycleSpec.Fragment_activityCreatedOnlyFirst
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val specSpace = new SpecSpace(specs)
      val config = ExecutorConfig(
        stepLimit = 300, w, specSpace,
        component = Some(List("com.example.createdestroy.MyFragment.*")), approxMode = f.approxMode,
        printAAProgress = false)
      val symbolicExecutor = config.getAbstractInterpreter
      val query = CallinReturnNonNull(
        Signature("com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)"),BounderUtil.lineForRegex(".*query1.*".r, src),
        ".*getActivity.*")

      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      // prettyPrinting.dumpDebugInfo(result,"ProveSafeGetActivityWithSubscribe")
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      f.expectUnreachable(BounderUtil.interpretResult(result,QueryFinished) )

    }

    makeApkWithSources(Map("MyFragment.java"->src), MkApk.RXBase, test)
  }

  test("Test prove dereference of return from getActivity with subscribe non-null spec") {f =>
    val src =
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
        |
        |
        |public class MyFragment extends Fragment {
        |    Subscription subscription;
        |
        |    public MyFragment() {
        |        // Required empty public constructor
        |    }
        |
        |
        |    @Override
        |    public void onActivityCreated(Bundle savedInstanceState){
        |        super.onActivityCreated(savedInstanceState);
        |        subscription = Single.create(subscriber -> {
        |            try {
        |                Thread.sleep(2000);
        |            } catch (InterruptedException e) {
        |                e.printStackTrace();
        |            }
        |            subscriber.onSuccess(3);
        |        })
        |                .subscribeOn(Schedulers.newThread())
        |                .observeOn(AndroidSchedulers.mainThread())
        |                .subscribe(a -> {
        |                    Activity b = getActivity();
        |                    Log.i("b", b.toString());
        |                });
        |    }
        |
        |
        |    @Override
        |    public void onDestroy(){
        |        super.onDestroy();
        |        if(subscription != null){
        |            subscription.unsubscribe();
        |        }
        |    }
        |}
        |""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        LifecycleSpec.Fragment_activityCreatedOnlyFirst, RxJavaSpec.subscribeNonNull
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val specSpace = new SpecSpace(specs)
      val config = ExecutorConfig(
        stepLimit = 300, w, specSpace,
        component = Some(List("com.example.createdestroy.MyFragment.*")), approxMode = f.approxMode)
      val symbolicExecutor = config.getAbstractInterpreter
      val query = CallinReturnNonNull(
        Signature("com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)"),43,
        ".*getActivity.*")

      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result,"MkApk")
//      prettyPrinting.dotWitTree(result, "OldMotiv.dot",includeSubsEdges = true)
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      f.expectUnreachable(BounderUtil.interpretResult(result,QueryFinished) )

    }

    makeApkWithSources(Map("MyFragment.java"->src), MkApk.RXBase, test)
  }


  test("Minimal motivating example with irrelevant unsubscribe") { f =>
    List(
      ("sub.unsubscribe();", f.expectUnreachable, "withUnsub"),
      ("", f.expectReachable, "noUnsub")
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
        val w = new SootWrapper(apk, specs)
        val specSpace = new SpecSpace(specs)
        File.usingTemporaryDirectory() { tmpDir =>
          assert(!(tmpDir / "paths.db").exists)
          //          implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString)
          //          dbMode.startMeta()
          val dbMode = om
          val config = ExecutorConfig(
            stepLimit = 200, w, specSpace,
            component = Some(Seq("com.example.createdestroy.ItemDescriptionFragment",
              "com.example.createdestroy.ExternalPlayerFragment")),
            outputMode = dbMode, approxMode = f.approxMode)
//          implicit val om = config.outputMode
          val symbolicExecutor = config.getAbstractInterpreter
          val line = BounderUtil.lineForRegex(".*query1.*".r, src)
          val query = CallinReturnNonNull(
            Signature("com.example.createdestroy.ExternalPlayerFragment",
            "void call(java.lang.Object)"), line,
            ".*getActivity.*")


          val result = symbolicExecutor.run(query, dbMode)
          val fname = s"IrrelevantUnsub_$fileSuffix"
//          prettyPrinting.dumpDebugInfo(result.flatMap(a => a.terminals), fname)
//          prettyPrinting.dotWitTree(result.flatMap(_.terminals),s"$fname.dot",includeSubsEdges = true, skipCmd = true)
          assert(result.nonEmpty)
          BounderUtil.throwIfStackTrace(result.flatMap(a => a.terminals))
          val interpretedResult = BounderUtil.interpretResult(result.flatMap(a => a.terminals), QueryFinished)
          expectedResult(interpretedResult)
          assert(BounderUtil.characterizeMaxPath(result.flatMap(a => a.terminals)) == MultiCallback)
          val onViewCreatedInTree: Set[List[IPathNode]] = result.flatMap(a => a.terminals).flatMap { node =>
            BounderUtil.findInWitnessTree(node, (p: IPathNode) =>
              p.qry.loc.msgSig.exists(m => m.contains("onViewCreated(")))
          }
          if (onViewCreatedInTree.nonEmpty) {
            println("--- witness ---")
            onViewCreatedInTree.head.foreach { v =>
              println(v.qry.loc)
              println(v.qry.state)
              println()
            }
            println("--- end witness ---")
          }
//          assert(onViewCreatedInTree.isEmpty) //TODO: Relevance currently disabled due to restructuring
        }
      }

      makeApkWithSources(Map("ExternalPlayerFragment.java" -> src,
        "ItemDescriptionFragment.java" -> src2), MkApk.RXBase, test)
    }
  }
  test("Minimal motivating example - even more simplified") { f =>
    // This is simplified a bit from the "minimal motivating example" so its easier to explain in the overview
    List(
      ("sub.unsubscribe();", f.expectUnreachable, "withUnsub"),
      ("", f.expectReachable, "noUnsub")
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
           |public class MyActivity extends Activity implements Action1<Object>{
           |    Subscription sub;
           |    String act = null;
           |    @Override
           |    public void onCreate(Bundle b){
           |        act = new String();
           |        sub = Single.create(subscriber -> {
           |            subscriber.onSuccess(3);
           |        }).subscribe(this);
           |    }
           |
           |    @Override
           |    public void call(Object o){
           |         act.toString(); //query1 : act != null
           |    }
           |
           |    @Override
           |    public void onDestroy(){
           |        act = null;
           |        $destroyLine
           |    }
           |}
           |""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        //Note: subscribeIsUnique rule ommitted from this test to check state relevant to callback
        val a = NamedPureVar("a")
        val specs = Set(
          LSSpec(a::Nil, Nil, Not(SpecSignatures.Activity_onCreate_entry),SpecSignatures.Activity_onCreate_entry),
          RxJavaSpec.call
        ) // ++ Dummy.specs
        val w = new SootWrapper(apk, specs)
        val config = ExecutorConfig(
          stepLimit = 180, w, new SpecSpace(specs),
          component = Some(List("com.example.createdestroy.*MyActivity.*")), approxMode = f.approxMode)
        val symbolicExecutor = config.getAbstractInterpreter

        //print callbacks
        //val callbacks = symbolicExecutor.appCodeResolver.getCallbacks
        //callbacks.foreach(c => println(s"${c.classType} ${c.simpleName}"))

        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val query = ReceiverNonNull(
          Signature("com.example.createdestroy.MyActivity",
          "void call(java.lang.Object)"), line,
          Some(".*toString.*"))

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        val fname = s"Motiv_$fileSuffix"
         //prettyPrinting.dumpDebugInfo(result, fname)
        // prettyPrinting.printWitness(result)
        //        prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
        expectedResult(interpretedResult )
      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }

  test("Button enable/disable") { f =>
    List(
      ("button.setEnabled(true);", f.expectReachable, "badDisable"),
      ("button.setEnabled(false);", f.expectUnreachable, "disable"),
      ("button.setOnClickListener(null);", f.expectUnreachable, "clickSetNull"),
      ("", f.expectReachable, "noDisable")
    ).foreach{
      { case (cancelLine, expectedResult,fileSuffix) =>
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
             |    String remover = null;
             |    View button = null;
             |    @Override
             |    public void onCreate(Bundle b){
             |        button = findViewById(3);
             |        button.setOnClickListener(this);
             |        $cancelLine
             |    }
             |    @Override
             |    public void onClick(View v){
             |        remover.toString(); //query1
             |    }
             |}
             |""".stripMargin

        val test: String => Unit = apk => {
          assert(apk != null)
          val specs = Set[LSSpec](
            ViewSpec.clickWhileNotDisabled,
            ViewSpec.clickWhileActive
//            LifecycleSpec.Activity_createdOnlyFirst
          )
          val w = new SootWrapper(apk, specs)
          val config = ExecutorConfig(
            stepLimit = 200, w, new SpecSpace(specs, Set()),
            component = Some(List("com.example.createdestroy.*RemoverActivity.*")), approxMode = f.approxMode,
            outputMode = om, printAAProgress = true)
          val symbolicExecutor = config.getAbstractInterpreter
          val line = BounderUtil.lineForRegex(".*query1.*".r, src)
          val query = ReceiverNonNull(
            Signature("com.example.createdestroy.RemoverActivity",
            "void onClick(android.view.View)"),
            line, Some(".*toString.*"))

          val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
          val fname = s"Button_disable_$fileSuffix"
          // prettyPrinting.dumpDebugInfo(result, fname)
          // prettyPrinting.printWitness(result)
          assert(result.nonEmpty)
          BounderUtil.throwIfStackTrace(result)
          val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
          expectedResult(interpretedResult )
        }

        makeApkWithSources(Map("RemoverActivity.java" -> src), MkApk.RXBase, test)
      }
    }
  }


  test("Safe with no spec due to must alloc."){ f =>
    // Note: this test also checks for whether interface inheritance is working correctly.
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
         |    String mediaName = null;
         |    @Override
         |    public void onActivityCreated(Bundle savedInstanceState){
         |        mediaName = "my awesome podcast";
         |        sub = Single.create(subscriber -> {
         |            mediaName.toString(); //query1
         |            subscriber.onSuccess(3);
         |        }).subscribe(this);
         |        s = "";
         |    }
         |
         |    @Override
         |    public void call(Object o){
         |         s.toString();
         |    }
         |
         |}
         |""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set[LSSpec]()
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 180, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.*MyFragment.*")), approxMode = f.approxMode, outputMode = om)

      // line in call is reachable
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)

      //line in call cannot throw npe since s is initialized
      // pre-line: -1 virtualinvoke $r1.<com.example.createdestroy.MyFragment: void lambda$onActivityCreated$0$MyFragment(rx.SingleSubscriber)>($r3)
      val query2 = ReceiverNonNull(Signature("com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$0$MyFragment(rx.SingleSubscriber)"),line,Some(".*toString.*"))

      val result2 = symbolicExecutor.run(query2).flatMap(a => a.terminals)

      //prettyPrinting.dumpDebugInfo(result2, "proveNospec")
      val interpretedResult2 = BounderUtil.interpretResult(result2,QueryFinished)
      f.expectUnreachable(interpretedResult2)
    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }
  test("Reachable location call and subscribe"){ f =>
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

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        LifecycleSpec.Fragment_activityCreatedOnlyFirst
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 80, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.*MyFragment.*")), approxMode = f.approxMode, outputMode = om)

      // line in call is reachable
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = Reachable(Signature("com.example.createdestroy.MyFragment",
        "void call(java.lang.Object)"),line)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      //val fname = s"UnreachableLocation"
      // prettyPrinting.dumpDebugInfo(result, fname)
      //      prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
      assert(interpretedResult == Witnessed)

      //line in call cannot throw npe since s is initialized
      val query2 = ReceiverNonNull(Signature("com.example.createdestroy.MyFragment",
        "void call(java.lang.Object)"),line, Some(".*toString.*"))
      val result2 = symbolicExecutor.run(query2).flatMap(a => a.terminals)
      val interpretedResult2 = BounderUtil.interpretResult(result2,QueryFinished)
      f.expectUnreachable(interpretedResult2)
    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }
  test("Test unreachable location simplified") { f =>
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
         |        if(s != null){
         |            sub = Single.create(subscriber -> {
         |                subscriber.onSuccess(3);
         |            }).subscribe(this);
         |        }
         |    }
         |
         |    @Override
         |    public void call(Object o){
         |         this.toString(); //query1 : reachable
         |    }
         |
         |}
         |""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        LifecycleSpec.Fragment_activityCreatedOnlyFirst
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 80, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.*MyFragment.*")), approxMode = f.approxMode, outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = Reachable(Signature("com.example.createdestroy.MyFragment",
        "void call(java.lang.Object)"),line)
      //      val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
      //        "com.example.createdestroy.myfragment",
      //        "void call(java.lang.Object)", line,
      //        ".*getActivity.*".r)

      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      val fname = s"UnreachableLocation"
      // prettyPrinting.dumpDebugInfo(result, fname)
      //      prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
      f.expectUnreachable(interpretedResult )
    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }
  test("Test unreachable location") { f =>
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
         |        if(s != null){ //note: unreachable because s is always null
         |            sub = Single.create(subscriber -> {
         |                subscriber.onSuccess(3);
         |            }).subscribe(this);
         |        }
         |    }
         |
         |    @Override
         |    public void call(Object o){
         |         this.toString(); //query1 : reachable
         |         s = new String();
         |    }
         |
         |}
         |""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        LifecycleSpec.Fragment_activityCreatedOnlyFirst
      ) ++ RxJavaSpec.spec
      val w = new SootWrapper(apk, specs)
      val config = ExecutorConfig(
        stepLimit = 180, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.*MyFragment.*")), outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = Reachable(Signature("com.example.createdestroy.MyFragment",
        "void call(java.lang.Object)"),line)
//      val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
//        "com.example.createdestroy.myfragment",
//        "void call(java.lang.Object)", line,
//        ".*getActivity.*".r)

      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      val fname = s"UnreachableLocation"
      // prettyPrinting.dumpDebugInfo(result, fname)
      //      prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
      f.expectUnreachable(interpretedResult)
    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }

  test("Test missing callback") { f =>
    val src = """package com.example.createdestroy;
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
                |
                |    @Override
                |    protected void onPause() {
                |        o.toString(); // query1
                |        o = new Object();
                |    }
                |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = LifecycleSpec.spec
      val w = new SootWrapper(apk, specs)

      val config = ExecutorConfig(
        stepLimit = 120, w, new SpecSpace(specs),
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode, outputMode = om)
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onPause()"),line, Some(".*toString.*"))
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      //      prettyPrinting.dumpDebugInfo(result, "missingCb")

      if(om == MemoryOutputMode || om.isInstanceOf[DBOutputMode]) assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      f.expectReachable(BounderUtil.interpretResult(result,QueryFinished) )
    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Static field") { f =>
    val src = """package com.example.createdestroy;
                |import androidx.appcompat.app.AppCompatActivity;
                |import android.os.Bundle;
                |import android.util.Log;
                |import android.view.View;
                |import android.os.Handler;
                |import android.view.View.OnClickListener;
                |
                |
                |public class MyActivity extends AppCompatActivity {
                |    static String s = null;
                |    @Override
                |    protected void onResume(){
                |        s = "";
                |    }
                |
                |    @Override
                |    protected void onPause() {
                |        s.toString(); //query1
                |        s = null;
                |    }
                |}""".stripMargin
    val test: String => Unit = apk => {
      File.usingTemporaryDirectory() { tmpDir =>
        assert(apk != null)
        implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString)
        dbMode.startMeta()
        assert(apk != null)
        val specs = new SpecSpace(LifecycleSpec.spec + ViewSpec.clickWhileActive)
        val w = new SootWrapper(apk, specs.getSpecs)

        val config = ExecutorConfig(
          stepLimit = 200, w, specs,
          component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode, outputMode = om)
        val symbolicExecutor = config.getAbstractInterpreter
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val pauseReachable = Reachable(Signature("com.example.createdestroy.MyActivity",
          "void onPause()"), line)

        val resultReachable = symbolicExecutor.run(pauseReachable)
          .flatMap(a => a.terminals)
        //      prettyPrinting.dumpDebugInfo(resultReachable, "staticReach")
        assert(resultReachable.nonEmpty)
        BounderUtil.throwIfStackTrace(resultReachable)
        assert(BounderUtil.interpretResult(resultReachable, QueryFinished) == Witnessed)

        val npe = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
          "void onPause()"), line, Some(".*toString.*"))

        val res2 = symbolicExecutor.run(npe).flatMap(a => a.terminals)
        //prettyPrinting.dumpDebugInfo(res2, "staticNPE")
        assert(res2.nonEmpty)
        BounderUtil.throwIfStackTrace(res2)
        f.expectReachable(BounderUtil.interpretResult(res2, QueryFinished))
      }

    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Should handle chained onClick"){ f =>
    //TODO: this test sometimes failes assertion on
    // src/ast/datatype_decl_plugin.cpp line 1241
    // z3 commit: 36ca98cbbe89e9404c210f5a2805e41010a24288

    // I( ci v.setOnClickListener(l) ) <= cb l.onClick()
    val src = """package com.example.createdestroy;
                |import androidx.appcompat.app.AppCompatActivity;
                |import android.os.Bundle;
                |import android.util.Log;
                |import android.view.View;
                |import android.os.Handler;
                |import android.view.View.OnClickListener;
                |
                |
                |public class MyActivity extends AppCompatActivity implements OnClickListener {
                |    String s = "";
                |    @Override
                |    protected void onResume(){
                |        View v = findViewById(3);
                |        v.setOnClickListener(this);
                |    }
                |    @Override
                |    public void onClick(View view){
                |        View v2 = findViewById(4);
                |        v2.setOnClickListener(new OnClickListener(){
                |            @Override
                |            public void onClick(View view){
                |                s.toString();//query1
                |            }
                |        });
                |    }
                |
                |}""".stripMargin
    val test: String => Unit = apk => {
      File.usingTemporaryDirectory() { tmpDir =>
        assert(apk != null)
        implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString)
        dbMode.startMeta()
        val specs = new SpecSpace(Set(ViewSpec.clickWhileActive, ViewSpec.viewOnlyReturnedFromOneActivity))
        val w = new SootWrapper(apk, specs.getSpecs)

        val config = ExecutorConfig(
          stepLimit = 200, w, specs,
          component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode,
          approxMode = f.approxMode)
        val symbolicExecutor = config.getAbstractInterpreter

        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val reach = Reachable(Signature("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)"), line)
        val nullReachRes = symbolicExecutor.run(reach,dbMode).flatMap(a => a.terminals)
//        prettyPrinting.dumpDebugInfo(nullReachRes, "clickClickReach")
        BounderUtil.throwIfStackTrace(nullReachRes)
        f.expectReachable(BounderUtil.interpretResult(nullReachRes, QueryFinished) )
      }

    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Should attach click to Activity") { f =>
    val src = """package com.example.createdestroy;
                |import androidx.appcompat.app.AppCompatActivity;
                |import android.os.Bundle;
                |import android.util.Log;
                |import android.view.View;
                |import android.os.Handler;
                |import android.view.View.OnClickListener;
                |
                |
                |public class MyActivity extends AppCompatActivity {
                |    String s = null;
                |    @Override
                |    protected void onResume(){
                |        View v = findViewById(3);
                |        s = "";
                |        v.setOnClickListener(new OnClickListener(){
                |             @Override
                |             public void onClick(View v){
                |               s.toString(); // query1
                |             }
                |          });
                |    }
                |
                |    @Override
                |    protected void onPause() {
                |        s = null;
                |    }
                |}""".stripMargin
    val test: String => Unit = apk => {
      File.usingTemporaryDirectory() { tmpDir =>
        assert(apk != null)
        //implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString)
        //dbMode.startMeta()
        implicit val dbMode = MemoryOutputMode //LifecycleSpec.spec +
        val specs = new SpecSpace( Set(ViewSpec.clickWhileActive,
           ViewSpec.viewOnlyReturnedFromOneActivity))
//        val specs = new SpecSpace(Set(ViewSpec.clickWhileActive))
        val w = new SootWrapper(apk, specs.getSpecs)

        val config = ExecutorConfig(
          stepLimit = 180, w, specs,
          component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode,
          approxMode = f.approxMode)
        val symbolicExecutor = config.getAbstractInterpreter
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val clickMethodReachable = Reachable(Signature("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)"), line)

        val resultClickReachable = symbolicExecutor.run(clickMethodReachable, dbMode)
          .flatMap(a => a.terminals)
        // prettyPrinting.dumpDebugInfo(resultClickReachable, "clickReachable")
        assert(resultClickReachable.nonEmpty)
        BounderUtil.throwIfStackTrace(resultClickReachable)
        f.expectReachable(BounderUtil.interpretResult(resultClickReachable, QueryFinished) )

        val nullUnreach = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)"),line, Some(".*toString.*"))
        val nullUnreachRes = symbolicExecutor.run(nullUnreach, dbMode).flatMap(a => a.terminals)
        //PrettyPrinting.dumpDebugInfo(nullUnreachRes, "clickNullUnreachable")
        println("Witness Null")
        // prettyPrinting.printWitness(nullUnreachRes)
        assert(nullUnreachRes.nonEmpty)
        //PrettyPrinting.printWitness(nullUnreachRes)
        BounderUtil.throwIfStackTrace(nullUnreachRes)
        f.expectUnreachable(BounderUtil.interpretResult(nullUnreachRes, QueryFinished))
      }

    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  ignore("Should attach click to Activity2") { f =>
    //Click attached to different activity
    //TODO: ====================== uncomment extra pieces and un-ignore this test
    val src = """package com.example.createdestroy;
                |import androidx.appcompat.app.AppCompatActivity;
                |import android.os.Bundle;
                |import android.util.Log;
                |import android.view.View;
                |import android.os.Handler;
                |import android.view.View.OnClickListener;
                |
                |
                |public class MyActivity extends AppCompatActivity {
                |    String s = null;
                |    static OnClickListener listener2 = null;
                |    @Override
                |    protected void onResume(){
                |        View v = findViewById(3);
                |        s = "";
                |        OnClickListener listener1 = new OnClickListener(){
                |             @Override
                |             public void onClick(View v){
                |               //View view2 = MyActivity.this.findViewById(4);
                |               //view2.setOnClickListener(listener2);
                |               s.toString(); // query1
                |               // listener2 = new OnClickListener(){ //TODO: uncomment?
                |               //   @Override
                |               //   public void onClick(View v){
                |               //      s.toString(); // query2 can throw null pointer exception
                |               //   }
                |               // };
                |
                |
                |             }
                |          };
                |        v.setOnClickListener(listener1);
                |        //View view2 = findViewById(4);
                |        //view2.setOnClickListener(listener2);
                |    }
                |
                |    @Override
                |    protected void onPause() {
                |        s = null;
                |
                |    }
                |}""".stripMargin
    val test: String => Unit = apk => {
      File.usingTemporaryDirectory() { tmpDir =>
        assert(apk != null)
        implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString)
        dbMode.startMeta()
        //        implicit val dbMode = MemoryOutputMode
        // LifecycleSpec.spec +
        val specs = new SpecSpace( Set(ViewSpec.clickWhileActive, ViewSpec.viewOnlyReturnedFromOneActivity))
        // + ViewSpec.noDupeFindView) //TODO: =====================  add noDupe back in if other tests use it
        //        val specs = new SpecSpace(Set(ViewSpec.clickWhileActive))
        val w = new SootWrapper(apk, specs.getSpecs)

        val config = ExecutorConfig(
          stepLimit = 180, w, specs,
          component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode,
          approxMode = f.approxMode)
        val symbolicExecutor = config.getAbstractInterpreter
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val clickMethodReachable = Reachable(Signature("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)"), line)

        val resultClickReachable = symbolicExecutor.run(clickMethodReachable, dbMode)
          .flatMap(a => a.terminals)
        // prettyPrinting.dumpDebugInfo(resultClickReachable, "clickReachable")
        assert(resultClickReachable.nonEmpty)
        BounderUtil.throwIfStackTrace(resultClickReachable)
        f.expectReachable(BounderUtil.interpretResult(resultClickReachable, QueryFinished) )

        val nullUnreach = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)"),line, Some(".*toString.*"))
        val nullUnreachRes = symbolicExecutor.run(nullUnreach, dbMode).flatMap(a => a.terminals)
        // prettyPrinting.dumpDebugInfo(nullUnreachRes, "clickNullUnreachable")
        println("Witness Null")
        // prettyPrinting.printWitness(nullUnreachRes)
        assert(nullUnreachRes.nonEmpty)
        BounderUtil.throwIfStackTrace(nullUnreachRes)
        f.expectUnreachable(BounderUtil.interpretResult(nullUnreachRes, QueryFinished) )

        //TODO: uncomment
        //        val line2 = BounderUtil.lineForRegex(".*query2.*".r, src)
        //        val nullReach = ReceiverNonNull("com.example.createdestroy.MyActivity$1$1",
        //          "void onClick(android.view.View)", line2, Some(".*toString.*"))
        //        val nullReachRes = symbolicExecutor.run(nullReach,dbMode).flatMap(a => a.terminals)
        //        prettyPrinting.dumpDebugInfo(nullReachRes, "clickNullReach")
        //        BounderUtil.throwIfStackTrace(nullReachRes)
        //        assert(BounderUtil.interpretResult(nullReachRes, QueryFinished) == Witnessed)
      }

    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Finish allows click after pause") { f =>
    List(
      ("", f.expectUnreachable),
      ("MyActivity.this.finish();", f.expectReachable),
    ).foreach {
      case (finishLine, expected) =>
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
             |public class MyActivity extends AppCompatActivity {
             |    String s = null;
             |    static OnClickListener listener2 = null;
             |    @Override
             |    protected void onResume(){
             |        View v = findViewById(3);
             |        s = "";
             |        v.setOnClickListener(new OnClickListener(){
             |           @Override
             |           public void onClick(View v){
             |             s.toString(); // query1
             |           }
             |        });
             |        (new Handler()).postDelayed(new Runnable(){
             |           @Override
             |           public void run(){
             |             ${finishLine}
             |           }
             |        }, 3000);
             |    }
             |
             |    @Override
             |    protected void onPause() {
             |        s = null;
             |
             |    }
             |}""".stripMargin
        val test: String => Unit = apk => {
          File.usingTemporaryDirectory() { tmpDir =>
            assert(apk != null)
            val dbFile = tmpDir / "paths.db"
            //implicit val dbMode = DBOutputMode(dbFile.toString)
            //dbMode.startMeta()
            implicit val dbMode = MemoryOutputMode
            //            implicit val dbMode = MemoryOutputMode
            val specs = new SpecSpace(Set(
              ViewSpec.clickWhileActive,
              ViewSpec.viewOnlyReturnedFromOneActivity,
            ) ++ Dummy.specs) // ++ LifecycleSpec.spec)
            val w = new SootWrapper(apk, specs.getSpecs)

            val config = ExecutorConfig(
              stepLimit = 280, w, specs,
              component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode,
              z3Timeout = Some(30), approxMode = f.approxMode)
            val symbolicExecutor = config.getAbstractInterpreter
            val line = BounderUtil.lineForRegex(".*query1.*".r, src)
            //            val clickReachable = Reachable("com.example.createdestroy.MyActivity$1",
            //              "void onClick(android.view.View)", line)

            //            val resultClickReachable = symbolicExecutor.run(clickReachable, dbMode)
            //              .flatMap(a => a.terminals)
            //            prettyPrinting.dumpDebugInfo(resultClickReachable, "clickFinish")
            //            assert(resultClickReachable.nonEmpty)
            //            BounderUtil.throwIfStackTrace(resultClickReachable)
            //            assert(BounderUtil.interpretResult(resultClickReachable, QueryFinished) == Witnessed)


            val nullUnreach = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity$1",
              "void onClick(android.view.View)"), line, Some(".*toString.*"))
            val nullUnreachRes = symbolicExecutor.run(nullUnreach, dbMode).flatMap(a => a.terminals)
            // prettyPrinting.dumpDebugInfo(nullUnreachRes, "finishNullUnreachRes")
            assert(nullUnreachRes.nonEmpty)
            BounderUtil.throwIfStackTrace(nullUnreachRes)
            // prettyPrinting.printWitness(nullUnreachRes)
            expected(BounderUtil.interpretResult(nullUnreachRes, QueryFinished))
          }

        }
        makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }

  ignore("Should not invoke methods on view after activity destroyed spec") { f =>
    //TODO: not fully implemented
    //TODO: what was the bug for this one?

    val src =
      """package com.example.createdestroy;
        |import androidx.appcompat.app.AppCompatActivity;
        |import android.os.Bundle;
        |import android.util.Log;
        |import android.view.View;
        |import android.os.Handler;
        |
        |
        |public class MyActivity extends AppCompatActivity {
        |    protected Handler keyRepeatHandler = new Handler();
        |    @Override
        |    protected void onCreate(Bundle savedInstanceState){
        |        View v = findViewById(3);
        |        Runnable r = new Runnable(){
        |            @Override
        |            public void run(){
        |                v.setVisibility(View.GONE); //query1
        |            }
        |        };
        |        keyRepeatHandler.postDelayed(r,3000);
        |    }
        |
        |    @Override
        |    protected void onDestroy() {
        |    }
        |}""".stripMargin
    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = new SpecSpace(Set() /*LifecycleSpec.spec*/ , Set(ViewSpec.disallowCallinAfterActivityPause))
      val w = new SootWrapper(apk, specs.getSpecs)

      val config = ExecutorConfig(
        stepLimit = 120, w, specs,
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val runMethodReachable = Reachable(Signature("com.example.createdestroy.MyActivity$1",
        "void run()"), line)

      val resultRunMethodReachable = symbolicExecutor.run(runMethodReachable)
        .flatMap(a => a.terminals)
      //      prettyPrinting.dumpDebugInfo(resultRunMethodReachable, "RunnableInHandler")
      assert(resultRunMethodReachable.nonEmpty)
      BounderUtil.throwIfStackTrace(resultRunMethodReachable)
      assert(BounderUtil.interpretResult(resultRunMethodReachable, QueryFinished) == Witnessed)

      val setVisibleCallin_ErrReachable = DisallowedCallin("com.example.createdestroy.MyActivity$1",
        "void run()", ViewSpec.disallowCallinAfterActivityPause)


      val resultsErrReachable = symbolicExecutor.run(setVisibleCallin_ErrReachable)
      val resultsErrReachableTerm = resultsErrReachable.flatMap(a => a.terminals)
      //TODO:=============== disallow specs need to be added to specspace allI somehow
      //      prettyPrinting.dumpDebugInfo(resultsErrReachableTerm, "ViewCallinDisallow2")
      //TODO:====== bad subsumption
      BounderUtil.throwIfStackTrace(resultsErrReachableTerm)
      f.expectReachable(BounderUtil.interpretResult(resultsErrReachableTerm, QueryFinished) )
    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Resumed paused test") { f =>
    val startTime = System.nanoTime()
    //Click attached to different activity
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
         |public class MyActivity extends AppCompatActivity {
         |    String s = null;
         |    String s2 = "";
         |    @Override
         |    protected void onResume(){
         |        s = "";
         |        s2.toString(); //query2
         |        s2 = null;
         |    }
         |
         |    @Override
         |    protected void onPause() {
         |        s.toString(); // query1
         |        s = null;
         |        s2 = "";
         |    }
         |}""".stripMargin
    val test: String => Unit = apk => {
      File.usingTemporaryDirectory() { tmpDir =>
        assert(apk != null)
        val dbFile = tmpDir / "paths.db"
        println(dbFile)
        //implicit val dbMode = DBOutputMode(dbFile.toString)
        //dbMode.startMeta()
        implicit val dbMode = MemoryOutputMode
        //        val specs = new SpecSpace(LifecycleSpec.spec + ViewSpec.clickWhileActive)
        val specs = new SpecSpace(Set(
          LifecycleSpec.Activity_onResume_first_orAfter_onPause,
          LifecycleSpec.Activity_onPause_onlyafter_onResume
        ))
        val w = new SootWrapper(apk, specs.getSpecs)

        val config = ExecutorConfig(
          stepLimit = 300, w, specs,
          component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode)
        val symbolicExecutor = config.getAbstractInterpreter

        // Null deref onPause unreachable
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val nullUnreach = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
          "void onPause()"), line, Some(".*toString.*"))
        val nullUnreachRes = symbolicExecutor.run(nullUnreach, dbMode).flatMap(a => a.terminals)
        // prettyPrinting.dumpDebugInfo(nullUnreachRes, s"ResumedPaused_NPE_Unreach")
        assert(nullUnreachRes.nonEmpty)
        BounderUtil.throwIfStackTrace(nullUnreachRes)
        // prettyPrinting.printWitness(nullUnreachRes)
        assert(BounderUtil.interpretResult(nullUnreachRes, QueryFinished) == Proven)

        // Pause reachable
        val pauseReachQ = Reachable(Signature("com.example.createdestroy.MyActivity", "void onPause()"), line)
        val pauseReachRes = symbolicExecutor.run(pauseReachQ, dbMode).flatMap(a => a.terminals)
        assert(pauseReachRes.nonEmpty)
        BounderUtil.throwIfStackTrace(pauseReachRes)
        f.expectReachable(BounderUtil.interpretResult(pauseReachRes, QueryFinished))

        // Null deref onResume unreachable
        val line2 = BounderUtil.lineForRegex(".*query2.*".r, src)
        val nullUnreach2 = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
          "void onResume()"), line2, Some(".*toString.*"))
        val nullUnreachRes2 = symbolicExecutor.run(nullUnreach2, dbMode).flatMap(a => a.terminals)
        PrettyPrinting.dumpDebugInfo(nullUnreachRes2, s"ResumedPaused_NPE_Unreach2")
        assert(nullUnreachRes2.nonEmpty)
        BounderUtil.throwIfStackTrace(nullUnreachRes2)
        //PrettyPrinting.printWitness(nullUnreachRes2)
        f.expectReachable(BounderUtil.interpretResult(nullUnreachRes2, QueryFinished) )
      }

    }
    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase,
      test)
    println(s"Test time(ms) ${(System.nanoTime() - startTime)/1000.0}")
  }
  test("Should treat output of method as different from input even if same variable") { f =>
    //Had a bug where x = foo(x) materializes x as the same pure var in both input and output

    val src =
      """package com.example.createdestroy;
        |import androidx.appcompat.app.AppCompatActivity;
        |import android.os.Bundle;
        |import android.view.View;
        |import android.os.Handler;
        |import android.app.AlertDialog;
        |import android.content.DialogInterface;
        |
        |public class MyActivity extends AppCompatActivity implements DialogInterface.OnClickListener{
        |    Object o = null;
        |    @Override
        |    protected void onCreate(Bundle savedInstanceState){
        |
        |     AlertDialog.Builder b2 = null;
        |     // note that the problem was that setPostive was assumed to return same value as its reciever
        |     // Test with fake spec that only lets onResume occur if setPostive was invoked with different values
        |     // cb a.onResume() -[]-> c := b.setPositiveButton(_,a) /\ c!= b
        |     AlertDialog.Builder b = new AlertDialog.Builder(this).setPositiveButton(0, this);
        |     b.toString();
        |    }
        |    @Override
        |    protected void onResume(){
        |      o.toString(); //query1
        |    }
        |
        |		public void onClick(DialogInterface dialog, int id) {}
        |}""".stripMargin
    val test: String => Unit = apk => {
      assert(apk != null)

      // cb a.onResume() -[]-> c := b.setPositiveButton(_,a) /\ c!= b
      val AlertDialogBuilder = Set("android.app.AlertDialog$Builder")
      val DialogBuilder_set__Button = (negPos: String) => AbsMsg(CIExit,
        SubClassMatcher(AlertDialogBuilder,
          "android.app.AlertDialog\\$Builder set" + negPos + "Button\\(int,android.content.DialogInterface\\$OnClickListener\\)",
          s"DialogBuilder_set${negPos}Button"), b2 :: b :: TopVal :: l :: Nil)
      val neqSpec = LSSpec(a::Nil, b2::b::l::Nil,
        And(DialogBuilder_set__Button("Positive"), LSConstraint(b2,NotEquals,b)),
        SpecSignatures.Activity_onResume_entry)

      val specs = new SpecSpace(Set(neqSpec) , Set())
      val w = new SootWrapper(apk, specs.getSpecs)

      val config = ExecutorConfig(
        stepLimit = 120, w, specs,
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
      val interpreter = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val runMethodReachable = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity",
        "void onResume()"), line, Some(".*toString.*"))
      val qry = runMethodReachable.make(interpreter)

      val resultRunMethodReachable = interpreter.run(runMethodReachable)
        .flatMap(a => a.terminals)
      //      prettyPrinting.dumpDebugInfo(resultRunMethodReachable, "RunnableInHandler")
      assert(resultRunMethodReachable.nonEmpty)
      BounderUtil.throwIfStackTrace(resultRunMethodReachable)
      assert(BounderUtil.interpretResult(resultRunMethodReachable, QueryFinished) == Witnessed)

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Heap relevant even if only null assign") { f =>
    //TODO: not fully implemented
    //TODO: figure out what this was testing for

    val src =
      """package com.example.createdestroy;
        |import androidx.appcompat.app.AppCompatActivity;
        |import android.os.Bundle;
        |import android.util.Log;
        |import android.view.View;
        |import android.os.Handler;
        |
        |
        |public class MyActivity extends AppCompatActivity {
        |    protected Handler keyRepeatHandler = new Handler();
        |    Object o = new Object();
        |    @Override
        |    protected void onCreate(Bundle savedInstanceState){
        |        o = new Object();
        |        Runnable r = new Runnable(){
        |            @Override
        |            public void run(){
        |                o.toString(); //query1
        |            }
        |        };
        |        keyRepeatHandler.postDelayed(r,3000);
        |    }
        |    @Override
        |    protected void onResume(){
        |       method3();
        |    }
        |    void method3(){
        |       method2();
        |    }
        |    void method2(){
        |       method1();
        |    }
        |
        |    void method1(){
        |       o = null;
        |    }
        |
        |    @Override
        |    protected void onDestroy() {
        |    }
        |}""".stripMargin
    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = new SpecSpace(Set() /*LifecycleSpec.spec*/ , Set())
      val w = new SootWrapper(apk, specs.getSpecs)

      val config = ExecutorConfig(
        stepLimit = 120, w, specs,
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val runMethodReachable = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity$1",
        "void run()"), line, Some(".*toString.*"))

      val resultRunMethodReachable = symbolicExecutor.run(runMethodReachable)
        .flatMap(a => a.terminals)
      //      prettyPrinting.dumpDebugInfo(resultRunMethodReachable, "RunnableInHandler")
      assert(resultRunMethodReachable.nonEmpty)
      BounderUtil.throwIfStackTrace(resultRunMethodReachable)
      assert(BounderUtil.interpretResult(resultRunMethodReachable, QueryFinished) == Witnessed)

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }

  ignore("Test corner case from synthesis") { f =>
    //TODO: this is just for testing out weird corner cases the synth finds, leave ignored

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
         |    @Override
         |    protected void onCreate(Bundle b){
         |        button = new Button(this);
         |        button.setOnClickListener(this);
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
         |    }
         |}""".stripMargin


    val test: String => Unit = apk => {
      assert(apk != null)

      val s = NamedPureVar("s")
      val l1 = NamedPureVar("l1")
      val a_onPause = SpecSignatures.Activity_onPause_exit.copy(lsVars = TopVal::a::Nil)
      val a_onResume = SpecSignatures.Activity_onResume_entry.copy(lsVars = TopVal::a::Nil)
      val v_setOnClick = setOnClickListenerI.copy(lsVars = TopVal::v::l1::Nil)

      val s1 = LSSpec(a::Nil,Nil, NS(a_onPause, a_onResume), a_onResume)
//      val s1 = LSSpec(a::Nil,Nil, a_onPause, a_onResume)
//      val s2 = LSSpec(l:: v::Nil, Nil, Exists(l1::Nil, v_setOnClick), onClickI)
      val s2 = LSSpec(l:: v::Nil, l1::Nil, v_setOnClick, onClickI)
      val specs = new SpecSpace(Set(
        s1,
//        s2,
      ) /*LifecycleSpec.spec*/ , Set(), Set(v_setOnClick))// Set(onClickI)) //, v_setOnClick))
      val w = new SootWrapper(apk, specs.getSpecs)

      val config = ExecutorConfig(
        stepLimit = 120, w, specs,
        component = None, approxMode = f.approxMode)
      val symbolicExecutor = config.getAbstractInterpreter

      val line = BounderUtil.lineForRegex(".*query1.*".r, srcUnreach)
      val clickSignature = Signature("com.example.createdestroy.MyActivity$1",
        "void onClick(android.view.View)")
      val nullUnreach = ReceiverNonNull(clickSignature, line, Some(".*toString.*"))


      val resultRunMethodReachable = symbolicExecutor.run(nullUnreach)
        .flatMap(a => a.terminals)
      PrettyPrinting.dumpDebugInfo(resultRunMethodReachable, "synthCorner")
      assert(resultRunMethodReachable.nonEmpty)
      BounderUtil.throwIfStackTrace(resultRunMethodReachable)
      assert(BounderUtil.interpretResult(resultRunMethodReachable, QueryFinished) == Witnessed)

    }

    makeApkWithSources(Map("MyActivity.java" -> srcUnreach, "OtherActivity.java" -> srcReach), MkApk.RXBase, test)
  }
  ignore("Should not invoke methods on view after activity destroyed spec ____") { f =>
    //TODO: not fully implemented

    val src =
      """package com.example.createdestroy;
        |import androidx.appcompat.app.AppCompatActivity;
        |import android.os.Bundle;
        |import android.util.Log;
        |import android.view.View;
        |import android.os.Handler;
        |
        |
        |public class MyActivity extends AppCompatActivity {
        |    protected Handler keyRepeatHandler = new Handler();
        |    @Override
        |    protected void onCreate(Bundle savedInstanceState){
        |        View v = findViewById(3);
        |        Runnable r = new Runnable(){
        |            @Override
        |            public void run(){
        |                v.setVisibility(View.GONE); //query1
        |            }
        |        };
        |        keyRepeatHandler.postDelayed(r,3000);
        |    }
        |
        |    @Override
        |    protected void onDestroy() {
        |    }
        |}""".stripMargin
    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = new SpecSpace(Set() /*LifecycleSpec.spec*/ , Set(ViewSpec.disallowCallinAfterActivityPause))
      val w = new SootWrapper(apk, specs.getSpecs)

      val config = ExecutorConfig(
        stepLimit = 120, w, specs,
        component = Some(List("com.example.createdestroy.MyActivity.*")), approxMode = f.approxMode)
      val symbolicExecutor = config.getAbstractInterpreter
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val runMethodReachable = Reachable(Signature("com.example.createdestroy.MyActivity$1",
        "void run()"), line)

      val resultRunMethodReachable = symbolicExecutor.run(runMethodReachable)
        .flatMap(a => a.terminals)
      //      prettyPrinting.dumpDebugInfo(resultRunMethodReachable, "RunnableInHandler")
      assert(resultRunMethodReachable.nonEmpty)
      BounderUtil.throwIfStackTrace(resultRunMethodReachable)
      assert(BounderUtil.interpretResult(resultRunMethodReachable, QueryFinished) == Witnessed)

      val setVisibleCallin_ErrReachable = DisallowedCallin("com.example.createdestroy.MyActivity$1",
        "void run()", ViewSpec.disallowCallinAfterActivityPause)


      val resultsErrReachable = symbolicExecutor.run(setVisibleCallin_ErrReachable)
      val resultsErrReachableTerm = resultsErrReachable.flatMap(a => a.terminals)
      BounderUtil.throwIfStackTrace(resultsErrReachableTerm)
      f.expectReachable(BounderUtil.interpretResult(resultsErrReachableTerm, QueryFinished))
    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Synthesis example - simplification of Connect bot click/finish") { f =>
    //TODO: test reachable locations from EnumModelGenerator ===
    val specs0 = Set[LSSpec](
    )
    val specs1 = Set[LSSpec](
      LSSpec(a::Nil, Nil,
          Or(NS(SpecSignatures.Activity_onPause_exit,SpecSignatures.Activity_onResume_entry),
            Not(SpecSignatures.Activity_onResume_entry)),
          SpecSignatures.Activity_onResume_entry),
      LSSpec(l::v::Nil, Nil, NS(setOnClickListenerI, setOnClickListenerINull), onClickI)
    )
    List(
      ("v.setOnClickListener(null);", f.expectReachable, specs0),
      ("", f.expectReachable, specs1),
      ("v.setOnClickListener(null);", f.expectUnreachable, specs1),
    ).foreach {
      case (disableClick, expected, specs) =>
//        val srcUnreach =
//          s"""package com.example.createdestroy;
//             |import android.app.Activity;
//             |import android.os.Bundle;
//             |import android.util.Log;
//             |import android.view.View;
//             |import android.widget.Button;
//             |import android.os.Handler;
//             |import android.view.View.OnClickListener;
//             |
//             |
//             |public class MyActivity extends Activity {
//             |    String s = null;
//             |    View v = null;
//             |    @Override
//             |    protected void onResume(){
//             |        s = "";
//             |        //v = findViewById(3);
//             |        v = new Button(this);
//             |        v.setOnClickListener(new OnClickListener(){
//             |           @Override
//             |           public void onClick(View v){
//             |             s.toString(); // query1 unreachable
//             |             MyActivity.this.finish();
//             |           }
//             |        });
//             |    }
//             |
//             |    @Override
//             |    protected void onPause() {
//             |        s = null;
//             |        ${disableClick}
//             |    }
//             |}""".stripMargin
//        val srcReach =
//          s"""package com.example.createdestroy;
//             |import android.app.Activity;
//             |import android.os.Bundle;
//             |import android.util.Log;
//             |import android.view.View;
//             |import android.widget.Button;
//             |import android.os.Handler;
//             |import android.view.View.OnClickListener;
//             |
//             |
//             |public class OtherActivity extends Activity implements OnClickListener{
//             |    String s = "";
//             |    @Override
//             |    protected void onCreate(Bundle b){
//             |        (new Button(this)).setOnClickListener(this);
//             |    }
//             |    @Override
//             |    public void onClick(View v){
//             |      s.toString(); // query2 reachable
//             |      OtherActivity.this.finish();
//             |    }
//             |
//             |    @Override
//             |    protected void onPause() {
//             |        s = null;
//             |    }
//             |}""".stripMargin
        val test: String => Unit = apk => {
          File.usingTemporaryDirectory() { tmpDir =>
            assert(apk != null)
            val dbFile = tmpDir / "paths.db"
            println(dbFile)
            // implicit val dbMode = DBOutputMode(dbFile.toString, truncate = false)
            // dbMode.startMeta()
            implicit val dbMode = MemoryOutputMode

            val iSet = Set(onClickI, setOnClickListenerI, setOnClickListenerINull,
              Activity_onResume_entry, Activity_onPause_entry, Button_init)

            val w = new SootWrapper(apk, specs)

            val specSpace = new SpecSpace(specs, matcherSpace = iSet)
            val config = ExecutorConfig(
              stepLimit = 2000, w, specSpace,
              component = Some(List("com.example.createdestroy.*")), outputMode = dbMode, approxMode = f.approxMode)

            //Unreach Location
            {
              val symbolicExecutor = config.getAbstractInterpreter
              val line = BounderUtil.lineForRegex(".*query1.*".r, EnumModelGeneratorTest.srcUnreach(disableClick))
              val nullUnreach = ReceiverNonNull(Signature("com.example.createdestroy.MyActivity$1",
                "void onClick(android.view.View)"), line, Some(".*toString.*"))
              val nullUnreachRes = symbolicExecutor.run(nullUnreach, dbMode).flatMap(a => a.terminals)
//              PrettyPrinting.dumpDebugInfo(nullUnreachRes, s"ConnectBot_simpsynth_${expected}", truncate = false)
              assert(nullUnreachRes.nonEmpty)
              BounderUtil.throwIfStackTrace(nullUnreachRes)
//              PrettyPrinting.printWitness(nullUnreachRes)
              val interpretedResult: BounderUtil.ResultSummary =
                BounderUtil.interpretResult(nullUnreachRes, QueryFinished)
              println(s"expected: $expected")
              println(s"actual: $interpretedResult")
              expected(interpretedResult)
            }



            //Reach Location
            {
              val symbolicExecutor_reach = config.getAbstractInterpreter
              val line_reach = BounderUtil.lineForRegex(".*query2.*".r, EnumModelGeneratorTest.srcReach)
              val nullReach = ReceiverNonNull(Signature("com.example.createdestroy.OtherActivity",
                "void onClick(android.view.View)"), line_reach, Some(".*toString.*"))
              val nullReachRes = symbolicExecutor_reach.run(nullReach, dbMode).flatMap(a => a.terminals)
              val interpretedResult = BounderUtil.interpretResult(nullReachRes,QueryFinished)
              println(s"spec set: ${specs.size}")
              //PrettyPrinting.dumpDebugInfo(nullReachRes, s"ReachSamp_${specs.size}",truncate=false)
              f.expectReachable(interpretedResult )
            }
          }

        }
        makeApkWithSources(Map("MyActivity.java" ->EnumModelGeneratorTest.srcUnreach(disableClick),
          "OtherActivity.java"->EnumModelGeneratorTest.srcReach), MkApk.RXBase,
          test)
    }
  }
}
