package edu.colorado.plv.bounder.symbolicexecutor

import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{MultiCallback, Proven, SingleCallbackMultiMethod, SingleMethod, Witnessed}
import edu.colorado.plv.bounder.ir.{JimpleFlowdroidWrapper, JimpleMethodLoc}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, LSSpec, NI, Not, Or}
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LifeState, LifecycleSpec, RxJavaSpec, SAsyncTask, SDialog, SpecSignatures, SpecSpace, ViewSpec}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{AllReceiversNonNull, BottomQry, CallinReturnNonNull, DBOutputMode, DisallowedCallin, FieldPtEdge, IPathNode, MemoryOutputMode, OutputMode, PrettyPrinting, Qry, Reachable, ReceiverNonNull}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite
import soot.{Scene, SootMethod}

class SymbolicExecutorTest extends AnyFunSuite {
  //TODO: ====== Set component filters for each test to improve perf time

  private val prettyPrinting = new PrettyPrinting()
  val cgMode = SparkCallGraph

  test("Symbolic Executor should prove an intraprocedural deref"){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath
    assert(test_interproc_1 != null)
    val specs:Set[LSSpec] = Set()
    val w = new JimpleFlowdroidWrapper(test_interproc_1, cgMode,specs)
    val transfer =  (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(specs),cha)
    val config = SymbolicExecutorConfig(
      stepLimit = 8, w,transfer, printProgress = true)
    implicit val om: OutputMode = config.outputMode
    val symbolicExecutor = config.getSymbolicExecutor
    val query = ReceiverNonNull(
      "com.example.test_interproc_1.MainActivity",
      "java.lang.String objectString()",21)
    // Call symbolic executor
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//    prettyPrinting.dumpDebugInfo(result, "test_interproc_1_derefSafe")
    assert(result.size == 1)
    assert(result.iterator.next.qry.isInstanceOf[BottomQry])
    assert(BounderUtil.characterizeMaxPath(result)== SingleMethod)
  }


  test("Symbolic Executor should prove an inter-callback deref"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, cgMode, LifecycleSpec.spec)

    val transfer = (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(LifecycleSpec.spec),cha)
    val config = SymbolicExecutorConfig(
      stepLimit = 200, w,transfer,  z3Timeout = Some(30),
      component = Some(List("com\\.example\\.test_interproc_2\\.MainActivity.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = ReceiverNonNull(
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
    prettyPrinting.dumpDebugInfo(result, "inter-callback", truncate = false)
    BounderUtil.throwIfStackTrace(result)

    assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)
    assert(result.nonEmpty)
  }
  test("Symbolic executor should witness onPause"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, cgMode,LifecycleSpec.spec)
    val transfer = (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(LifecycleSpec.spec),cha)
    val config = SymbolicExecutorConfig(
      stepLimit = 50, w,transfer,  z3Timeout = Some(30),
      component = Some(List("com\\.example\\.test_interproc_2\\.MainActivity.*")))
    //      component = Some(List("com\\.example\\.test_interproc_2\\.*"))
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val query = Reachable(
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",25)
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/witnessOnPause.dot")
//    prettyPrinting.dumpDebugInfo(result, "test_interproc_2_onPauseReach")
    BounderUtil.throwIfStackTrace(result)
    assert(BounderUtil.interpretResult(result,QueryFinished) == Witnessed)
  }
  test("Symbolic executor should witness onResume"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, cgMode, LifecycleSpec.spec)
    val transfer = (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(LifecycleSpec.spec),cha)
    val config = SymbolicExecutorConfig(
      stepLimit = 50, w,transfer,  z3Timeout = Some(30))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Reachable(
      "com.example.test_interproc_2.MainActivity",
      "void onResume()",20)
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//    prettyPrinting.dumpDebugInfo(result, "test_interproc_2_onResumeReach")
    BounderUtil.throwIfStackTrace(result)
    assert(BounderUtil.interpretResult(result,QueryFinished) == Witnessed)
  }

  test("Test read string literal") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 50, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)", BounderUtil.lineForRegex(".*query1.*".r,src))
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result, "readLiteral")
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Test for each loop") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 200, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      implicit val om = config.outputMode
      val symbolicExecutor = config.getSymbolicExecutor

      // Entry of oncreate should be reachable (debugging spark issue)
      val queryEntry = Reachable(
        "com.example.createdestroy.MyActivity","void onResume()",
        BounderUtil.lineForRegex(".*query0.*".r,src))
      val resultEntry = symbolicExecutor.run(queryEntry).flatMap(a => a.terminals)

      BounderUtil.throwIfStackTrace(resultEntry)
      assert(BounderUtil.interpretResult(resultEntry,QueryFinished) == Witnessed)

      // Dereference in loop should witness since we do not have a spec for the list
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onResume()", BounderUtil.lineForRegex(".*query1.*".r,src))

//      prettyPrinting.dotMethod( query.head.loc, symbolicExecutor.controlFlowResolver, "onPauseCond.dot")

      val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result, "forEach")
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Witnessed)
      // Search refutation state for materialized "o2" field
      // Should not be in there since conditional is not relevant
//      val o2ExistsInRef = result.exists((p:IPathNode) => findInWitnessTree(p,
//        {pn => pn.qry.state.heapConstraints.exists{
//          case (FieldPtEdge(_,fieldName),_) if fieldName == "o2" =>
//            println(pn.qry.state)
//            true
//          case _ => false
//        }}).isDefined)
//      assert(!o2ExistsInRef)

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Test irrelevant condition") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 60, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      implicit val om = config.outputMode
      val symbolicExecutor = config.getSymbolicExecutor
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onPause()", BounderUtil.lineForRegex(".*query1.*".r,src))

//      prettyPrinting.dotMethod( query.head.loc, symbolicExecutor.controlFlowResolver, "onPauseCond.dot")

      val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
      prettyPrinting.dumpDebugInfo(result, "irrelevantConditional", truncate = false)
//      prettyPrinting.dotWitTree(result, "irrelevantConditional.dot",true)
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)
      // Search refutation state for materialized "o2" field
      // Should not be in there since conditional is not relevant
      val o2ExistsInRef = result.exists((p:IPathNode) => findInWitnessTree(p,
        {pn => pn.qry.getState.get.heapConstraints.exists{
          case (FieldPtEdge(_,fieldName),_) if fieldName == "o2" =>
            println(pn.qry.getState)
            true
          case _ => false
        }}).isDefined)
      assert(!o2ExistsInRef)

    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Test assign refute") {
    val tests = List(
      ("!=",Witnessed),
      ("==", Proven)
    )
    tests.foreach { case (comp, expected) =>
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
        val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 200, w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")))
        val symbolicExecutor = config.getSymbolicExecutor
        val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
          "void onCreate(android.os.Bundle)", BounderUtil.lineForRegex(".*query1.*".r, src))
        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        prettyPrinting.dumpDebugInfo(result, s"alias_${expected}", truncate = false)
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        assert(BounderUtil.interpretResult(result,QueryFinished) == expected)

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Test internal object method call") {
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
                |        Log.i("b", o.toString());
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 200, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      implicit val om = config.outputMode
      val symbolicExecutor = config.getSymbolicExecutor
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)",20)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result,"setField")
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)
      assert(BounderUtil.characterizeMaxPath(result) == SingleCallbackMultiMethod)

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  test("Test assign from") {
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
                |        Log.i("b", o1.toString());
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode,specs)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 200, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)",22)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result,"assignFromTest")
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  test("Test all dereferences") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 50, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      implicit val om = config.outputMode
      val symbolicExecutor = config.getSymbolicExecutor

      // Entry of oncreate should be reachable (debugging spark issue)
      val qrys = AllReceiversNonNull("com.example.createdestroy.MyActivity").make(symbolicExecutor)
      qrys.foreach(println)
      val queryEntry = Reachable("com.example.createdestroy.MyActivity","void onResume()",
        BounderUtil.lineForRegex(".*query0.*".r,src))
      val resultEntry = symbolicExecutor.run(queryEntry).flatMap(a => a.terminals)
      BounderUtil.throwIfStackTrace(resultEntry)
      assert(BounderUtil.interpretResult(resultEntry, QueryFinished) == Witnessed)
      // Dereference in loop should witness since we do not have a spec for the list
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onResume()", BounderUtil.lineForRegex(".*query1.*".r,src))

      //      prettyPrinting.dotMethod( query.head.loc, symbolicExecutor.controlFlowResolver, "onPauseCond.dot")

      val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
      //      prettyPrinting.dumpDebugInfo(result, "forEach")
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result, QueryFinished) == Witnessed)
    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Test loop") {
    List(
      ("!=",Witnessed),
      ("==", Proven)
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
        val w = new JimpleFlowdroidWrapper(apk, cgMode,specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 200, w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")))
        val symbolicExecutor = config.getSymbolicExecutor
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
          "void onCreate(android.os.Bundle)", line, Some(".*toString.*"))

        val i = BounderUtil.lineForRegex(".*initializeabc.*".r, src)
        //Dump dot of while method
        val query2 = Qry.makeReach(symbolicExecutor,
          "com.example.createdestroy.MyActivity", "void setO()",i )
//        prettyPrinting.dotMethod(query2.head.loc,symbolicExecutor.controlFlowResolver, "setO.dot")

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//        prettyPrinting.dumpDebugInfo(result, "whileTest")
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        assert(BounderUtil.interpretResult(result,QueryFinished) == expectedResult)

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Test dynamic dispatch") {
    List(
      (".*query2.*".r,Witnessed),
      (".*query1.*".r, Proven)
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
        val w = new JimpleFlowdroidWrapper(apk, cgMode,specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 200, w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")))
        val symbolicExecutor = config.getSymbolicExecutor
        val i = BounderUtil.lineForRegex(queryL, src)
        val query = ReceiverNonNull("com.example.createdestroy.MyActivity.*",
          ".*run.*", i)


        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        prettyPrinting.dumpDebugInfo(result, s"dynamicDispatchTest${expectedResult}")
//        prettyPrinting.dotWitTree(result, "dynamicDispatchTest", true)
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        assert(BounderUtil.interpretResult(result,QueryFinished) == expectedResult)

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }

  test("Test method call on disaliased object") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 120, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)",line)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      // prettyPrinting.dumpDebugInfo(result,"DisaliasedObj")
      // prettyPrinting.dotWitTree(result, "DisaliasedObj.dot",true)
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Witnessed)

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  test("Boolean conditional") {
    List((true,Witnessed), (false, Proven)).map { case (initial, expectedResult) =>
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
        val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 200, w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")))
        val symbolicExecutor = config.getSymbolicExecutor
        val line = BounderUtil.lineForRegex(".*query1.*".r,src)
        val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
          "void onDestroy()", 28)

//        prettyPrinting.dotMethod(query.head.loc, symbolicExecutor.controlFlowResolver, "onDestroy_if_not_drop.dot")

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//        prettyPrinting.dumpDebugInfo(result, s"BoolTest_initial_$initial")
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        assert(BounderUtil.interpretResult(result,QueryFinished) == expectedResult, s"Initial value: $initial")

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }

  test("Test dereference with subscribe/unsubscribe and non null subscribe") {
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
                |                    Log.i("b", o.toString());
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
        FragmentGetActivityNullSpec.getActivityNonNull,
      ) ++ LifecycleSpec.spec ++ RxJavaSpec.spec
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)

      File.usingTemporaryDirectory() { tmpDir =>
        implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString, truncate = false)
        val config = SymbolicExecutorConfig(
          stepLimit = 300, w, transfer,z3Timeout = Some(30),
          component = Some(List("com\\.example\\.createdestroy\\.*MyActivity.*")))
        val symbolicExecutor = config.getSymbolicExecutor
        val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
          "void lambda$onCreate$1$MyActivity(java.lang.Object)", 31)
        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        //prettyPrinting.dumpDebugInfo(result, "ProveFieldDerefWithSubscribe")
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        assert(BounderUtil.interpretResult(result, QueryFinished) == Proven)
      }
    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  test("Test witness dereference with subscribe and possibly null field") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)

      val transfer = (cha:ClassHierarchyConstraints) =>
        new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 200, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void lambda$onCreate$1$MyActivity(java.lang.Object)",line)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      prettyPrinting.dumpDebugInfo(result,"WitnessFieldDerefWithSubscribe")
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Witnessed)

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Test prove dereference of return from getActivity") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode,specs)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 300, w, transfer,
        component = Some(List("com.example.createdestroy.MyFragment.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = CallinReturnNonNull(
        "com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)",BounderUtil.lineForRegex(".*query1.*".r, src),
        ".*getActivity.*")

      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      prettyPrinting.dumpDebugInfo(result,"ProveSafeGetActivityWithSubscribe") //TODO: comment out =====
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)

    }

    makeApkWithSources(Map("MyFragment.java"->src), MkApk.RXBase, test)
  }

  test("Test prove dereference of return from getActivity with subscribe non-null spec") {
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
        LifecycleSpec.Fragment_activityCreatedOnlyFirst,
      ) ++ RxJavaSpec.spec
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 300, w, transfer,
        component = Some(List("com.example.createdestroy.MyFragment.*")))
      implicit val om: OutputMode = config.outputMode
      val symbolicExecutor = config.getSymbolicExecutor
      val query = CallinReturnNonNull(
        "com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)",43,
        ".*getActivity.*")

      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result,"MkApk")
//      prettyPrinting.dotWitTree(result, "OldMotiv.dot",includeSubsEdges = true)
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)

    }

    makeApkWithSources(Map("MyFragment.java"->src), MkApk.RXBase, test)
  }

  def findInWitnessTree(node: IPathNode, nodeToFind: IPathNode => Boolean)
                       (implicit om: OutputMode): Option[List[IPathNode]] = {
    if(nodeToFind(node))
      Some(List(node))
    else{
      node.succ match{
        case Nil => None
        case v => v.collectFirst{
          case v2 if findInWitnessTree(v2, nodeToFind).isDefined => findInWitnessTree(v2,nodeToFind).get
        }
      }
    }
  }
  test("Minimal motivating example with irrelevant unsubscribe") {
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
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs), cha)
        File.usingTemporaryDirectory() { tmpDir =>
          assert(!(tmpDir / "paths.db").exists)
          implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString, truncate = false)
          dbMode.startMeta()
          val config = SymbolicExecutorConfig(
            stepLimit = 200, w, transfer,
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
          assert(interpretedResult == expectedResult)
          assert(BounderUtil.characterizeMaxPath(result.flatMap(a => a.terminals)) == MultiCallback)
          val onViewCreatedInTree: Set[List[IPathNode]] = result.flatMap(a => a.terminals).flatMap { node =>
            findInWitnessTree(node, (p: IPathNode) =>
              p.qry.loc.msgSig.exists(m => m.contains("onViewCreated(")))
          }
          if (onViewCreatedInTree.nonEmpty) {
            println("--- witness ---")
            onViewCreatedInTree.head.foreach { v =>
              println(v.qry.loc)
              println(v.qry.getState)
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
  test("Minimal motivating example - even more simplified") {
    // This is simplified a bit from the "minimal motivating example" so its easier to explain in the overview
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
           |public class MyActivity extends Activity implements Action1<Object>{
           |    Subscription sub;
           |    String act = null;
           |    @Override
           |    public void onResume(){
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
           |    public void onPause(){
           |        act = null;
           |        $destroyLine
           |    }
           |}
           |""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        //Note: subscribeIsUnique rule ommitted from this test to check state relevant to callback
        //TODO: ==== can use smaller spec set?
        val specs = Set(
//          LifecycleSpec.Activity_onResume_first_orAfter_onPause,
          LSSpec("a"::Nil, Nil, Or(
            NI(SpecSignatures.Activity_onPause_exit, SpecSignatures.Activity_onResume_entry),
            Not(SpecSignatures.Activity_onResume_entry))
            , SpecSignatures.Activity_onResume_entry),
//          LifecycleSpec.Activity_onPause_onlyafter_onResume
          RxJavaSpec.call
        ) //++ RxJavaSpec.spec
        val w = new JimpleFlowdroidWrapper(apk, cgMode,specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 180, w, transfer,
          component = Some(List("com.example.createdestroy.*MyActivity.*")))
        implicit val om = config.outputMode
        val symbolicExecutor = config.getSymbolicExecutor

        //print callbacks
        val callbacks = symbolicExecutor.appCodeResolver.getCallbacks
        callbacks.map(c => println(s"${c.classType} ${c.simpleName}"))

        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val query = ReceiverNonNull(
          "com.example.createdestroy.MyActivity",
          "void call(java.lang.Object)", line,
          Some(".*toString.*"))

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
        val fname = s"Motiv_$fileSuffix"
        prettyPrinting.dumpDebugInfo(result, fname)
        prettyPrinting.printWitness(result)
        //        prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
        assert(result.nonEmpty)
        BounderUtil.throwIfStackTrace(result)
        val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
        assert(interpretedResult == expectedResult)
      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Minimal motivating example") {
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
          |public class MyFragment extends Fragment implements Action1<Object>{
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
        assert(apk != null)
        //Note: subscribeIsUnique rule ommitted from this test to check state relevant to callback
        // TODO: relevance could probably be refined so this isn't necessary
        val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          LifecycleSpec.Fragment_activityCreatedOnlyFirst,
//          RxJavaSpec.call
        ) ++ RxJavaSpec.spec
        val w = new JimpleFlowdroidWrapper(apk, cgMode,specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 80, w, transfer,
          component = Some(List("com.example.createdestroy.*MyFragment.*")))
        implicit val om = config.outputMode
        val symbolicExecutor = config.getSymbolicExecutor
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val query = CallinReturnNonNull(
          "com.example.createdestroy.MyFragment",
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
      }

      makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Yamba dismiss (simplified remove fragment)") {
    // Simplified version of Experiments row 2
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
        assert(apk != null)
        //Note: subscribeIsUnique rule ommitted from this test to check state relevant to callback
        // TODO: relevance could probably be refined so this isn't necessary
        val specs = Set[LSSpec](
          SDialog.noDupeShow //TODO: ===== uncomment spec
        )
        val w = new JimpleFlowdroidWrapper(apk, cgMode,specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs, Set(SDialog.disallowDismiss)), cha)
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
      }

      makeApkWithSources(Map("StatusActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Row3: Antennapod execute") {
    // Simplified version of Experiments row 3 (ecoop 19 meier motivating example)
    //TODO: ===================
    List(
      ("button.setEnabled(false);", Proven, "withCheck"),
      ("", Witnessed, "noCheck")
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
        assert(apk != null)
        val specs = Set[LSSpec](
          ViewSpec.clickWhileNotDisabled,
          LifecycleSpec.Activity_createdOnlyFirst
        )
        val w = new JimpleFlowdroidWrapper(apk, cgMode,specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs, Set(SAsyncTask.disallowDoubleExecute)), cha)
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
      }

      makeApkWithSources(Map("RemoverActivity.java" -> src), MkApk.RXBase, test)
    }
  }

  test("Reachable location call and subscribe"){
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
  test("Test unreachable location simplified") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 80, w, transfer,
        component = Some(List("com.example.createdestroy.*MyFragment.*")))
      implicit val om = config.outputMode
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = Reachable("com.example.createdestroy.MyFragment",
        "void call(java.lang.Object)",line)
      //      val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
      //        "com.example.createdestroy.myfragment",
      //        "void call(java.lang.Object)", line,
      //        ".*getActivity.*".r)

      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      val fname = s"UnreachableLocation"
      prettyPrinting.dumpDebugInfo(result, fname)
      //      prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
      assert(interpretedResult == Proven)
    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }
  test("Test unreachable location") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 80, w, transfer,
        component = Some(List("com.example.createdestroy.*MyFragment.*")))
      implicit val om = config.outputMode
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = Reachable("com.example.createdestroy.MyFragment",
        "void call(java.lang.Object)",line)
//      val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
//        "com.example.createdestroy.myfragment",
//        "void call(java.lang.Object)", line,
//        ".*getActivity.*".r)

      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      val fname = s"UnreachableLocation"
      prettyPrinting.dumpDebugInfo(result, fname)
//      prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
      assert(interpretedResult == Proven)
    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }

  test("Test missing callback") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)

//      val parsed = LifeState.parseSpec(ActivityLifecycle.spec)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 120, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onPause()",line)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result, "missingCb")
      assert(result.nonEmpty)
      BounderUtil.throwIfStackTrace(result)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Witnessed)
    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Static field") {
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
      assert(apk != null)
      val specs = new SpecSpace(LifecycleSpec.spec + ViewSpec.clickWhileActive)
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs.getSpecs)

      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        specs,cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 200, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val pauseReachable = Reachable("com.example.createdestroy.MyActivity",
        "void onPause()",line)

      val resultReachable = symbolicExecutor.run(pauseReachable)
        .flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(resultReachable, "staticReach")
      assert(resultReachable.nonEmpty)
      BounderUtil.throwIfStackTrace(resultReachable)
      assert(BounderUtil.interpretResult(resultReachable,QueryFinished) == Witnessed)

      val npe = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onPause()",line, Some(".*toString.*"))

      val res2 = symbolicExecutor.run(npe).flatMap(a => a.terminals)
      prettyPrinting.dumpDebugInfo(res2, "staticNPE")
      assert(res2.nonEmpty)
      BounderUtil.throwIfStackTrace(res2)
      assert(BounderUtil.interpretResult(res2,QueryFinished) == Witnessed)

    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Should handle chained onClick"){
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
        implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString, truncate = false)
        dbMode.startMeta()
        val specs = new SpecSpace(Set(ViewSpec.clickWhileActive, ViewSpec.viewOnlyReturnedFromOneActivity))
        val w = new JimpleFlowdroidWrapper(apk, cgMode, specs.getSpecs)

        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          specs, cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 200, w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode,
          subsumptionEnabled = true)
        val symbolicExecutor = config.getSymbolicExecutor

        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val reach = Reachable("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)", line)
        val nullReachRes = symbolicExecutor.run(reach,dbMode).flatMap(a => a.terminals)
//        prettyPrinting.dumpDebugInfo(nullReachRes, "clickClickReach")
        BounderUtil.throwIfStackTrace(nullReachRes)
        assert(BounderUtil.interpretResult(nullReachRes, QueryFinished) == Witnessed)
      }

    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Should attach click to Activity") {
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
        implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString, truncate = false)
        dbMode.startMeta()
//        implicit val dbMode = MemoryOutputMode //LifecycleSpec.spec +
        val specs = new SpecSpace( Set(ViewSpec.clickWhileActive,
           ViewSpec.viewOnlyReturnedFromOneActivity))
//        val specs = new SpecSpace(Set(ViewSpec.clickWhileActive))
        val w = new JimpleFlowdroidWrapper(apk, cgMode, specs.getSpecs)

        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          specs, cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 180, w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode)
        val symbolicExecutor = config.getSymbolicExecutor
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val clickMethodReachable = Reachable("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)", line)

        val resultClickReachable = symbolicExecutor.run(clickMethodReachable, dbMode)
          .flatMap(a => a.terminals)
        prettyPrinting.dumpDebugInfo(resultClickReachable, "clickReachable")
        assert(resultClickReachable.nonEmpty)
        BounderUtil.throwIfStackTrace(resultClickReachable)
        assert(BounderUtil.interpretResult(resultClickReachable, QueryFinished) == Witnessed)

        val nullUnreach = ReceiverNonNull("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)",line, Some(".*toString.*"))
        val nullUnreachRes = symbolicExecutor.run(nullUnreach, dbMode).flatMap(a => a.terminals) // TODO: Slow
        prettyPrinting.dumpDebugInfo(nullUnreachRes, "clickNullUnreachable")
        println("Witness Null")
        prettyPrinting.printWitness(nullUnreachRes)
        assert(nullUnreachRes.nonEmpty)
        BounderUtil.throwIfStackTrace(nullUnreachRes)
        assert(BounderUtil.interpretResult(nullUnreachRes, QueryFinished) == Proven)
      }

    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  ignore("Should attach click to Activity2") {
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
        implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString, truncate = false)
        dbMode.startMeta()
        //        implicit val dbMode = MemoryOutputMode
        // LifecycleSpec.spec +
        val specs = new SpecSpace( Set(ViewSpec.clickWhileActive, ViewSpec.viewOnlyReturnedFromOneActivity))
        // + ViewSpec.noDupeFindView) //TODO: =====================  add noDupe back in if other tests use it
        //        val specs = new SpecSpace(Set(ViewSpec.clickWhileActive))
        val w = new JimpleFlowdroidWrapper(apk, cgMode, specs.getSpecs)

        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          specs, cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 180, w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode)
        val symbolicExecutor = config.getSymbolicExecutor
        val line = BounderUtil.lineForRegex(".*query1.*".r, src)
        val clickMethodReachable = Reachable("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)", line)

        val resultClickReachable = symbolicExecutor.run(clickMethodReachable, dbMode)
          .flatMap(a => a.terminals)
        prettyPrinting.dumpDebugInfo(resultClickReachable, "clickReachable")
        assert(resultClickReachable.nonEmpty)
        BounderUtil.throwIfStackTrace(resultClickReachable)
        assert(BounderUtil.interpretResult(resultClickReachable, QueryFinished) == Witnessed)

        val nullUnreach = ReceiverNonNull("com.example.createdestroy.MyActivity$1",
          "void onClick(android.view.View)",line, Some(".*toString.*"))
        val nullUnreachRes = symbolicExecutor.run(nullUnreach, dbMode).flatMap(a => a.terminals) // TODO: Slow
        prettyPrinting.dumpDebugInfo(nullUnreachRes, "clickNullUnreachable")
        println("Witness Null")
        prettyPrinting.printWitness(nullUnreachRes)
        assert(nullUnreachRes.nonEmpty)
        BounderUtil.throwIfStackTrace(nullUnreachRes)
        assert(BounderUtil.interpretResult(nullUnreachRes, QueryFinished) == Proven)

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
  test("Finish allows click after pause") {
    List(
      ("", Proven),
      ("MyActivity.this.finish();", Witnessed),
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
            implicit val dbMode = DBOutputMode(dbFile.toString, truncate = false)
            println(dbFile)
            dbMode.startMeta()
            //            implicit val dbMode = MemoryOutputMode
            val specs = new SpecSpace(Set(
              ViewSpec.clickWhileActive, ViewSpec.viewOnlyReturnedFromOneActivity, LifecycleSpec.noResumeWhileFinish,
              LifecycleSpec.Activity_onResume_first_orAfter_onPause //TODO: === testing if this prevents timeout
            )) // ++ LifecycleSpec.spec)
            val w = new JimpleFlowdroidWrapper(apk, cgMode, specs.getSpecs)

            val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
              specs, cha)
            val config = SymbolicExecutorConfig(
              stepLimit = 280, w, transfer,
              component = Some(List("com.example.createdestroy.MyActivity.*")), outputMode = dbMode)
            val symbolicExecutor = config.getSymbolicExecutor
            val line = BounderUtil.lineForRegex(".*query1.*".r, src)
            //            val clickReachable = Reachable("com.example.createdestroy.MyActivity$1",
            //              "void onClick(android.view.View)", line)

            //            val resultClickReachable = symbolicExecutor.run(clickReachable, dbMode)
            //              .flatMap(a => a.terminals)
            //            prettyPrinting.dumpDebugInfo(resultClickReachable, "clickFinish")
            //            assert(resultClickReachable.nonEmpty)
            //            BounderUtil.throwIfStackTrace(resultClickReachable)
            //            assert(BounderUtil.interpretResult(resultClickReachable, QueryFinished) == Witnessed)


            val nullUnreach = ReceiverNonNull("com.example.createdestroy.MyActivity$1",
              "void onClick(android.view.View)", line, Some(".*toString.*"))
            val nullUnreachRes = symbolicExecutor.run(nullUnreach, dbMode).flatMap(a => a.terminals)
            prettyPrinting.dumpDebugInfo(nullUnreachRes, "finishNullUnreachRes")
            assert(nullUnreachRes.nonEmpty)
            BounderUtil.throwIfStackTrace(nullUnreachRes)
            prettyPrinting.printWitness(nullUnreachRes)
            assert(BounderUtil.interpretResult(nullUnreachRes, QueryFinished) == expected)
            println()
          }

        }
        makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }

  ignore("Should not invoke methods on view after activity destroyed spec") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs.getSpecs)

      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        specs, cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 120, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val runMethodReachable = Reachable("com.example.createdestroy.MyActivity$1",
        "void run()", line)

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
      assert(BounderUtil.interpretResult(resultsErrReachableTerm, QueryFinished) == Witnessed)
    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Row 4: Connect bot click/finish") {
    val startTime = System.currentTimeMillis()
    List(
      ("v.setOnClickListener(null);", Proven),
      ("", Witnessed)
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
            |             MyActivity.this.finish();
            |             ${disableClick}
            |           }
            |        }, 3000);
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
            val dbFile = tmpDir / "paths.db"
            println(dbFile)
            implicit val dbMode = DBOutputMode(dbFile.toString, truncate = false)
            dbMode
              .startMeta()
//            implicit val dbMode = MemoryOutputMode
            //        val specs = new SpecSpace(LifecycleSpec.spec + ViewSpec.clickWhileActive)
            val specs = new SpecSpace(Set(
              ViewSpec.clickWhileActive,
              ViewSpec.viewOnlyReturnedFromOneActivity, //TODO: ===== currently testing which combination of specs causes timeout
              LifecycleSpec.noResumeWhileFinish,
              LifecycleSpec.Activity_onResume_first_orAfter_onPause,
              LifecycleSpec.Activity_onPause_onlyafter_onResume
            ))
            val w = new JimpleFlowdroidWrapper(apk, cgMode, specs.getSpecs)

            val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
              specs, cha)
            val config = SymbolicExecutorConfig(
              stepLimit = 300, w, transfer,
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

        }
        makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase,
          test)
    }
    println(s"Test took ${startTime - System.currentTimeMillis()} milliseconds")
  }

  ignore("Should not invoke methods on view after activity destroyed spec ____") {
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
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs.getSpecs)

      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        specs, cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 120, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val runMethodReachable = Reachable("com.example.createdestroy.MyActivity$1",
        "void run()", line)

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
      assert(BounderUtil.interpretResult(resultsErrReachableTerm, QueryFinished) == Witnessed)
    }

    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
}
