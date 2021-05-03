package edu.colorado.plv.bounder.symbolicexecutor

import better.files.File
import edu.colorado.plv.bounder.{BounderUtil, RunConfig}
import edu.colorado.plv.bounder.BounderUtil.{MultiCallback, Proven, SingleCallbackMultiMethod, SingleMethod, Witnessed}
import edu.colorado.plv.bounder.ir.{JimpleFlowdroidWrapper, JimpleMethodLoc}
import edu.colorado.plv.bounder.lifestate.LifeState.LSSpec
import edu.colorado.plv.bounder.lifestate.{ActivityLifecycle, FragmentGetActivityNullSpec, LifeState, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, SetInclusionTypeSolving}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AllReceiversNonNull, BottomQry, CallinReturnNonNull, DBOutputMode, FieldPtEdge, IPathNode, OutputMode, PrettyPrinting, Qry, Reachable, ReceiverNonNull}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite
import soot.{Scene, SootMethod}

import scala.jdk.CollectionConverters.CollectionHasAsScala
import scala.util.matching.Regex

class SymbolicExecutorTest extends AnyFunSuite {

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
    val w = new JimpleFlowdroidWrapper(test_interproc_1, cgMode, ActivityLifecycle.spec.getSpecs)

    val transfer = (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, ActivityLifecycle.spec,cha)
    val config = SymbolicExecutorConfig(
      stepLimit = 160, w,transfer,  z3Timeout = Some(30), component = Some(List("com\\.example\\.test_interproc_2.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = ReceiverNonNull(
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/foo.dot")
//    PrettyPrinting.printWitnessTraces(result, outFile="/Users/shawnmeier/Desktop/foo.witnesses")
//    prettyPrinting.dumpDebugInfo(result, "test_interproc_2_derefSafe")
    assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)
    assert(result.nonEmpty)
  }
  test("Symbolic executor should witness onPause"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, cgMode,ActivityLifecycle.spec.getSpecs)
    val transfer = (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, ActivityLifecycle.spec,cha)
    val config = SymbolicExecutorConfig(
      stepLimit = 50, w,transfer,  z3Timeout = Some(30))
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val query = Reachable(
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",25)
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/witnessOnPause.dot")
//    prettyPrinting.dumpDebugInfo(result, "test_interproc_2_onPauseReach")
    assert(BounderUtil.interpretResult(result,QueryFinished) == Witnessed)
  }
  test("Symbolic executor should witness onResume"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, cgMode, ActivityLifecycle.spec.getSpecs)
    val transfer = (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, ActivityLifecycle.spec,cha)
    val config = SymbolicExecutorConfig(
      stepLimit = 50, w,transfer,  z3Timeout = Some(30))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Reachable(
      "com.example.test_interproc_2.MainActivity",
      "void onResume()",20)
    val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//    prettyPrinting.dumpDebugInfo(result, "test_interproc_2_onResumeReach")
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
        ActivityLifecycle.init_first_callback,
        RxJavaSpec.call,
        //          RxJavaSpec.subscribeDoesNotReturnNull
      )
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
      val specs:Set[LSSpec] = Set(//FragmentGetActivityNullSpec.getActivityNull,
        //          FragmentGetActivityNullSpec.getActivityNonNull,
        //          ActivityLifecycle.init_first_callback,
        //          ActivityLifecycle.onPause_onlyafter_onResume_init
        //          RxJavaSpec.call,
        //          RxJavaSpec.subscribeDoesNotReturnNull
      )
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 50, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      implicit val om = config.outputMode
      val symbolicExecutor = config.getSymbolicExecutor

      // Entry of oncreate should be reachable (debugging spark issue)
      val queryEntry = Reachable(
        "com.example.createdestroy.MyActivity","void onResume()",
        BounderUtil.lineForRegex(".*query0.*".r,src))
      val resultEntry = symbolicExecutor.run(queryEntry).flatMap(a => a.terminals)
      assert(BounderUtil.interpretResult(resultEntry,QueryFinished) == Witnessed)

      // Dereference in loop should witness since we do not have a spec for the list
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onResume()", BounderUtil.lineForRegex(".*query1.*".r,src))

//      prettyPrinting.dotMethod( query.head.loc, symbolicExecutor.controlFlowResolver, "onPauseCond.dot")

      val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result, "forEach")
      assert(result.nonEmpty)
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
    //TODO: Still intermittently getting o2 why?
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
        ActivityLifecycle.init_first_callback,
        ActivityLifecycle.onPause_onlyafter_onResume_init
        //          RxJavaSpec.call,
        //          RxJavaSpec.subscribeDoesNotReturnNull
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
//      prettyPrinting.dumpDebugInfo(result, "irrelevantConditional")
//      prettyPrinting.dotWitTree(result, "irrelevantConditional.dot",true)
      assert(result.nonEmpty)
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
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          //          RxJavaSpec.subscribeDoesNotReturnNull
        )
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
        prettyPrinting.dumpDebugInfo(result, "alias")
        assert(result.nonEmpty)
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
        ActivityLifecycle.init_first_callback,
        RxJavaSpec.call,
        //          RxJavaSpec.subscribeDoesNotReturnNull
      )
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
      prettyPrinting.dumpDebugInfo(result,"setField")
      assert(result.nonEmpty)
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
        ActivityLifecycle.init_first_callback,
        RxJavaSpec.call,
        RxJavaSpec.subscribeIsUnique
        //          RxJavaSpec.subscribeDoesNotReturnNull
      )
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
      val specs:Set[LSSpec] = Set(//FragmentGetActivityNullSpec.getActivityNull,
        //          FragmentGetActivityNullSpec.getActivityNonNull,
        //          ActivityLifecycle.init_first_callback,
        //          ActivityLifecycle.onPause_onlyafter_onResume_init
        //          RxJavaSpec.call,
        //          RxJavaSpec.subscribeDoesNotReturnNull
      )
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 50, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      implicit val om = config.outputMode
      val symbolicExecutor = config.getSymbolicExecutor

      // Entry of oncreate should be reachable (debugging spark issue)
      val qrys = AllReceiversNonNull("com.example.createdestroy.MyActivity").make(symbolicExecutor,w)
      qrys.foreach(println)
//      val queryEntry = Qry.makeReach(symbolicExecutor, w,
//        "com.example.createdestroy.MyActivity","void onResume()",
//        BounderUtil.lineForRegex(".*query0.*".r,src))
//      val resultEntry = symbolicExecutor.run(queryEntry).flatMap(a => a.terminals)
//      assert(BounderUtil.interpretResult(resultEntry) == Witnessed)
//
//      // Dereference in loop should witness since we do not have a spec for the list
//      val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
//        "void onResume()", BounderUtil.lineForRegex(".*query1.*".r,src))
//
//      //      prettyPrinting.dotMethod( query.head.loc, symbolicExecutor.controlFlowResolver, "onPauseCond.dot")
//
//      val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      //      prettyPrinting.dumpDebugInfo(result, "forEach")
//      assert(result.nonEmpty)
//      assert(BounderUtil.interpretResult(result) == Witnessed)
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
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          RxJavaSpec.subscribeIsUnique
          //            RxJavaSpec.subscribeDoesNotReturnNull
        )
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
        val query2 = Qry.makeReach(symbolicExecutor, w,
          "com.example.createdestroy.MyActivity", "void setO()",i )
//        prettyPrinting.dotMethod(query2.head.loc,symbolicExecutor.controlFlowResolver, "setO.dot")

        val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//        prettyPrinting.dumpDebugInfo(result, "whileTest")
        assert(result.nonEmpty)
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
        val specs = Set(ActivityLifecycle.init_first_callback)
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
//        prettyPrinting.dumpDebugInfo(result, "dynamicDispatchTest")
//        prettyPrinting.dotWitTree(result, "dynamicDispatchTest", true)
        assert(result.nonEmpty)
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
                |             //f.run();
                |        }
                |        super.onDestroy();
                |        o = null;
                |    }
                |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        ActivityLifecycle.init_first_callback,
        RxJavaSpec.call,
        //          RxJavaSpec.subscribeDoesNotReturnNull,
        RxJavaSpec.subscribeIsUnique
      )
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
//      prettyPrinting.dumpDebugInfo(result,"DisaliasedObj")
//      prettyPrinting.dotWitTree(result, "DisaliasedObj.dot",true)
      //dbg code:
//      val l = query.head.loc.containingMethod.get.asInstanceOf[JimpleMethodLoc]
//      val pta = Scene.v().getPointsToAnalysis
//      val ptl = l.method.getActiveBody.getLocals.asScala.map{l =>
//        (l,pta.reachingObjects(l))
//      }
//      val ptf = l.method.getDeclaringClass.getFields.asScala.map{f =>
////        f -> pta.reachingObjects(???, f)
//      }
//      val ctx = l.method.context()
//      println(ptl)
//      println(ptf)
//      println(ctx)
//
//      //end dbg code
      assert(result.nonEmpty)
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
        ActivityLifecycle.init_first_callback,
        RxJavaSpec.call,
        ActivityLifecycle.Fragment_activityCreatedOnlyFirst,
        RxJavaSpec.subscribeIsUnique
      )
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 200, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void lambda$onCreate$1$MyActivity(java.lang.Object)",31)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result,"ProveFieldDerefWithSubscribe")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)
    }
    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  test("Test witness dereference with subscribe and possibly null field") {
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
                |        o = null;
                |    }
                |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        ActivityLifecycle.init_first_callback,
        RxJavaSpec.call,
        ActivityLifecycle.Fragment_activityCreatedOnlyFirst
        //          RxJavaSpec.subscribeDoesNotReturnNull,
        //          RxJavaSpec.subscribeIsUniqueAndNonNull
      )
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)

      val transfer = (cha:ClassHierarchyConstraints) =>
        new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 200, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void lambda$onCreate$1$MyActivity(java.lang.Object)",31)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result,"WitnessFieldDerefWithSubscribe")
      assert(result.nonEmpty)
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
        |                    Activity b = getActivity();
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
        RxJavaSpec.call,
        ActivityLifecycle.Fragment_activityCreatedOnlyFirst
        //          RxJavaSpec.subscribeIsUniqueAndNonNull
      )
      val w = new JimpleFlowdroidWrapper(apk, cgMode,specs)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(specs),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 300, w, transfer,
        component = Some(List("com.example.createdestroy.MyFragment.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = CallinReturnNonNull(
        "com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)",43,
        ".*getActivity.*")

      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
//      prettyPrinting.dumpDebugInfo(result,"ProveSafeGetActivityWithSubscribe")
      assert(result.nonEmpty)
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
        RxJavaSpec.call,
        ActivityLifecycle.Fragment_activityCreatedOnlyFirst,
        //          RxJavaSpec.subscribeDoesNotReturnNull,
        RxJavaSpec.subscribeIsUnique
      )
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
          RxJavaSpec.call,
          ActivityLifecycle.Fragment_activityCreatedOnlyFirst,
          //            RxJavaSpec.subscribeDoesNotReturnNull,
          //            RxJavaSpec.subscribeIsUniqueAndNonNull
        )
        val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs), cha)
        File.usingTemporaryDirectory() { tmpDir =>
          assert(!(tmpDir / "paths.db").exists)
          implicit val dbMode = DBOutputMode((tmpDir / "paths.db").toString, truncate = true)
          dbMode.startMeta()
          val config = SymbolicExecutorConfig(
            stepLimit = 80, w, transfer,
            component = None, outputMode = dbMode)
          implicit val om = config.outputMode
          val symbolicExecutor = config.getSymbolicExecutor
          val line = BounderUtil.lineForRegex(".*query1.*".r, src)
          val query = CallinReturnNonNull(
            "com.example.createdestroy.ExternalPlayerFragment",
            "void call(java.lang.Object)", line,
            ".*getActivity.*")


          val result = symbolicExecutor.run(query, dbMode)
          val fname = s"IrrelevantUnsub_$fileSuffix"
          prettyPrinting.dumpDebugInfo(result.flatMap(a => a.terminals), fname)
          //        prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
         assert(result.nonEmpty)
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
          assert(onViewCreatedInTree.isEmpty)
        }
      }

      makeApkWithSources(Map("ExternalPlayerFragment.java" -> src,
        "ItemDescriptionFragment.java" -> src2), MkApk.RXBase, test)
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
          |    //TODO: add callback with irrelevant subscribe
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
        val specs = Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          RxJavaSpec.call,
          ActivityLifecycle.Fragment_activityCreatedOnlyFirst,
          //            RxJavaSpec.subscribeDoesNotReturnNull,
          //            RxJavaSpec.subscribeIsUniqueAndNonNull
        )
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
//        prettyPrinting.dumpDebugInfo(result, fname)
//        prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
        assert(result.nonEmpty)
        val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
        assert(interpretedResult == expectedResult)
        val onViewCreatedInTree: Set[List[IPathNode]] = result.flatMap{node =>
            findInWitnessTree(node, (p: IPathNode) =>
              p.qry.loc.msgSig.exists(m => m.contains("onViewCreated(")))
        }
        if(onViewCreatedInTree.nonEmpty) {
          println("--- witness ---")
          onViewCreatedInTree.head.foreach{v =>
            println(v.qry.loc)
            println(v.qry.getState)
            println()
          }
          println("--- end witness ---")
        }
        assert(onViewCreatedInTree.isEmpty)
      }

      makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
    }
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
        RxJavaSpec.call,
        ActivityLifecycle.Fragment_activityCreatedOnlyFirst
        //          RxJavaSpec.subscribeDoesNotReturnNull,
        //          RxJavaSpec.subscribeIsUniqueAndNonNull
      )
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
//      prettyPrinting.dumpDebugInfo(result, fname)
//      prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
      assert(result.nonEmpty)
      val interpretedResult = BounderUtil.interpretResult(result,QueryFinished)
      assert(interpretedResult == Proven)
    }

    makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
  }
  test("Test dynamic dispatch2") {
    List(
      (".*query2.*".r,Witnessed),
      (".*query1.*".r, Proven)
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
           |    SomethingAble r = null;
           |    SomethingAble r2 = null;
           |
           |    @Override
           |    protected void onCreate(Bundle savedInstanceState) {
           |        super.onCreate(savedInstanceState);
           |        r = new SomethingAble(){
           |          @Override
           |          public void run(){
           |            o = null;
           |          }
           |        };
           |        r2 = r;
           |        r = new SomethingAble(){
           |          @Override
           |          public void run(){
           |            o = new String();
           |          }
           |        };
           |    }
           |
           |    @Override
           |    protected void onDestroy() {
           |        super.onDestroy();
           |        r.run();
           |        o.toString(); //query1 no NPE
           |        r2.run();
           |        o.toString(); //query2 NPE
           |        r.run();
           |    }
           |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val specs = Set(ActivityLifecycle.init_first_callback)
        val w = new JimpleFlowdroidWrapper(apk, cgMode, specs)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(specs), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = 200, w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")),
          //          outputMode = DBOutputMode("/Users/shawnmeier/Desktop/bounder_debug_data/deref2.db")
        )
        val symbolicExecutor = config.getSymbolicExecutor
        val i = BounderUtil.lineForRegex(queryL, src)
        val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
          ".*onDestroy.*", i)


        val result: Set[IPathNode] = symbolicExecutor.run(query).flatMap(a => a.terminals)
//        prettyPrinting.dumpDebugInfo(result, "dynamicDispatchTest2")
//        prettyPrinting.dotWitTree(result, "dynamicDispatchTest2", true)
        assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result,QueryFinished) == expectedResult)

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
      println(s"test: $queryL done")
    }
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
                |    }
                |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val specs = ActivityLifecycle.spec
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs.getSpecs)

//      val parsed = LifeState.parseSpec(ActivityLifecycle.spec)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        specs,cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 120, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = ReceiverNonNull("com.example.createdestroy.MyActivity",
        "void onPause()",line)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      prettyPrinting.dumpDebugInfo(result, "missingCb")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Witnessed)
    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Should not invoke methods on view after activity destroyed spec"){

    val src = """package com.example.createdestroy;
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
      val specs = ActivityLifecycle.spec
      val w = new JimpleFlowdroidWrapper(apk, cgMode, specs.getSpecs)

      //      val parsed = LifeState.parseSpec(ActivityLifecycle.spec)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        specs,cha)
      val config = SymbolicExecutorConfig(
        stepLimit = 120, w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val line = BounderUtil.lineForRegex(".*query1.*".r, src)
      val query = Reachable("com.example.createdestroy.MyActivity$1",
        "void run()",line)
      val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
      prettyPrinting.dumpDebugInfo(result, "RunnableInHandler")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result,QueryFinished) == Witnessed)
      //TODO:============================================= write spec for view methods not called after activity dest

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
}
