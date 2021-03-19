package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.{ActivityLifecycle, FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, SetInclusionTypeSolving}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, DBOutputMode, IPathNode, PrettyPrinting, Qry}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

import scala.util.matching.Regex

class SymbolicExecutorTest extends AnyFunSuite {

  private val prettyPrinting = new PrettyPrinting()
  def lineForRegex(r:Regex, in:String):Int = {
    val lines = in.split("\n")
    lines.indexWhere(r.matches(_)) + 1 // source code line numbers start at 1
  }

  test("Symbolic Executor should prove an intraprocedural deref"){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, PatchedFlowdroidCallGraph)
    val transfer =  (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set()),cha)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(8), w,transfer, printProgress = true)
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeReceiverNonNull(symbolicExecutor, w,
      "com.example.test_interproc_1.MainActivity",
      "java.lang.String objectString()",21)
    // Call symbolic executor

    val result: Set[IPathNode] = symbolicExecutor.executeBackward(query)
    assert(result.size == 1)
    assert(result.iterator.next.qry.isInstanceOf[BottomQry])
    prettyPrinting.dumpDebugInfo(result, "test_interproc_1_derefSafe")
  }


  test("Symbolic Executor should prove an inter-callback deref"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, PatchedFlowdroidCallGraph)

    val transfer = (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, ActivityLifecycle.spec,cha)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(160), w,transfer,  z3Timeout = Some(30), component = Some(List("com\\.example\\.test_interproc_2.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeReceiverNonNull(symbolicExecutor, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val result: Set[IPathNode] = symbolicExecutor.executeBackward(query)
//    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/foo.dot")
//    PrettyPrinting.printWitnessTraces(result, outFile="/Users/shawnmeier/Desktop/foo.witnesses")
    prettyPrinting.dumpDebugInfo(result, "test_interproc_2_derefSafe")
    assert(BounderUtil.interpretResult(result) == Proven)
    assert(result.nonEmpty)
  }
  test("Symbolic executor should witness onPause"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, PatchedFlowdroidCallGraph)
    val transfer = (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, ActivityLifecycle.spec,cha)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(50), w,transfer,  z3Timeout = Some(30))
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val query = Qry.makeReach(symbolicExecutor, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",25)
    val result: Set[IPathNode] = symbolicExecutor.executeBackward(query)
//    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/witnessOnPause.dot")
    prettyPrinting.dumpDebugInfo(result, "test_interproc_2_onPauseReach")
    assert(BounderUtil.interpretResult(result) == Witnessed)
  }
  test("Symbolic executor should witness onResume"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, PatchedFlowdroidCallGraph)
    val transfer = (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, ActivityLifecycle.spec,cha)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(50), w,transfer,  z3Timeout = Some(30))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeReach(symbolicExecutor, w,
      "com.example.test_interproc_2.MainActivity",
      "void onResume()",20)
    val result: Set[IPathNode] = symbolicExecutor.executeBackward(query)
    prettyPrinting.dumpDebugInfo(result, "test_interproc_2_onResumeReach")
    assert(BounderUtil.interpretResult(result) == Witnessed)
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
      val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          RxJavaSpec.subscribeDoesNotReturnNull
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(200), w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)",20)
      val result = symbolicExecutor.executeBackward(query)
      prettyPrinting.dumpDebugInfo(result,"setField")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Proven)

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
      val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          RxJavaSpec.subscribeDoesNotReturnNull
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(200), w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)",22)
      val result = symbolicExecutor.executeBackward(query)
      prettyPrinting.dumpDebugInfo(result,"assignFromTest")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Proven)

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
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
          |        Log.i("b", o.toString());
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
        val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
            FragmentGetActivityNullSpec.getActivityNonNull,
            ActivityLifecycle.init_first_callback,
            RxJavaSpec.call,
            RxJavaSpec.subscribeDoesNotReturnNull
          )), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = Some(200), w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")))
        val symbolicExecutor = config.getSymbolicExecutor
        val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
          "void onCreate(android.os.Bundle)", 20)

        val i = lineForRegex(".*initializeabc.*".r, src)
        //Dump dot of while method
        val query2 = Qry.makeReach(symbolicExecutor, w,
          "com.example.createdestroy.MyActivity", "void setO()",i )
        prettyPrinting.dotMethod(query2.head.loc,symbolicExecutor.controlFlowResolver, "setO.dot")

        val result = symbolicExecutor.executeBackward(query)
        prettyPrinting.dumpDebugInfo(result, "whileTest")
        prettyPrinting.dotWitTree(result, "whileTest", true) //TODO: remove
        assert(result.nonEmpty)
        assert(BounderUtil.interpretResult(result) == expectedResult)

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
           |        Object o2 = null;
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
           |    }
           |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(Set(ActivityLifecycle.init_first_callback)), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = Some(200), w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")))
        val symbolicExecutor = config.getSymbolicExecutor
        val i = lineForRegex(queryL, src)
        val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity.*",
          ".*run.*", i)


        val result = symbolicExecutor.executeBackward(query)
        prettyPrinting.dumpDebugInfo(result, "dynamicDispatchTest")
        prettyPrinting.dotWitTree(result, "dynamicDispatchTest", true)
        assert(result.nonEmpty)
        assert(BounderUtil.interpretResult(result) == expectedResult)

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
    }
  }
  test("Test dynamic dispatch2") {
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
           |    Subscription subscription;
           |    Runnable r = null;
           |    Runnable r2 = null;
           |
           |    @Override
           |    protected void onCreate(Bundle savedInstanceState) {
           |        super.onCreate(savedInstanceState);
           |        r = new Runnable(){
           |          @Override
           |          public void run(){
           |            o = null;
           |          }
           |        };
           |        r2 = r;
           |        r = new Runnable(){
           |          @Override
           |          public void run(){
           |            o = new Object();
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
           |    }
           |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(Set(ActivityLifecycle.init_first_callback)), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = Some(110), w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")),
//          outputMode = DBOutputMode("/Users/shawnmeier/Desktop/bounder_debug_data/deref2.db")
        )
        val symbolicExecutor = config.getSymbolicExecutor
        val i = lineForRegex(queryL, src)
        val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
          ".*onDestroy.*", i)


        val result = symbolicExecutor.executeBackward(query)
        prettyPrinting.dumpDebugInfo(result, "dynamicDispatchTest2")
        prettyPrinting.dotWitTree(result, "dynamicDispatchTest2", true)
        assert(result.nonEmpty)
        assert(BounderUtil.interpretResult(result) == expectedResult)

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
      val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          RxJavaSpec.subscribeDoesNotReturnNull,
          RxJavaSpec.subscribeIsUniqueAndNonNull
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(60), w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)",20)
      val result = symbolicExecutor.executeBackward(query)
      prettyPrinting.dumpDebugInfo(result,"DisaliasedObj")
      prettyPrinting.dotWitTree(result, "DisaliasedObj.dot",true)
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Witnessed)

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  test("Boolean conditional") {
    // TODO: add (false,Proven) when bool vals are handled precisely
    List((true,Witnessed)).map { case (initial, expectedResult) =>
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
          |            Log.i("b", o.toString());
          |        }
          |        o = null;
          |    }
          |}""".stripMargin

      val test: String => Unit = apk => {
        assert(apk != null)
        val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(Set()), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = Some(60), w, transfer,
          component = Some(List("com.example.createdestroy.MyActivity.*")))
        val symbolicExecutor = config.getSymbolicExecutor
        val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
          "void onDestroy()", 28)
        val result = symbolicExecutor.executeBackward(query)
        prettyPrinting.dumpDebugInfo(result, s"BoolTest_initial_$initial")
        assert(result.nonEmpty)
        assert(BounderUtil.interpretResult(result) == expectedResult, s"Initial value: $initial")

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
      val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          RxJavaSpec.subscribeDoesNotReturnNull,
          RxJavaSpec.subscribeIsUniqueAndNonNull
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(200), w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
        "void lambda$onCreate$1$MyActivity(java.lang.Object)",31)
      val result = symbolicExecutor.executeBackward(query)
      prettyPrinting.dumpDebugInfo(result,"ProveFieldDerefWithSubscribe")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Proven)
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
      val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
      val transfer = (cha:ClassHierarchyConstraints) =>
        new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          RxJavaSpec.subscribeDoesNotReturnNull,
          RxJavaSpec.subscribeIsUniqueAndNonNull
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(200), w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")),stateTypeSolving = SetInclusionTypeSolving)
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
        "void lambda$onCreate$1$MyActivity(java.lang.Object)",31)
      val result = symbolicExecutor.executeBackward(query)
      prettyPrinting.dumpDebugInfo(result,"WitnessFieldDerefWithSubscribe")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Witnessed)

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
      val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          RxJavaSpec.call,
          RxJavaSpec.subscribeIsUniqueAndNonNull
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(300), w, transfer,
        component = Some(List("com.example.createdestroy.MyFragment.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
        "com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)",43,
        ".*getActivity.*".r)

      val result = symbolicExecutor.executeBackward(query)
      prettyPrinting.dumpDebugInfo(result,"ProveSafeGetActivityWithSubscribe")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Proven)

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
      val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
      val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          RxJavaSpec.call,
          RxJavaSpec.subscribeDoesNotReturnNull,
          RxJavaSpec.subscribeIsUniqueAndNonNull
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(300), w, transfer,
        component = Some(List("com.example.createdestroy.MyFragment.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
        "com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)",43,
        ".*getActivity.*".r)

      val result = symbolicExecutor.executeBackward(query)
      prettyPrinting.dumpDebugInfo(result,"MkApk")
      prettyPrinting.dotWitTree(result, "OldMotiv.dot",includeSubsEdges = true)
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Proven)

    }

    makeApkWithSources(Map("MyFragment.java"->src), MkApk.RXBase, test)
  }
  test("Minimal motivating example") {
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
          |    //@Override
          |    //public void onViewCreated(View view, Bundle savedInstanceState) {
          |    //    Single.create(subscriber -> {
          |    //        subscriber.onSuccess(4);
          |    //    }).subscribe(r -> {
          |    //        r.toString();
          |    //    });
          |    //}
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
        val w = new JimpleFlowdroidWrapper(apk, CHACallGraph)
        val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
          new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
            FragmentGetActivityNullSpec.getActivityNonNull,
            RxJavaSpec.call,
            RxJavaSpec.subscribeDoesNotReturnNull,
            RxJavaSpec.subscribeIsUniqueAndNonNull
          )), cha)
        val config = SymbolicExecutorConfig(
          stepLimit = Some(300), w, transfer,
          component = Some(List("com.example.createdestroy.MyFragment.*")))
        val symbolicExecutor = config.getSymbolicExecutor
        val line = lineForRegex(".*query1.*".r, src)
        val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
          "com.example.createdestroy.MyFragment",
          "void call(java.lang.Object)", line,
          ".*getActivity.*".r)

        val result = symbolicExecutor.executeBackward(query)
        val fname = s"Motiv_$fileSuffix"
        prettyPrinting.dumpDebugInfo(result, fname)
        prettyPrinting.dotWitTree(result,s"$fname.dot",includeSubsEdges = true, skipCmd = true)
        assert(result.nonEmpty)
        val interpretedResult = BounderUtil.interpretResult(result)
        assert(interpretedResult == expectedResult)

      }

      makeApkWithSources(Map("MyFragment.java" -> src), MkApk.RXBase, test)
    }
  }
}
