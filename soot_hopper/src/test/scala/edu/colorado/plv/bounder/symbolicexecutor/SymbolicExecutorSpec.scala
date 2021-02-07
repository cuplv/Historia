package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.{ActivityLifecycle, FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, NoTypeSolving, SolverTypeSolving}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, PathNode, PrettyPrinting, Qry}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

class SymbolicExecutorSpec extends AnyFunSuite {

  test("Symbolic Executor should prove an intraprocedural deref"){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, PatchedFlowdroidCallGraph)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val transfer =  (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set()),cha)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(8), w,transfer, printProgress = true)
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeReceiverNonNull(symbolicExecutor, w,
      "com.example.test_interproc_1.MainActivity",
      "java.lang.String objectString()",21)
    // Call symbolic executor

    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    assert(result.size == 1)
    assert(result.iterator.next.qry.isInstanceOf[BottomQry])
//    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/reftest.dot")
    PrettyPrinting.dumpDebugInfo(result, "test_interproc_1_derefSafe")
  }


  test("Symbolic Executor should prove an inter-callback deref"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, PatchedFlowdroidCallGraph)

    val transfer = (cha:ClassHierarchyConstraints) =>
      new TransferFunctions[SootMethod,soot.Unit](w, ActivityLifecycle.spec,cha)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(60), w,transfer,  z3Timeout = Some(30), component = Some(List("com\\.example\\.test_interproc_2.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeReceiverNonNull(symbolicExecutor, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
//    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/foo.dot")
//    PrettyPrinting.printWitnessTraces(result, outFile="/Users/shawnmeier/Desktop/foo.witnesses")
    PrettyPrinting.dumpDebugInfo(result, "test_interproc_2_derefSafe")
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
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
//    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/witnessOnPause.dot")
    PrettyPrinting.dumpDebugInfo(result, "test_interproc_2_onPauseReach")
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
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    PrettyPrinting.dumpDebugInfo(result, "test_interproc_2_onResumeReach")
    assert(BounderUtil.interpretResult(result) == Witnessed)
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
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          RxJavaSpec.subscribeDoesNotReturnNull
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(200), w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
        "void lambda$onCreate$1$MyActivity(java.lang.Object)",31)
      val result = symbolicExecutor.executeBackward(query)
      PrettyPrinting.dumpDebugInfo(result,"MkApk")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Proven)

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }

  test("Test witness dereference with subscribe and possibly null field") {
    // TODO: 9 min 50 seconds with memo version
    // TODO: time with non-memo version?
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
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          RxJavaSpec.subscribeDoesNotReturnNull
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(200), w, transfer,
        component = Some(List("com.example.createdestroy.MyActivity.*")),stateTypeSolving = NoTypeSolving)
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeReceiverNonNull(symbolicExecutor, w, "com.example.createdestroy.MyActivity",
        "void lambda$onCreate$1$MyActivity(java.lang.Object)",31)
      val result = symbolicExecutor.executeBackward(query)
      PrettyPrinting.dumpDebugInfo(result,"MkApk")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Witnessed)

    }

    makeApkWithSources(Map("MyActivity.java"->src), MkApk.RXBase, test)
  }
  test("Test prove dereference of return from getActivity") {
    //TODO: this test is currently timing out not sure if it will work or not
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
          RxJavaSpec.call
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(300), w, transfer,
        component = Some(List("com.example.createdestroy.MyFragment.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeCallinReturnNonNull(symbolicExecutor, w,
        "com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)",43,
        ".*getActivity.*".r)

      val result = symbolicExecutor.executeBackward(query)
      PrettyPrinting.dumpDebugInfo(result,"MkApk")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Proven)

    }

    makeApkWithSources(Map("MyFragment.java"->src), MkApk.RXBase, test)
  }

  ignore("Test prove dereference of return from getActivity with subscribe non-null spec") {
    //TODO: this test is currently timing out not sure if it will work or not
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
//          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          RxJavaSpec.subscribeDoesNotReturnNull
        )),cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(300), w, transfer,
        component = Some(List("com.example.createdestroy.MyFragment.*")))
      val symbolicExecutor = config.getSymbolicExecutor
      val query = Qry.makeCallinReturnNonNull(symbolicExecutor, w,
        "com.example.createdestroy.MyFragment",
        "void lambda$onActivityCreated$1$MyFragment(java.lang.Object)",43,
        ".*getActivity.*".r)

      val result = symbolicExecutor.executeBackward(query)
      PrettyPrinting.dumpDebugInfo(result,"MkApk")
      assert(result.nonEmpty)
      assert(BounderUtil.interpretResult(result) == Proven)

    }

    makeApkWithSources(Map("MyFragment.java"->src), MkApk.RXBase, test)
  }
}
