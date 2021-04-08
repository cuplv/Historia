package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.lifestate.{ActivityLifecycle, FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.Qry
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, CallGraphSource, FlowdroidCallGraph, SparkCallGraph, SymbolicExecutorConfig, TransferFunctions}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.FixtureAnyFunSuite
import soot.{Scene, SootMethod}

import scala.jdk.CollectionConverters.CollectionHasAsScala

class JimpleFlowdroidWrapperTest extends FixtureAnyFunSuite  {

  case class FixtureParam(cgSource: CallGraphSource)
  override def withFixture(test: OneArgTest) = {
    // Run all tests with both CHA call graph and SparkCallGraph
    withFixture(test.toNoArgTest(FixtureParam(SparkCallGraph)))
//    withFixture(test.toNoArgTest(FixtureParam(CHACallGraph)))
//    withFixture(test.toNoArgTest(FixtureParam(FlowdroidCallGraph)))
  }
  test("Call graph picks up basic edge") { f =>

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
                |        setO(); //query1
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
      val w = new JimpleFlowdroidWrapper(apk, f.cgSource)
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          //          RxJavaSpec.subscribeDoesNotReturnNull
        )), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(50), w, transfer,
        component = None)
      val query = Qry.makeReach(config.getSymbolicExecutor, w, "com.example.createdestroy.MyActivity",
        "void onCreate(android.os.Bundle)",
        BounderUtil.lineForRegex(".*query1.*".r,src))
      val loc = query.head.loc.asInstanceOf[AppLoc]
      val targets: UnresolvedMethodTarget = w.makeInvokeTargets(loc)
      targets.loc.map(println)
      assert(targets.loc.nonEmpty)
    }
    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
  test("Call graph picks up edge based on value from framework") { f =>
    val src =
      """package com.example.createdestroy;
        |import androidx.appcompat.app.AppCompatActivity;
        |import android.os.Bundle;
        |import android.util.Log;
        |import java.util.List;
        |import java.util.ArrayList;
        |import java.util.Iterator;
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
        |    static String o3 = "foo";
        |
        |    @Override
        |    protected void onResume() {
        |        List<String> l = new ArrayList<String>(); //query0
        |        l.add(o3);
        |        String s2 = null;
        |        Iterator it = l.iterator(); // query1 does this call edge exist?
        |        it.hasNext(); //query2 does this call edge exist?
        |        for(String s : l){
        |            s.toString();
        |        }
        |    }
        |
        |    @Override
        |    protected void onPause() {
        |    }
        |}""".stripMargin

    val test: String => Unit = apk => {
      assert(apk != null)
      val w = new JimpleFlowdroidWrapper(apk, f.cgSource)
      val transfer = (cha: ClassHierarchyConstraints) => new TransferFunctions[SootMethod, soot.Unit](w,
        new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
          FragmentGetActivityNullSpec.getActivityNonNull,
          ActivityLifecycle.init_first_callback,
          RxJavaSpec.call,
          //          RxJavaSpec.subscribeDoesNotReturnNull
        )), cha)
      val config = SymbolicExecutorConfig(
        stepLimit = Some(50), w, transfer,
        component = None)
      val query = Qry.makeReceiverNonNull(config.getSymbolicExecutor, w, "com.example.createdestroy.MyActivity",
        "void onResume()",
        BounderUtil.lineForRegex(".*query1.*".r,src), Some(".*iterator.*".r))
      val loc = query.head.loc.asInstanceOf[AppLoc]
      val targets: UnresolvedMethodTarget = w.makeInvokeTargets(loc)
      assert(targets.loc.nonEmpty)

      val jm = query.head.loc.asInstanceOf[AppLoc].method.asInstanceOf[JimpleMethodLoc].method
      val locals = jm.getActiveBody.getLocals
      val pt = Scene.v().getPointsToAnalysis
      val ro = locals.asScala.map{l => l -> pt.reachingObjects(l)}.toMap
      println(ro)

      val ep = Scene.v().getEntryPoints.get(0)
      val ro2 = ep.getActiveBody.getLocals.asScala.map{l => l-> pt.reachingObjects(l)}.toMap
      val allocL = ep.getActiveBody.getLocals.asScala.find(l => l.toString().contains("alloc"))
      val posT = ro2(allocL.get).possibleTypes()
      val dummies = posT.asScala.filter(t => t.toString.contains("Dummy"))
      println(posT)

      val arrayList = Scene.v().getSootClass("java.util.ArrayList")
      val iterMethod = arrayList.getMethod("java.util.Iterator iterator()")
      val ro3 = iterMethod.getActiveBody.getLocals.asScala.map{l => l-> pt.reachingObjects(l)}.toMap
      println(ro3)



      val query2 = Qry.makeReceiverNonNull(config.getSymbolicExecutor, w,
        "com.example.createdestroy.MyActivity",
        "void onResume()",
        BounderUtil.lineForRegex(".*query2.*".r,src), Some(".*iterator.*".r))
      val loc2 = query2.head.loc.asInstanceOf[AppLoc]
      val targets2: UnresolvedMethodTarget = w.makeInvokeTargets(loc2)
      assert(targets2.loc.nonEmpty)
    }
    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
}
