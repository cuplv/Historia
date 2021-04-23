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
        stepLimit = 50, w, transfer,
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
        |import android.content.Context;
        |import android.content.SharedPreferences;
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
        |    Runnable r = null;
        |
        |    @Override
        |    protected void onResume() {
        |        List<Runnable> l = new ArrayList<Runnable>(); //query0
        |        r = new Runnable(){
        |          @Override
        |          public void run(){}
        |        };
        |        Runnable run3 = new Runnable(){
        |          @Override
        |          public void run(){}
        |        };
        |        l.add(r);
        |        Iterator it = l.iterator(); // query1 does this call edge exist?
        |        it.hasNext(); //query2 does this call edge exist?
        |        for(Runnable r2 : l){
        |           r2.run(); //query4 should have many edges
        |        }
        |      SharedPreferences pref = this.getSharedPreferences("", Context.MODE_PRIVATE);
        |      SharedPreferences.Editor editor = pref.edit(); //query5
        |      editor.putInt("foo",3);
        |    }
        |
        |    @Override
        |    protected void onPause() {
        |      r.run(); //query3 should have exactly one edge
        |
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
        stepLimit = 50, w, transfer,
        component = None)
      val query = Qry.makeReceiverNonNull(config.getSymbolicExecutor, w, "com.example.createdestroy.MyActivity",
        "void onResume()",
        BounderUtil.lineForRegex(".*query1.*".r,src), Some(".*iterator.*".r))
      val loc = query.head.loc.asInstanceOf[AppLoc]
      val targets: UnresolvedMethodTarget = w.makeInvokeTargets(loc)

      //TODO: dbg code
      val onResumeMethod = query.head.loc.asInstanceOf[AppLoc].method.asInstanceOf[JimpleMethodLoc].method
      val locals = onResumeMethod.getActiveBody.getLocals
      val units = onResumeMethod.getActiveBody.getUnits
      val callEdges = units.asScala.map(u => (u,Scene.v().getCallGraph.edgesOutOf(u)))
      val pt = Scene.v().getPointsToAnalysis
      val onResumeMethod_locals = locals.asScala.map{l => l -> pt.reachingObjects(l).possibleTypes()}.toMap
//      val r6ContainsTwo = ro.filter(v => v._1.getName == "$r6").head._2.asScala.filter(t => t.toString.contains("MyActivity"))
      println(onResumeMethod_locals.size)
      // target of getSharedPreferences
      val getSharedPref = Scene.v().getSootClass("android.content.ContextWrapper").getMethod("android.content.SharedPreferences getSharedPreferences(java.lang.String,int)")
      val getSharedPref_localMap = getSharedPref.getActiveBody.getLocals.asScala.map{l => l.getName->pt.reachingObjects(l).possibleTypes()}
      val fieldLoc_getSharedPref = getSharedPref_localMap.find(_._1.contains("tmplocal")).get._2
      val fieldLocSP_contains = fieldLoc_getSharedPref.asScala.filter(_.toString().contains("MyActivity$2"))
      //
      val ep = Scene.v().getEntryPoints.get(0)
      val ro2 = ep.getActiveBody.getLocals.asScala.map{l => l-> pt.reachingObjects(l)}.toMap
      val allocL = ep.getActiveBody.getLocals.asScala.find(l => l.toString().contains("alloc"))
      val posT = ro2(allocL.get).possibleTypes()
      val sharedPref = posT.asScala.filter(t => t.toString.contains("SharedPreferences"))
      println(getSharedPref_localMap.size)
//      val dummies = posT.asScala.filter(t => t.toString.contains("Dummy"))
//      val posTContainsTwo = posT.asScala.filter(t => t.toString.contains("MyActivity$2"))
//      val posTContainsOne = posT.asScala.filter(t => t.toString.contains("MyActivity$1"))
//      val ro2ContainsOne = ro2.filter{case (local, pts) => pts.possibleTypes().asScala.exists(t => t.toString.contains("MyActivity$1"))}
//      val ro2ContainsTwo = ro2.filter{case (local, pts) => pts.possibleTypes().asScala.exists(t => t.toString.contains("MyActivity$2"))}
//      println(posT.size)
//
//      val arrayList = Scene.v().getSootClass("java.util.ArrayList")
//      val iterMethod = arrayList.getMethod("java.util.Iterator iterator()")
//      val ro3 = iterMethod.getActiveBody.getLocals.asScala.map{l => l-> pt.reachingObjects(l)}.toMap
//      println(ro3.size)
      // dbg code end


      assert(targets.loc.nonEmpty)

      val query2 = Qry.makeReceiverNonNull(config.getSymbolicExecutor, w,
        "com.example.createdestroy.MyActivity",
        "void onResume()",
        BounderUtil.lineForRegex(".*query2.*".r,src), Some(".*iterator.*".r))
      val loc2 = query2.head.loc.asInstanceOf[AppLoc]
      val targets2: UnresolvedMethodTarget = w.makeInvokeTargets(loc2)
      assert(targets2.loc.nonEmpty)

      val query3 = Qry.makeReceiverNonNull(config.getSymbolicExecutor, w,
        "com.example.createdestroy.MyActivity",
        "void onPause()",
        BounderUtil.lineForRegex(".*query3.*".r,src), Some(".*iterator.*".r))
      val loc3 = query3.head.loc.asInstanceOf[AppLoc]
      val targets3: UnresolvedMethodTarget = w.makeInvokeTargets(loc3)
      assert(targets3.loc.size == 1)


      val query4 = Qry.makeReceiverNonNull(config.getSymbolicExecutor, w,
        "com.example.createdestroy.MyActivity",
        "void onResume()",
        BounderUtil.lineForRegex(".*query4.*".r,src), Some(".*iterator.*".r))
      val loc4 = query4.head.loc.asInstanceOf[AppLoc]
      val targets4: UnresolvedMethodTarget = w.makeInvokeTargets(loc4)
      assert(targets4.loc.size > 1)
      assert(targets4.loc.count(m => m.classType == "com.example.createdestroy.MyActivity$1") == 1)

      //TODO: following assertion should probably work if we can get any level of context sensitivity
      // leaked via Object.<init>
      //assert(!targets4.loc.exists(m => m.classType == "com.example.createdestroy.MyActivity$2"))

      val query5 = Qry.makeReceiverNonNull(config.getSymbolicExecutor, w,
        "com.example.createdestroy.MyActivity",
        "void onResume()",
        BounderUtil.lineForRegex(".*query5.*".r,src), Some(".*iterator.*".r))
      val loc5 = query5.head.loc.asInstanceOf[AppLoc]
      val targets5 = w.makeInvokeTargets(loc5)
      assert(targets5.loc.nonEmpty)
      println("TODO") // Why no shared pref from getSharedPreferences?
    }
    makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
  }
}
