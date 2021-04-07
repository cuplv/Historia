package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.lifestate.{ActivityLifecycle, FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.Qry
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, CallGraphSource, SparkCallGraph, SymbolicExecutorConfig, TransferFunctions}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.FixtureAnyFunSuite
import soot.SootMethod

class JimpleFlowdroidWrapperTest extends FixtureAnyFunSuite  {

  case class FixtureParam(cgSource: CallGraphSource)
  override def withFixture(test: OneArgTest) = {
    // Run all tests with both CHA call graph and SparkCallGraph
    withFixture(test.toNoArgTest(FixtureParam(SparkCallGraph)))
    withFixture(test.toNoArgTest(FixtureParam(CHACallGraph)))
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

}
