package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.LifeState.LSSpec
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{IPathNode, ReceiverNonNull}
import edu.colorado.plv.bounder.testutils.MkApk
import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

/**
 * Useful but very slow tests on the symbolic executor.
 * Note that hopefully these will eventually be faster. Then they should be moved to SymbolicExecutorTest.scala
 */
class SymbolicExecutorTestSlow extends AnyFunSuite{
  val cgMode = SparkCallGraph

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
        val specs:Set[LSSpec] = Set()
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
        BounderUtil.throwIfStackTrace(result)
        assert(BounderUtil.interpretResult(result,QueryFinished) == expectedResult)

      }

      makeApkWithSources(Map("MyActivity.java" -> src), MkApk.RXBase, test)
      println(s"test: $queryL done")
    }
  }
}
