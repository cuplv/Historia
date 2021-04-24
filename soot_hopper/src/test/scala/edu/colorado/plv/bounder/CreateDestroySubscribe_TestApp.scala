package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.{ActivityLifecycle, FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{PrettyPrinting, Qry}
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, ControlFlowResolver, DefaultAppCodeResolver, FlowdroidCallGraph, PatchedFlowdroidCallGraph, QueryFinished, SparkCallGraph, SymbolicExecutor, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.{Scene, SootMethod}

import scala.jdk.CollectionConverters.CollectionHasAsScala

class CreateDestroySubscribe_TestApp extends AnyFunSuite{
  val apk = getClass.getResource("/CreateDestroySubscribe-debug.apk").getPath
  assert(apk != null)
  val specSpace = new SpecSpace(Set(ActivityLifecycle.onPause_onlyafter_onResume_init,
    ActivityLifecycle.init_first_callback,
    RxJavaSpec.subscribeIsUnique,
    //    RxJavaSpec.subscribeDoesNotReturnNull,
    RxJavaSpec.call))
  val w = new JimpleFlowdroidWrapper(apk,CHACallGraph, specSpace.getSpecs)

  val transfer = (cha:ClassHierarchyConstraints) =>  {
    new TransferFunctions[SootMethod, soot.Unit](w, specSpace,cha)
  }
  val config = SymbolicExecutorConfig(
    stepLimit = 200, w,transfer,
    component = Some(List("com.example.createdestroy.MainActivity.*")))
  val symbolicExecutor = config.getSymbolicExecutor
  private val prettyPrinting = new PrettyPrinting()

  ignore("Prove location in stack trace is unreachable under a simple spec.") {
    val clazzes = Scene.v().getClasses.asScala.filter(c => c.toString.contains("MainActivity"))

    // No null pointer exception line 31
    val query = Qry.makeReceiverNonNull(symbolicExecutor, w,
      "com.example.createdestroy.MainActivity",
      "void lambda$onCreate$1$MainActivity(java.lang.Object)",31)
    val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
    prettyPrinting.dumpDebugInfo(result, "CreateDestroySubscribe_TestApp")
    assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)
    assert(result.nonEmpty)
  }
  ignore("Witness call reachability"){
    // Line 31 is reachable
    val query2 = Qry.makeReach(symbolicExecutor,w,
      "com.example.createdestroy.MainActivity",
      "void lambda$onCreate$1$MainActivity(java.lang.Object)",31)
    val result2 = symbolicExecutor.run(query2).flatMap(a => a.terminals)
    prettyPrinting.dumpDebugInfo(result2, "CreateDestroySubscribe_TestApp_reach")
    assert(result2.nonEmpty)
    assert(BounderUtil.interpretResult(result2,QueryFinished) == Witnessed)
  }

}