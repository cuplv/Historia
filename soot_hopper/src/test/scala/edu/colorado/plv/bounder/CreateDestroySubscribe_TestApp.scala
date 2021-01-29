package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, ResumePauseSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{PrettyPrinting, Qry}
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, ControlFlowResolver, DefaultAppCodeResolver, FlowdroidCallGraph, PatchedFlowdroidCallGraph, SparkCallGraph, SymbolicExecutor, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.{Scene, SootMethod}

import scala.jdk.CollectionConverters.CollectionHasAsScala

class CreateDestroySubscribe_TestApp extends AnyFunSuite{
  test("Prove location in stack trace is unreachable under a simple spec.") {
    val apk = getClass.getResource("/CreateDestroySubscribe-debug.apk").getPath
    assert(apk != null)
    val w = new JimpleFlowdroidWrapper(apk,CHACallGraph)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    //    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w,
      new SpecSpace(Set(ResumePauseSpec.resumePauseInit,RxJavaSpec.call)))
    val config = SymbolicExecutorConfig(
      stepLimit = Some(60), w,transfer, printProgress = true,
      component = Some(List("com.example.createdestroy.MainActivity.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val clazzes = Scene.v().getClasses.asScala.filter(c => c.toString.contains("MainActivity"))
    val query = Qry.makeReceiverNonNull(symbolicExecutor, w,
      "com.example.createdestroy.MainActivity",
      "void lambda$onCreate$1$MainActivity(java.lang.Object)",31)
    val result = symbolicExecutor.executeBackward(query)
    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/CreateDestroySubscribe_TestApp.dot")
    PrettyPrinting.printWitnessTraces(result, outFile="/Users/shawnmeier/Desktop/CreateDestroySubscribe_TestApp.witnesses")
    assert(BounderUtil.interpretResult(result) == Proven)
  }

}