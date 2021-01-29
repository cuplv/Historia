import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.Witnessed
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{PrettyPrinting, Qry}
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, ControlFlowResolver, DefaultAppCodeResolver, FlowdroidCallGraph, PatchedFlowdroidCallGraph, SparkCallGraph, SymbolicExecutor, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.{Scene, SootMethod}

import scala.jdk.CollectionConverters.CollectionHasAsScala

class RXJavaSubscribe_TestApp extends AnyFunSuite{
  test("Prove location in stack trace is unreachable under a simple spec.") {
    val apk = getClass.getResource("/RXJavaSubscribe-fix-debug.apk").getPath
    assert(apk != null)
    val w = new JimpleFlowdroidWrapper(apk,CHACallGraph)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    //    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w,
      new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,RxJavaSpec.call)))
    val config = SymbolicExecutorConfig(
      stepLimit = Some(120), w,transfer, printProgress = true,
      component = Some(List("example.com.rxjavasubscribebug.PlayerFragment.*")))
    val symbolicExecutor = config.getSymbolicExecutor

    val query = Qry.makeCallinReturnNonNull(symbolicExecutor, w,
      "example.com.rxjavasubscribebug.PlayerFragment",
      "void lambda$onActivityCreated$1$PlayerFragment(java.lang.Object)",64,
      callinMatches = ".*getActivity.*".r)
    val result = symbolicExecutor.executeBackward(query)
    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/RXJavaSubscribe_Fix_TestApp.dot")
    PrettyPrinting.printWitnessTraces(result, outFile="/Users/shawnmeier/Desktop/RXJavaSubscribe_Fix_TestApp.witnesses")
    assert(BounderUtil.interpretResult(result) == Witnessed)
  }

}