import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.{ActivityLifecycle, FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{PrettyPrinting, Qry}
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

class RXJavaSubscribe_TestApp extends AnyFunSuite{
  // TODO: !!!!IMPORTANT!!!! current transfer functions are imprecise with respect to IF
  // if this example works before fixing precision issue, there is likely unsoundness somewhere
  test("Prove location in stack trace is unreachable under a simple spec.") {
    val apk = getClass.getResource("/RXJavaSubscribe-fix-debug.apk").getPath
    assert(apk != null)
    val w = new JimpleFlowdroidWrapper(apk,CHACallGraph)
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w,
      new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
        ActivityLifecycle.init_first_callback,
        RxJavaSpec.call)))
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
    assert(BounderUtil.interpretResult(result) == Proven)
  }

}