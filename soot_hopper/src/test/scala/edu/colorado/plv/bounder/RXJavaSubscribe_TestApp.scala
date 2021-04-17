import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.LifeState.LSFalse
import edu.colorado.plv.bounder.lifestate.{ActivityLifecycle, FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{PrettyPrinting, Qry}
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, QueryFinished, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

class RXJavaSubscribe_TestApp extends AnyFunSuite{
  test("Prove location in stack trace is unreachable under a simple spec.") {
    val apk = getClass.getResource("/RXJavaSubscribe-fix-debug.apk").getPath
    assert(apk != null)
    val w = new JimpleFlowdroidWrapper(apk,CHACallGraph)
    val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod,soot.Unit](w,
      new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
        FragmentGetActivityNullSpec.getActivityNonNull,
        ActivityLifecycle.init_first_callback,
        RxJavaSpec.call,
//        RxJavaSpec.subscribeDoesNotReturnNull,
        RxJavaSpec.subscribeIsUnique
      )),cha)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(200), w,transfer,
      component = Some(List("example.com.rxjavasubscribebug.PlayerFragment.*")))
    val symbolicExecutor = config.getSymbolicExecutor

    val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
      "example.com.rxjavasubscribebug.PlayerFragment",
      "void lambda$onActivityCreated$1$PlayerFragment(java.lang.Object)",64,
      callinMatches = ".*getActivity.*".r)
    val result = symbolicExecutor.run(query).flatMap(a => a.terminals)
    assert(BounderUtil.interpretResult(result,QueryFinished) == Proven)
    assert(result.nonEmpty)
  }
}