package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.symbolicexecutor.state.{PrettyPrinting, Qry}
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, FlowdroidCallGraph, SymbolicExecutor, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

class AntennaPod2856FixExperiment  extends AnyFunSuite{
  test("Prove location in stack trace is unreachable under a simple spec."){
    val apk = getClass.getResource("/Antennapod-fix-2856-app-free-debug.apk").getPath
    assert(apk != null)
    val w = new JimpleFlowdroidWrapper(apk, FlowdroidCallGraph)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set()))
    val config = SymbolicExecutorConfig(
      stepLimit = Some(10), w, resolver,transfer, printProgress = true)
    val query = Qry.makeCallinReturnNonNull(config, w,
      "de.danoeh.antennapod.fragment.ExternalPlayerFragment",
      "void updateUi(de.danoeh.antennapod.core.util.playback.Playable)",200,
      callinMatches = ".*getActivity.*".r)
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result = symbolicExecutor.executeBackward(query)
    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/antennapod_fix_2856.dot")
    PrettyPrinting.printWitnessTraces(result, outFile="/Users/shawnmeier/Desktop/antennapod_fix_2856.witnesses")
  }

}
