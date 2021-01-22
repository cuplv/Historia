package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.symbolicexecutor.state.Qry
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

class AntennaPod2856FixExperiment  extends AnyFunSuite{
  test("Prove location in stack trace is unreachable under a simple spec."){
    val apk = getClass.getResource("/Antennapod-fix-2856-app-free-debug.apk").getPath
    assert(apk != null)
    val w = new JimpleFlowdroidWrapper(apk)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set()))
    val config = SymbolicExecutorConfig(
      stepLimit = Some(40), w, resolver,transfer)
    val query = Qry.makeCallinReturnNonNull(config, w,
      "de.danoeh.antennapod.fragment.ExternalPlayerFragment",
      "void updateUi(de.danoeh.antennapod.core.util.playback.Playable)",200,
      callinMatches = ".*getActivity.*".r)
    println(query)
  }

}
