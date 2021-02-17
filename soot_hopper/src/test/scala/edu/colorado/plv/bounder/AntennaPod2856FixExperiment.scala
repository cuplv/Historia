package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{PrettyPrinting, Qry}
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, ControlFlowResolver, DefaultAppCodeResolver, FlowdroidCallGraph, PatchedFlowdroidCallGraph, SparkCallGraph, SymbolicExecutor, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

class AntennaPod2856FixExperiment  extends AnyFunSuite{
  private val apk = getClass.getResource("/Antennapod-fix-2856-app-free-debug.apk").getPath
  assert(apk != null)
  private val w = new JimpleFlowdroidWrapper(apk,CHACallGraph)
  private val transfer = (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod,soot.Unit](w,
    new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
      FragmentGetActivityNullSpec.getActivityNonNull,
      RxJavaSpec.call,
      RxJavaSpec.subscribeDoesNotReturnNull,
      RxJavaSpec.subscribeIsUniqueAndNonNull
    )),cha)

  test("Prove updateUI is not reachable where getActivity returns null under a simple spec.") {
    val config = SymbolicExecutorConfig(
      stepLimit = Some(300), w,transfer,
      component = Some(List("de\\.danoeh\\.antennapod\\.fragment\\.ExternalPlayerFragment.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
      "de.danoeh.antennapod.fragment.ExternalPlayerFragment",
      "void updateUi(de.danoeh.antennapod.core.util.playback.Playable)",200,
      callinMatches = ".*getActivity.*".r)
    val result = symbolicExecutor.executeBackward(query)
    PrettyPrinting.dumpDebugInfo(result, "antennapod_fix_2856")
    assert(BounderUtil.interpretResult(result) == Proven)
  }
  ignore("updateUI is reachable under a simple spec.") {
    // TODO: currently timing out, should witness
    val config = SymbolicExecutorConfig(
      stepLimit = Some(300), w,transfer,
      component = Some(List("de\\.danoeh\\.antennapod\\.fragment\\.ExternalPlayerFragment.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeReach(symbolicExecutor, w,
      "de.danoeh.antennapod.fragment.ExternalPlayerFragment",
      "void updateUi(de.danoeh.antennapod.core.util.playback.Playable)",200)
    val result = symbolicExecutor.executeBackward(query)
    PrettyPrinting.dumpDebugInfo(result, "antennapod_witness1_2856")
    assert(BounderUtil.interpretResult(result) == Witnessed)
  }
  ignore("GetActivity may return null in certain locations"){
    // TODO: currently timing out, should witness
    val config = SymbolicExecutorConfig(
      stepLimit = Some(50), w,transfer,
      component = Some(List("de\\.danoeh\\.antennapod\\.fragment\\.CompletedDownloadsFragment.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
      "de.danoeh.antennapod.fragment.CompletedDownloadsFragment",
      "void onViewCreated(android.view.View,android.os.Bundle)",112,
      callinMatches = ".*getActivity.*".r)
    val result = symbolicExecutor.executeBackward(query)

    PrettyPrinting.dumpDebugInfo(result, "antennapod_witness2_2856")
    assert(BounderUtil.interpretResult(result) == Witnessed)
  }

}
