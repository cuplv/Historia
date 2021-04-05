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
  private val apkFix = getClass.getResource("/Antennapod-fix-2856-app-free-debug.apk").getPath
  assert(apkFix != null)
  private val apkBug = getClass.getResource("/Antennapod-bug-2856-free-debug.apk").getPath
  assert(apkBug != null)
  private val transfer = (w:JimpleFlowdroidWrapper) =>
    (cha:ClassHierarchyConstraints) => new TransferFunctions[SootMethod,soot.Unit](w,
    new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
      FragmentGetActivityNullSpec.getActivityNonNull,
      RxJavaSpec.call,
      RxJavaSpec.subscribeDoesNotReturnNull,
      RxJavaSpec.subscribeIsUniqueAndNonNull
    )),cha)
  private val prettyPrinting = new PrettyPrinting()

  ignore("Fix: Prove updateUI is not reachable where getActivity returns null under a simple spec.") {
    //TODO: currently timing out
    val w = new JimpleFlowdroidWrapper(apkFix,CHACallGraph)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(400), w,transfer(w),
      component = Some(List("de\\.danoeh\\.antennapod\\.fragment\\.ExternalPlayerFragment.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
      "de.danoeh.antennapod.fragment.ExternalPlayerFragment",
      "void updateUi(de.danoeh.antennapod.core.util.playback.Playable)",200,
      callinMatches = ".*getActivity.*".r)
    val result = symbolicExecutor.run(query).flatMap(a => a._2)
    prettyPrinting.dumpDebugInfo(result, "antennapod_fix_2856")
    assert(BounderUtil.interpretResult(result) == Proven)
  }

  ignore("Bug: Fails to prove updateUI is not reachable where getActivity returns null with same spec.") {
    // TODO: currently timing out
    val w = new JimpleFlowdroidWrapper(apkBug,CHACallGraph)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(400), w,transfer(w),
      component = Some(List("de\\.danoeh\\.antennapod\\.fragment\\.ExternalPlayerFragment.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
      "de.danoeh.antennapod.fragment.ExternalPlayerFragment",
      "void updateUi(de.danoeh.antennapod.core.util.playback.Playable)",193,
      callinMatches = ".*getActivity.*".r)
    val result = symbolicExecutor.run(query).flatMap(a => a._2)
    prettyPrinting.dumpDebugInfo(result, "antennapod_bug_2856")
    assert(BounderUtil.interpretResult(result) == Witnessed)
  }
  ignore("Fix: updateUI is reachable under a simple spec.") {
    // TODO: currently timing out, should witness
    val w = new JimpleFlowdroidWrapper(apkFix,CHACallGraph)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(400), w,transfer(w),
      component = Some(List("de\\.danoeh\\.antennapod\\.fragment\\.ExternalPlayerFragment.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeReach(symbolicExecutor, w,
      "de.danoeh.antennapod.fragment.ExternalPlayerFragment",
      "void updateUi(de.danoeh.antennapod.core.util.playback.Playable)",200)
    val result = symbolicExecutor.run(query).flatMap(a => a._2)
    prettyPrinting.dumpDebugInfo(result, "antennapod_witness1_2856")
    assert(BounderUtil.interpretResult(result) == Witnessed)
  }
  ignore("Fix: GetActivity may return null in certain locations"){
    // TODO: currently timing out, should witness
    val w = new JimpleFlowdroidWrapper(apkFix,CHACallGraph)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(50), w,transfer(w),
      component = Some(List("de\\.danoeh\\.antennapod\\.fragment\\.CompletedDownloadsFragment.*")))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeCallinReturnNull(symbolicExecutor, w,
      "de.danoeh.antennapod.fragment.CompletedDownloadsFragment",
      "void onViewCreated(android.view.View,android.os.Bundle)",112,
      callinMatches = ".*getActivity.*".r)
    val result = symbolicExecutor.run(query).flatMap(a => a._2)

    prettyPrinting.dumpDebugInfo(result, "antennapod_witness2_2856")
    assert(BounderUtil.interpretResult(result) == Witnessed)
  }

}
