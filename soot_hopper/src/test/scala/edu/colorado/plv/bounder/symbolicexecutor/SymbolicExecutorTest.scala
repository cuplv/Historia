package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, Witnessed}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.LifeState.{And, LSSpec, NI}
import edu.colorado.plv.bounder.lifestate.{SpecSignatures, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, PathNode, PrettyPrinting, Qry}
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

class SymbolicExecutorTest extends AnyFunSuite {

  test("Symbolic Executor should prove an intraprocedural deref"){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, PatchedFlowdroidCallGraph)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set()))
    val config = SymbolicExecutorConfig(
      stepLimit = Some(8), w, resolver,transfer, printProgress = true)
    val query = Qry.makeReceiverNonNull(config, w,
      "com.example.test_interproc_1.MainActivity",
      "java.lang.String objectString()",21)
    // Call symbolic executor

    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    assert(result.size == 1)
    assert(result.iterator.next.qry.isInstanceOf[BottomQry])
    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/reftest.dot")
  }
  val resumePause = NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit)
  val initPause = NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_init_exit)
  val testSpec1 = LSSpec(And(resumePause,initPause),
    SpecSignatures.Activity_onPause_entry)
  val specForResumePause = new SpecSpace(Set(testSpec1))

  test("Symbolic Executor should prove an inter-callback deref"){
    println("======= Interproc ======")
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, PatchedFlowdroidCallGraph)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)

    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, specForResumePause)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(60), w,resolver,transfer, printProgress = true, z3Timeout = Some(30))
    val query = Qry.makeReceiverNonNull(config, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/foo.dot")
    PrettyPrinting.printWitnessTraces(result, outFile="/Users/shawnmeier/Desktop/foo.witnesses")
    assert(BounderUtil.interpretResult(result) == Proven)
  }
  test("Symbolic executor should witness onPause"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, PatchedFlowdroidCallGraph)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, specForResumePause)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(50), w,resolver,transfer, printProgress = true, z3Timeout = Some(30))
    val query = Qry.makeReach(config, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",25)
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/witnessOnPause.dot")
    assert(BounderUtil.interpretResult(result) == Witnessed)
  }
  test("Symbolic executor should witness onResume"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, PatchedFlowdroidCallGraph)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, specForResumePause)
    val config = SymbolicExecutorConfig(
      stepLimit = Some(50), w,resolver,transfer, printProgress = true, z3Timeout = Some(30))
    val query = Qry.makeReach(config, w,
      "com.example.test_interproc_2.MainActivity",
      "void onResume()",20)
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/witnessOnResume.dot")
    assert(BounderUtil.interpretResult(result) == Witnessed)
  }


}
