package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderSetupApplication
import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, JimpleFlowdroidWrapper, JimpleMethodLoc, LineLoc, Loc, LocalWrapper, VirtualInvoke}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, LSSpec, NI}
import edu.colorado.plv.bounder.lifestate.{SpecSpace, SpecSignatures}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, PathNode, PrettyPrinting, PureVar, Qry, StackVar}
import soot.SootMethod

class SymbolicExecutorTest extends org.scalatest.FunSuite {

  test("Symbolic Executor should prove an intraprocedural deref"){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set()))
    val config = SymbolicExecutorConfig(
      stepLimit = Some(8), w, resolver,transfer)
    val query = Qry.makeReceiverNonNull(config, w,
      "com.example.test_interproc_1.MainActivity",
      "java.lang.String objectString()",21)
    // Call symbolic executor

    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    assert(result.size === 1)
    assert(result.iterator.next.qry.isInstanceOf[BottomQry])
  }

  test("Symbolic Executor should prove an inter-callback deref"){
    //TODO: seems to prove too quickly?
    println("======= Interproc ======")
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)


    val testSpec0 = LSSpec(NI(SpecSignatures.Activity_init_exit, SpecSignatures.Activity_onPause_exit),
      SpecSignatures.Activity_onResume_entry)
    val resumePause = NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit)
    val testSpec1 = LSSpec(resumePause,
      SpecSignatures.Activity_onPause_entry) // TODO: fill in spec details for test
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set(testSpec1,testSpec0)))
    val config = SymbolicExecutorConfig(
      stepLimit = Some(23), w,resolver,transfer, printProgress = true, z3Timeout = Some(30))
    val query = Qry.makeReceiverNonNull(config, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    //TODO: deref not proven, figure out what is going on
    PrettyPrinting.printWitnessOrProof(result, "/Users/shawnmeier/Desktop/foo.dot")
  }
  test("Simplified inter-callback deref") {
    //TODO: define resume/pause app with TestIR to debug termination issue more easily
    ???
  }
}
