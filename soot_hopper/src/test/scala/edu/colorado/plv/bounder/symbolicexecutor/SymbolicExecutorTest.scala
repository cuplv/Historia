package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.{BounderSetupApplication, TestSignatures}
import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, JimpleFlowdroidWrapper, JimpleMethodLoc, LineLoc, Loc, LocalWrapper, VirtualInvoke}
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, NI}
import edu.colorado.plv.bounder.lifestate.SpecSpace
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
    println(result.iterator.next)
    assert(result.size === 1)
    assert(result.iterator.next.qry.isInstanceOf[BottomQry])
  }

  test("Symbolic Executor should prove an inter-callback deref"){
    println("======= Interproc ======")
    val test_interproc_1 = getClass.getResource("/test_interproc_2.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val testSpec = LSSpec(NI(TestSignatures.Activity_onResume_entry, TestSignatures.Activity_onPause_exit),
      TestSignatures.Activity_onPause_entry) // TODO: fill in spec details for test
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set(testSpec)))
    val config = SymbolicExecutorConfig(
      stepLimit = Some(30), w,resolver,transfer)
    val query = Qry.makeReceiverNonNull(config, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    //TODO: deref not proven, figure out what is going on
    PrettyPrinting.dotWitTree(result, "/Users/shawnmeier/Desktop/foo.dot")
  }
  test("Simplified inter-callback deref") {
    //TODO: define resume/pause app with TestIR to debug termination issue more easily
    ???
  }
}
