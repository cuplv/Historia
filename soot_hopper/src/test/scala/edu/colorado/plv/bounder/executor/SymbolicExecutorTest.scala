package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.BounderSetupApplication
import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, JimpleFlowdroidWrapper, JimpleMethodLoc, LineLoc, Loc, LocalWrapper, VirtualInvoke}
import edu.colorado.plv.bounder.state.{BottomQry, Equals, LocalPtEdge, NullVal, PathNode, PureAtomicConstraint, PureVar, Qry, StackVar}
import soot.{Local, SootMethod}
import soot.jimple.internal.JAssignStmt

class SymbolicExecutorTest extends org.scalatest.FunSuite {
  val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
  assert(test_interproc_1 != null)
  val w = new JimpleFlowdroidWrapper(test_interproc_1)
  val transfer = new TransferFunctions[SootMethod,soot.Unit](w)
  val a = new DefaultAppCodeResolver()
  val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)

  test("Symbolic Executor should prove an intraprocedural deref"){
    val query = Qry.makeReceiverNonNull(w,
      "com.example.test_interproc_1.MainActivity",
      "java.lang.String objectString()",21)
    // Call symbolic executor
    val config = SymbolicExecutorConfig(
      stepLimit = Some(8), w, resolver,transfer)
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    println(result.iterator.next)
    assert(result.size === 1)
    assert(result.iterator.next.qry.isInstanceOf[BottomQry])
  }
}
