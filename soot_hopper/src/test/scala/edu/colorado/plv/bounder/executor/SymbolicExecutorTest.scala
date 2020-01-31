package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.SetupApplication
import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, JimpleMethodLoc, JimpleWrapper, LineLoc, Loc, LocalWrapper, VirtualInvoke}
import edu.colorado.plv.bounder.state.{Equals, LocalPtEdge, NullVal, PureAtomicConstraint, PureVar, Qry, StackVar}
import soot.{Local, SootMethod}
import soot.jimple.internal.JAssignStmt

class SymbolicExecutorTest extends org.scalatest.FunSuite {
  val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
  assert(test_interproc_1 != null)
  val w = new JimpleWrapper(test_interproc_1)
  test("Symbolic Executor should prove an intraprocedural deref"){
    val locs = w.findLineInMethod(
      "com.example.test_interproc_1.MainActivity", "java.lang.String objectString()",21)

    val derefLocs: Iterable[AppLoc] = locs.filter(pred = a => {
      w.cmdAfterLocation(a).isInstanceOf[AssignCmd[SootMethod, soot.Unit]]
      //      a.u.isInstanceOf[JAssignStmt]
    })
    assert(derefLocs.size === 1)
    // Get location of query
    val derefLoc: AppLoc = derefLocs.iterator.next
    // Get name of variable that should not be null
    val varname = w.cmdAfterLocation(derefLoc) match {
      case a@AssignCmd(_, VirtualInvoke(LocalWrapper(name),_,_,_,_), _, _) => name
      case _ => ???
    }

    val pureVar = PureVar("")
    val query = Qry.make(derefLoc, Map((StackVar(varname),pureVar)),
      Set(PureAtomicConstraint(pureVar, Equals, NullVal)))

    val a = new DefaultAppCodeResolver()
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w)
    // Call symbolic executor
    val config = SymbolicExecutorConfig(
      stepLimit = 5, w, new ControlFlowResolver[SootMethod,soot.Unit](w,a),transfer)
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result = symbolicExecutor.executeBackwardRec(query, config.stepLimit)
//    assert(!result.isDefined)
    println()

  }
}
