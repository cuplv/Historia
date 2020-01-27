package edu.colorado.plv.bounder.state

import edu.colorado.plv.bounder.ir.{LineLoc, Loc, MethodWrapper}
import soot.SootMethod

object Qry {
  private var qryIdCounter = 0
  private def getFreshQryId = { qryIdCounter += 1; qryIdCounter }
  def make(loc:Loc, assertions : Set[PtEdge]):Qry = {
    val localAssertions = assertions.flatMap(a => a match {
      case lpt@LocalPtEdge(_,_) => Some(lpt)
      case _ => None
    })
    SomeQry(CallStack(List(CallStackFrame(loc.method,localAssertions))),loc)
  }

}
//TODO: add extra constraints into query later
//heapConstraints : Set[HeapPtEdge],
//pureConstraints : Set[PureConstraint],
sealed trait Qry {
  def loc: Loc
}
//Query consists of a location and an abstract state defined at the program point just before that location.
case class SomeQry(callStack : CallStack, loc: Loc) extends Qry
case class BottomQry(loc:Loc) extends Qry // Infeasible precondition, path refuted