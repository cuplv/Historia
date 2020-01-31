package edu.colorado.plv.bounder.state

import edu.colorado.plv.bounder.ir.{AppLoc, LineLoc, Loc, MethodWrapper}
import soot.SootMethod

object Qry {
  private var qryIdCounter = 0
  private def getFreshQryId = { qryIdCounter += 1; qryIdCounter }
  def make(loc:AppLoc, locals : Map[StackVar, Val], pureFormula: Set[PureConstraint]):Qry = {
//    val localAssertions = locals.flatMap(a => a match {
//      case lpt@LocalPtEdge(_,_) => Some(lpt)
//      case _ => None
//    })
    // Note: no return location for arbitrary query
    val queryStack = List(CallStackFrame(loc,None, locals))
    SomeQry(State(queryStack, pureFormula),loc)
  }

}
//TODO: add extra constraints into query later
//heapConstraints : Set[HeapPtEdge],
//pureConstraints : Set[PureConstraint],
sealed trait Qry {
  def loc: Loc
}
//Query consists of a location and an abstract state defined at the program point just before that location.
case class SomeQry(state:State, loc: Loc) extends Qry {
  override def toString:String = loc.toString + "  " + state.toString
}
// Infeasible precondition, path refuted
case class BottomQry(loc:Loc) extends Qry {
  override def toString:String = "refuted"
}