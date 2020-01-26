package edu.colorado.plv.bounder.state

object Qry {
  private var qryIdCounter = 0
  private def getFreshQryId = { qryIdCounter += 1; qryIdCounter }


}
//TODO: add extra constraints into query later
//heapConstraints : Set[HeapPtEdge],
//pureConstraints : Set[PureConstraint],
case class Qry(  callStack : CallStack)