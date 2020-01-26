package edu.colorado.plv.bounder.state

sealed trait PtEdge {

}
case class LocalPtEdge() extends PtEdge

sealed trait Val {

}
case class ObjVar()