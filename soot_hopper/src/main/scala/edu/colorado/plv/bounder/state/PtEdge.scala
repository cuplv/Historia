package edu.colorado.plv.bounder.state

sealed trait PtEdge
case class LocalPtEdge(src : StackVar, snk:Val) extends PtEdge