package edu.colorado.plv.bounder.state

import edu.colorado.plv.bounder.ir.FieldRef

sealed trait HeapPtEdge
case class FieldPtEdge(p:PureVar, fieldName:String, containsType:String, declType:String) extends HeapPtEdge
//Note: these can contain
//case class LocalPtEdge(src : StackVar, snk:Val) extends PtEdge

