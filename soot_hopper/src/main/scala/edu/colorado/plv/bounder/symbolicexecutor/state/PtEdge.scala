package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.ir.FieldRef

sealed trait HeapPtEdge

case class FieldPtEdge(p:PureVar, fieldName:String) extends HeapPtEdge{
  override def toString:String = s"${p.toString}.${fieldName}"
}
case class StaticPtEdge(clazz: String, fieldName:String) extends HeapPtEdge
//TODO: Array pt edge to represent array heap cells
