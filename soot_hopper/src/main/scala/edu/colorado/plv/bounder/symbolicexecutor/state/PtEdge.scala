package edu.colorado.plv.bounder.symbolicexecutor.state

import upickle.default.{ReadWriter => RW, macroRW}

sealed trait HeapPtEdge
object HeapPtEdge{
  implicit val rw:RW[HeapPtEdge] = RW.merge(FieldPtEdge.rw, StaticPtEdge.rw, ArrayPtEdge.rw)
}

case class FieldPtEdge(p:PureVar, fieldName:String) extends HeapPtEdge{
  override def toString:String = s"${p.toString}.${fieldName}"
}
object FieldPtEdge{
  implicit val rw:RW[FieldPtEdge] = macroRW
}
case class StaticPtEdge(clazz: String, fieldName:String) extends HeapPtEdge
//TODO: Array pt edge to represent array heap cells
object StaticPtEdge{
  implicit val rw:RW[StaticPtEdge] = macroRW
}

case class ArrayPtEdge(base:PureVar, index: PureExpr) extends HeapPtEdge
object ArrayPtEdge{
  implicit val rw:RW[ArrayPtEdge] = macroRW
}