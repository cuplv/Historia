package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.ir.{Loc, MethodLoc}


//TODO: state should probably define all locals as pointing to pv, pv can then be constrained by pure expr
sealed case class CallStackFrame(methodLoc : Loc,
                          retLoc: Option[Loc],
                          locals: Map[StackVar, PureExpr]){
  override def toString:String = {
    "[" + methodLoc.toString + " locals: " + locals.map(k => k._1.toString + ":" + k._2.toString).mkString(",") + "]"
  }
  def removeStackVar(v: StackVar):CallStackFrame = CallStackFrame(methodLoc, retLoc, locals.-(v))
}
