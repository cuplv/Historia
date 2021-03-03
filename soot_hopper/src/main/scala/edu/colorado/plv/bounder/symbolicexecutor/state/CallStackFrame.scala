package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.ir.{CallbackMethodReturn, CallinMethodReturn, GroupedCallinMethodReturn, InternalMethodReturn, Loc}
import upickle.default.{macroRW, ReadWriter => RW}


//TODO: state should probably define all locals as pointing to pv, pv can then be constrained by pure expr
sealed case class CallStackFrame(methodLoc : Loc,
                          retLoc: Option[Loc],
                          locals: Map[StackVar, PureExpr]){
  // TODO: Loc type is probably too general, this assert could be removed
  assert(methodLoc match{
    case _:CallbackMethodReturn => true
    case _:CallinMethodReturn => true
    case _:InternalMethodReturn => true
    case _:GroupedCallinMethodReturn => true
    case v =>
      throw new IllegalStateException(s"$v is not a return location")
  })
  override def toString:String = {
    "[" + methodLoc.toString + " locals: " + locals.map(k => k._1.toString + ":" + k._2.toString).mkString(",") + "]"
  }
  def removeStackVar(v: StackVar):CallStackFrame = CallStackFrame(methodLoc, retLoc, locals.-(v))
}
object CallStackFrame{
  implicit val rw:RW[CallStackFrame] = macroRW
}
