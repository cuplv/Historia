package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, InternalMethodInvoke, InternalMethodReturn, Loc, SkippedInternalMethodInvoke, SkippedInternalMethodReturn}
import upickle.default.{macroRW, ReadWriter => RW}


//TODO: state should probably define all locals as pointing to pv, pv can then be constrained by pure expr
sealed case class CallStackFrame(exitLoc : Loc,
                                 retLoc: Option[AppLoc],
                                 locals: Map[StackVar, PureExpr]){
  assert(retLoc.forall {
    case AppLoc(method, line, true) => true
    case _ => false

  })
  // TODO: Loc type is probably too general, this assert could be removed
  assert(exitLoc match{
    case _:CallbackMethodReturn => true
    case _:CallinMethodReturn => true
    case _:InternalMethodReturn => true
    case _:GroupedCallinMethodReturn => true
    case _:SkippedInternalMethodReturn => true
    case v =>
      throw new IllegalStateException(s"$v is not a return location")
  })
  override def toString:String = {
    "[" + exitLoc.toString + " locals: " + locals.map(k => k._1.toString + ":" + k._2.toString).mkString(",") + "]"
  }
  def removeStackVar(v: StackVar):CallStackFrame = CallStackFrame(exitLoc, retLoc, locals.-(v))
}
object CallStackFrame{
  implicit val rw:RW[CallStackFrame] = macroRW
}
