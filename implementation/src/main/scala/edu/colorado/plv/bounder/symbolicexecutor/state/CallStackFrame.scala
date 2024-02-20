package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, InternalMethodInvoke, InternalMethodReturn, Loc, SkippedInternalMethodInvoke, SkippedInternalMethodReturn}
import edu.colorado.plv.bounder.lifestate.LifeState.SignatureMatcher
import upickle.default.{macroRW, ReadWriter => RW}

import scala.util.matching.Regex


//TODO: state should probably define all locals as pointing to pv, pv can then be constrained by pure expr
sealed trait CallStackFrame
object CallStackFrame{
  def apply(exitLoc : Loc,
            retLoc: Option[AppLoc],
            locals: Map[StackVar, PureExpr]) = MaterializedCallStackFrame(exitLoc, retLoc, locals)
  def unapply(frame:CallStackFrame):Option[(Loc, Option[AppLoc], Map[StackVar,PureExpr])] = frame match {
    case MaterializedCallStackFrame(exitLoc, retLoc, locals) => Some((exitLoc, retLoc, locals))
    case _ => ???
  }
  implicit val rw:RW[CallStackFrame] = RW.merge(MaterializedCallStackFrame.rw)
}
object MaterializedCallStackFrame{
  implicit val rw:RW[MaterializedCallStackFrame] = macroRW
}
case class FuzzyAppMethodStackFrame(signatureMatcher: SignatureMatcher) extends CallStackFrame{

}
case class MaterializedCallStackFrame(exitLoc : Loc,
                                 retLoc: Option[AppLoc],
                                 locals: Map[StackVar, PureExpr]) extends CallStackFrame{
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

  def removeStackVar(v: StackVar): MaterializedCallStackFrame = CallStackFrame(exitLoc, retLoc, locals.-(v))
}
