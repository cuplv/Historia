package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, InternalMethodInvoke, InternalMethodReturn, Loc, SkippedInternalMethodInvoke, SkippedInternalMethodReturn}
import edu.colorado.plv.bounder.symbolicexecutor.state.{State, StateFormula}

object MustExecutor {
  def pareseJavaSignature(sig: String): (String, List[String]) = {
    val (name, args) = sig.splitAt(sig.indexOf("("))
    (name, args.drop(1).dropRight(1).split(",").toList)
  }
  def execute(preConcState:StateFormula, loc:Loc, postAbsState:StateFormula):StateFormula= loc match {
    case AppLoc(method, line, isPre) =>
      ???
    case CallinMethodReturn(fmwClazz, fmwName) => ???
    case CallinMethodInvoke(fmwClazz, fmwName) => ???
    case GroupedCallinMethodInvoke(targetClasses, fmwName) => ???
    case GroupedCallinMethodReturn(targetClasses, fmwName) => ???
    case CallbackMethodInvoke(tgtClazz, fmwName, loc) =>
      val parsed = pareseJavaSignature(fmwName)
      println(loc)
      ???
    case CallbackMethodReturn(tgtClazz, fmwName, loc, line) => ???
    case InternalMethodInvoke(clazz, name, loc) => ???
    case InternalMethodReturn(clazz, name, loc) => ???
    case SkippedInternalMethodInvoke(clazz, name, loc) => ???
    case SkippedInternalMethodReturn(clazz, name, rel, loc) => ???
  }

}
