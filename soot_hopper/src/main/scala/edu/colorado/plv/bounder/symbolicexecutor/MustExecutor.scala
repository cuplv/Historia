package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, InternalMethodInvoke, InternalMethodReturn, Loc, SkippedInternalMethodInvoke, SkippedInternalMethodReturn}
import edu.colorado.plv.bounder.symbolicexecutor.state.{State, StateFormula}

object MustExecutor {
  def parseJavaSignature(sig: String): (String,String, List[String]) = {
    //TODO: crap code generated by GHA, find soot code that does this instead
    val (left, args) = sig.splitAt(sig.indexOf("("))
    val (retType,name) = left.splitAt(left.indexOf(" "))
    (retType, name.drop(1), args.drop(1).dropRight(1).split(",").toList)
  }
  def execute(preConcState:StateFormula, loc:Loc, postAbsState:StateFormula):StateFormula= loc match {
    case AppLoc(method, line, isPre) =>
      ???
    case CallinMethodReturn(sig) => ???
    case CallinMethodInvoke(sig) => ???
    case GroupedCallinMethodInvoke(targetClasses, fmwName) => ???
    case GroupedCallinMethodReturn(targetClasses, fmwName) => ???
    case CallbackMethodInvoke(sig, loc) =>
      val parsed = parseJavaSignature(sig.base)
      println(loc)
      ???
    case CallbackMethodReturn(sig, loc, line) => ???
    case InternalMethodInvoke(clazz, name, loc) => ???
    case InternalMethodReturn(clazz, name, loc) => ???
    case SkippedInternalMethodInvoke(clazz, name, loc) => ???
    case SkippedInternalMethodReturn(clazz, name, rel, loc) => ???
  }

}
