package edu.colorado.plv.bounder.executor

import java.lang.annotation.Target

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, IRWrapper, Invoke, InvokeCmd, Loc, LocalWrapper, SpecialInvoke, StaticInvoke, VirtualInvoke}
import edu.colorado.plv.bounder.state.{BottomQry, CallStackFrame, Qry, SomeQry, State, Val}
import soot.jimple.internal.JInvokeStmt

class TransferFunctions[M,C](w:IRWrapper[M,C]) {
  def transfer(pre:State, target:Loc, source:Loc):Set[State] = (source,target,pre) match{
    case (_,CallinMethodReturn(fmwClazz, fmwName), State(stack, pure)) =>
      Set(State(CallStackFrame(target, Some(source),Map())::stack, pure)) //TODO: lifestate rule transfer
    case (CallinMethodReturn(_,_),CallinMethodInvoke(_,_),state) => Set(state)
    case (CallinMethodInvoke(_,_),targetLoc@AppLoc(_,_), State(h::t,pure)) => {
      val cmd = w.cmdAfterLocation(targetLoc)
      Set(State(t,pure))
    }
    case _ =>
      ???
  }

  //  def targetSelector(inv: JInvokeStmt):Set[Loc] = ???
//
//  def transfer(post:Qry, cmd: CmdWrapper[M,C], methodRef: Option[MethodReference]): Option[State] = post match{
//    case SomeQry(stack, loc) => cmd match{
//      case InvokeCmd(method, loc, w) => transferReturn(post, method,methodRef.get, None)
//      case AssignCmd(target, source, loc, wrapper) => ???
//      case a =>
//        ???
//    }
//    case BottomQry(loc) => None
//  }
//
//  /**
//   *
//   * @param post - State after method invocation
//   * @param ref - method being returned from
//   * @param result - Defined if the result of the function is stored to a local
//   * @return
//   */
//  def transferReturn(post:Qry,inv:Invoke[M,C], ref:MethodReference, result: Option[LocalWrapper]): Option[State] =  ref match {
//      case CallinMethod(clazz, methodName) => invokeCallin(post, ref, result)
//      case CallbackMethod(clazz, methodName, loc) =>
//        ???
//      case InternalMethod(clazz, methodName, loc) =>
//        ???
//  }
//
//  // Return from an application method
//  def returnApp(post:Qry, resolvedMethod: Target, cmd:Invoke[M,C]):Option[State] =
//    ???
//
//  def invokeApp(post:Qry):Option[State] =
//    ???
//
//  // TODO: possibly split into call/return
//  def invokeCallin(post:Qry, cmd:MethodReference, result: Option[LocalWrapper]): Option[State] = post match{
//    case SomeQry(state, loc) => Some(state) // TODO: implement lifestate matching rule here
//    case _ =>
//      ???
//  }

}
