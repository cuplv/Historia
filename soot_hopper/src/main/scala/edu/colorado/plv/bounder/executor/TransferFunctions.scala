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
    case (CallinMethodInvoke(_,_),loc@AppLoc(_,_), State(h::t,pure)) => {
      //TODO: parameter mapping
      Set(State(t,pure))
    }
    case _ =>
      ???
  }
}
