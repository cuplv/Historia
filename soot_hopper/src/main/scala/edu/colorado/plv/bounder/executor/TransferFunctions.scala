package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, FieldRef, IRWrapper, Invoke, InvokeCmd, Loc, LocalWrapper, NewCommand, SpecialInvoke, StaticInvoke, VirtualInvoke}
import edu.colorado.plv.bounder.state.{CallStackFrame, ClassVal, Equals, PureAtomicConstraint, StackVar, State}

class TransferFunctions[M,C](w:IRWrapper[M,C]) {
  def transfer(pre:State, target:Loc, source:Loc):Set[State] = (source,target,pre) match{
    case (source@AppLoc(_,_,false),CallinMethodReturn(fmwClazz, fmwName), State(stack, pure)) =>
      Set(State(CallStackFrame(target, Some(source.copy(isPre=true)),Map())::stack, pure)) //TODO: lifestate rule transfer
    case (CallinMethodReturn(_,_),CallinMethodInvoke(_,_),state) => Set(state)
    case (CallinMethodInvoke(_,_),loc@AppLoc(_,_,true), State(h::t,pure)) => {
      //TODO: parameter mapping
      Set(State(t,pure))
    }
    case (AppLoc(_,_,true),AppLoc(_,_,false), pre) => Set(pre)
    case (appLoc@AppLoc(c1,m1,false),AppLoc(c2,m2,true), prestate) if c1 == c2 && m1 == m2 =>
      cmdTransfer(w.cmdBeforeLocation(appLoc),prestate)
    case _ =>
      ???
  }
  def cmdTransfer(cmd:CmdWrapper[M,C], state: State):Set[State] = (cmd,state) match{
    case (AssignCmd(LocalWrapper(name), NewCommand(className),_,_), s@State(stack@f::tail,pureFormula)) =>
      f.locals.get(StackVar(name)) match{
        case Some(purevar) =>
          val constraint = PureAtomicConstraint(purevar, Equals, ClassVal(className))
          val newpf = pureFormula + constraint
          Set(State(stack, newpf))
        case None =>
          //TODO: Alias Case Split
          ???
      }
    case (AssignCmd(LocalWrapper(name), FieldRef(base, _, _, fieldName),_,_), s) =>
      ???
    case _ =>
      ???
  }
}
