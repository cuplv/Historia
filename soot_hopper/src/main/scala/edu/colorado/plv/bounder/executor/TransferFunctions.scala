package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, FieldRef, IRWrapper, Invoke, InvokeCmd, LVal, Loc, LocalWrapper, NewCommand, SpecialInvoke, StaticInvoke, VirtualInvoke}
import edu.colorado.plv.bounder.state.{CallStackFrame, ClassVal, Equals, PureAtomicConstraint, PureVar, StackVar, State, SubClassOf, TypeConstraint}

class TransferFunctions[M,C](w:IRWrapper[M,C]) {
  def transfer(pre:State, target:Loc, source:Loc):Set[State] = (source,target,pre) match{
    case (source@AppLoc(_,_,false),CallinMethodReturn(fmwClazz, fmwName), State(stack,heap,tc, pure)) =>
      Set(State(CallStackFrame(target, Some(source.copy(isPre=true)),Map())::stack,heap,tc, pure)) //TODO: lifestate rule transfer
    case (CallinMethodReturn(_,_),CallinMethodInvoke(_,_),state) => Set(state)
    case (CallinMethodInvoke(_,_),loc@AppLoc(_,_,true), s@State(h::t,_,_,_)) => {
      //TODO: parameter mapping
      Set(s.copy(callStack = t))
    }
    case (AppLoc(_,_,true),AppLoc(_,_,false), pre) => Set(pre)
    case (appLoc@AppLoc(c1,m1,false),AppLoc(c2,m2,true), prestate) if c1 == c2 && m1 == m2 =>
      cmdTransfer(w.cmdBeforeLocation(appLoc),prestate)
    case _ =>
      ???
  }
  def cmdTransfer(cmd:CmdWrapper[M,C], state: State):Set[State] = (cmd,state) match{
    case (AssignCmd(LocalWrapper(name,vartype), NewCommand(className),_,_),
        s@State(stack@f::tail,heap,typeConstraints,pureFormula)) =>
      f.locals.get(StackVar(name,vartype)) match{
        case Some(purevar: PureVar) =>
          val constraint = PureAtomicConstraint(purevar, Equals, ClassVal(className))
          val newpf = pureFormula + constraint
          // TODO: check no fields are required to be non null
          Set(State(stack,heap,typeConstraints, newpf))
        case None =>
          //TODO: Alias Case Split
          ???
        case _ => throw new IllegalStateException("Assign object to primitive")
      }
    case (AssignCmd(target, fr@FieldRef(base, containsType, declType, name),_,_), s) =>{
      if(s.isDefined(target)) {
        val (tgtval, s1) = s.getOrDefine(target)
        if(s.isDefined(base)){
          ??? // no alias between vars possible
        }else{
          // Case split between aliased or not aliased
          val possibleBaseAliases: Set[PureVar] = s.pureVars()
            .filter(s.isNull)
            .filter(a => canAlias(s.typeConstraints(a), base))
          //TODO: swap pure vars types
          val aliasSets: Set[State] = possibleBaseAliases.map(pv => ???)
          aliasSets + s1.copy(heapConstraints = s.heapConstraints + ???)
        }
      }else{
        Set(s) // No change to state if assignment doesn't affect anything in current state
      }
    }
    case _ =>
      ???
  }
  def canAlias(tc:TypeConstraint, target: LVal):Boolean = (tc,target) match{
    case (SubClassOf(pureTypeName),LocalWrapper(_,lvalType)) => w.canAlias(pureTypeName, lvalType)
    case _ =>
      ???
  }
}
