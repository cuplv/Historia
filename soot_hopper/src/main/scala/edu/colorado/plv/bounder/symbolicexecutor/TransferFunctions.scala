package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, FieldRef, IRWrapper, Invoke, InvokeCmd, LVal, Loc, LocalWrapper, NewCommand, SpecialInvoke, StaticInvoke, ThisWrapper, VirtualInvoke}
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallStackFrame, ClassVal, Equals, FieldPtEdge, PureConstraint, PureVar, StackVar, State, SubClassOf, TypeConstraint}

class TransferFunctions[M,C](w:IRWrapper[M,C]) {
  def transfer(pre:State, target:Loc, source:Loc):Set[State] = (source,target,pre) match{
    case (source@AppLoc(_,_,false),CallinMethodReturn(fmwClazz, fmwName), State(stack,heap, pure)) =>
      Set(State(CallStackFrame(target, Some(source.copy(isPre=true)),Map())::stack,heap, pure)) //TODO: lifestate rule transfer
    case (CallinMethodReturn(_,_),CallinMethodInvoke(_,_),state) => Set(state)
    case (CallinMethodInvoke(_,_),loc@AppLoc(_,_,true), s@State(h::t,_,_)) => {
      //TODO: parameter mapping
      Set(s.copy(callStack = t))
    }
    case (AppLoc(_,_,true),AppLoc(_,_,false), pre) => Set(pre)
    case (appLoc@AppLoc(c1,m1,false),AppLoc(c2,m2,true), prestate) if c1 == c2 && m1 == m2 =>
      cmdTransfer(w.cmdBeforeLocation(appLoc),prestate)
    case (AppLoc(_,_,true), CallbackMethodInvoke(fc1, fn1, l1), State(CallStackFrame(CallbackMethodReturn(fc2, fn2, l2), None, locals)::s, heap, pure)) => {
      // If call doesn't match return on stack, return bottom
      if (fc1 != fc2 || fn1 != fn2 || l1 != l2) Set() else {
        Set(State(s,heap, pure))
      }
    }
    case _ => ???
  }
  def cmdTransfer(cmd:CmdWrapper[M,C], state: State):Set[State] = (cmd,state) match{
    case (AssignCmd(LocalWrapper(name,vartype), NewCommand(className),_,_),
        s@State(stack@f::_,heap,pureFormula)) =>
      f.locals.get(StackVar(name,vartype)) match{
        case Some(purevar: PureVar) =>
          val constraint = PureConstraint(purevar, Equals, ClassVal(className))
          val newpf = pureFormula + constraint
          // TODO: check no fields are required to be non null
          Set(State(stack,heap, newpf))
        case None =>
          //TODO: Alias Case Split
          ???
        case _ => throw new IllegalStateException("Assign object to primitive")
      }
    case (AssignCmd(target, FieldRef(base, containsType, declType, name),_,_), s) =>{
      if(s.isDefined(target)) {
        val (tgtval, s1) = s.getOrDefine(target)
        if(s.isDefined(base)){
          ??? // no alias between vars possible
        }else{
          // Case split between aliased or not aliased
          val possibleBaseAliases: Set[PureVar] = s.pureVars()
            .filter(!s.isNull(_))
            .filter(a => ???) //TODO: use canAlias from IR
          //TODO: swap pure vars types
          val aliasSets: Set[State] = possibleBaseAliases.map(pv => ???)
          val (basePure, s2) = s1.getOrDefine(base)
          if(! basePure.isInstanceOf[PureVar]) throw new IllegalStateException(s"Assign to non object purevar.")
          aliasSets + s2.copy(heapConstraints = s2.heapConstraints +
            (FieldPtEdge(basePure.asInstanceOf[PureVar],name,containsType,declType)-> tgtval)).clearLVal(target)
        }
      }else{
        Set(s) // No change to state if assignment doesn't affect anything in current state
      }
    }
    case (AssignCmd(target:LocalWrapper, LocalWrapper(name, localType),_,_),s@State(f::t,_,_)) => {
      f.locals.get(StackVar(target.name, target.localType)) match {
        case Some(v) =>
          val (pval,s1) = s.getOrDefine(target)
          val s2 = s1.clearLVal(target)
          Set(s2.copy(callStack = f.copy(locals=f.locals + (StackVar(name,localType) -> pval))::t))
        case None => Set(s)
      }
    }
    case (AssignCmd(lw: LocalWrapper, ThisWrapper(thisTypename),a,b), s) =>
      cmdTransfer(AssignCmd(lw, LocalWrapper("this", thisTypename),a,b),s)
    case _ =>
      ???
  }
  def canAlias(tc:TypeConstraint, target: LVal):Boolean = (tc,target) match{
    case (SubClassOf(pureTypeName),LocalWrapper(_,lvalType)) => w.canAlias(pureTypeName, lvalType)
    case _ =>
      ???
  }
}
