package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, FieldRef, IRWrapper, LVal, Loc, LocalWrapper, NewCommand, ReturnCmd, SpecialInvoke, StaticInvoke, ThisWrapper, VirtualInvoke}
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallStackFrame, ClassType, Equals, FieldPtEdge, NotEquals, NullVal, PureConstraint, PureVar, StackVar, State, SubclassOf, TypeComp, TypeConstraint, Val}

class TransferFunctions[M,C](w:IRWrapper[M,C]) {
  def transfer(pre:State, target:Loc, source:Loc):Set[State] = (source,target,pre) match{
    case (source@AppLoc(_,_,false),CallinMethodReturn(fmwClazz, fmwName), State(stack,heap, pure, reg)) =>
      Set(State(CallStackFrame(target, Some(source.copy(isPre=true)),Map())::stack,heap, pure, reg)) //TODO: lifestate rule transfer
    case (CallinMethodReturn(_,_),CallinMethodInvoke(_,_),state) => Set(state)
    case (CallinMethodInvoke(_,_),loc@AppLoc(_,_,true), s@State(h::t,_,_,_)) => {
      //TODO: parameter mapping
      Set(s.copy(callStack = t))
    }
    case (AppLoc(_,_,true),AppLoc(_,_,false), pre) => Set(pre)
    case (appLoc@AppLoc(c1,m1,false),AppLoc(c2,m2,true), prestate) if c1 == c2 && m1 == m2 =>
      cmdTransfer(w.cmdBeforeLocation(appLoc),prestate)
    case (AppLoc(_,m,true), CallbackMethodInvoke(fc1, fn1, l1), State(CallStackFrame(CallbackMethodReturn(fc2, fn2, l2), None, locals)::s, heap, pure, reg)) => {
      // If call doesn't match return on stack, return bottom
      val thisEdge = locals.find(l => l._1.name == "this").flatMap(_._2 match {
        case v@PureVar() => Some(v)
        case _ => throw new IllegalStateException("this must point to pure var or be unconstrained")
      })
      val reg2 = reg ++ thisEdge
      if (fc1 != fc2 || fn1 != fn2 || l1 != l2) Set() else {
        Set(State(s,heap, pure, reg2))
      }
    }
    case (CallbackMethodInvoke(clazz, name, loc), targetLoc@AppLoc(m,l,false), pre) => {
      val cmd = w.cmdBeforeLocation(targetLoc).asInstanceOf[ReturnCmd[M,C]]
      val thisId = PureVar()
      val thisTypeUpperBound: String = m.classType
      val newStackVars:Map[StackVar, Val] = if(cmd.returnVar.isDefined){
        ???
      }else Map()
      val newStack: Seq[CallStackFrame] =
        CallStackFrame(targetLoc,None, newStackVars + ??? )::pre.callStack


      ???
    }
    case t =>
      println(t)
      ???
  }
  def cmdTransfer(cmd:CmdWrapper[M,C], state: State):Set[State] = (cmd,state) match{
    case (AssignCmd(LocalWrapper(name,_), NewCommand(className),_,_),
        s@State(stack@f::_,heap,pureFormula, reg)) =>
      f.locals.get(StackVar(name)) match{
        case Some(purevar: PureVar) =>
          val tconstraint = PureConstraint(purevar, TypeComp, ClassType(className))
          val constraint = PureConstraint(purevar, NotEquals, NullVal)
          val newpf = pureFormula + tconstraint + constraint
          // TODO: check no fields are required to be non null
          Set(State(stack,heap, newpf, reg))
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
    case (AssignCmd(target:LocalWrapper, LocalWrapper(name, localType),_,_),s@State(f::t,_,_,_)) => {
      f.locals.get(StackVar(target.name)) match {
        case Some(v) =>
          val (pval,s1) = s.getOrDefine(target)
          val s2 = s1.clearLVal(target).copy(pureFormula =
            s1.pureFormula + PureConstraint(pval, TypeComp, SubclassOf(localType)))
          Set(s2.copy(callStack = f.copy(locals=f.locals + (StackVar(name) -> pval))::t))
        case None => Set(s)
      }
    }
    case (AssignCmd(lw: LocalWrapper, ThisWrapper(thisTypename),a,b), s) =>
      cmdTransfer(AssignCmd(lw, LocalWrapper("this", thisTypename),a,b),s)
    case _ =>
      ???
  }
  //def canAlias(tc:TypeConstraint, target: LVal):Boolean = (tc,target) match{
  //  case (SubClassOf(pureTypeName),LocalWrapper(_,lvalType)) => w.canAlias(pureTypeName, lvalType)
  //  case _ =>
  //    ???
  //}
}
