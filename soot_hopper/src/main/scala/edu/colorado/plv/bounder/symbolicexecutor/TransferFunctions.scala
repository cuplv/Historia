package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSAbsBind, LSPred, LSSpec, LSTrue, Or}
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.symbolicexecutor.state._

class TransferFunctions[M,C](w:IRWrapper[M,C], specSpace: SpecSpace) {
  /**
   *
   * @param pre state before current location
   * @param target predecessor of current location
   * @param source current location
   * @return set of states that may reach the target state by stepping from source to target
   */
  def transfer(pre: State, target: Loc, source: Loc): Set[State] = (source, target, pre) match {
    case (source@AppLoc(_, _, false), CallinMethodReturn(fmwClazz, fmwName), State(stack, heap, pure, reg)) =>
      Set(State(CallStackFrame(target, Some(source.copy(isPre = true)), Map()) :: stack, heap, pure, reg)) //TODO: lifestate rule transfer
    case (CallinMethodReturn(_, _), CallinMethodInvoke(_, _), state) => Set(state)
    case (CallinMethodInvoke(_, _), loc@AppLoc(_, _, true), s@State(h :: t, _, _, _)) => {
      //TODO: parameter mapping
      Set(s.copy(callStack = t))
    }
    case (AppLoc(_, _, true), AppLoc(_, _, false), pre) => Set(pre)
    case (appLoc@AppLoc(c1, m1, false), AppLoc(c2, m2, true), prestate) if c1 == c2 && m1 == m2 =>
      cmdTransfer(w.cmdBeforeLocation(appLoc), prestate)
    case (AppLoc(_, m, true), CallbackMethodInvoke(fc1, fn1, l1), State(CallStackFrame(cmloc@CallbackMethodReturn(fc2, fn2, l2, _), None, locals) :: s, heap, pure, reg)) => {
      // If call doesn't match return on stack, return bottom
      // Target loc of CallbackMethodInvoke means just before callback is invoked
      // TODO: if
      val thisEdge: Option[PureVar] = locals.find(l => l._1.name == "this").flatMap(_._2 match {
        case v@PureVar() => Some(v)
        case _ => throw new IllegalStateException("this must point to pure var or be unconstrained")
      })
      if (fc1 != fc2 || fn1 != fn2 || l1 != l2) Set() else {
        // Update each element in the trace abstraction for the current message
        val (pkg, name, invar, outvar) = msgCmdToMsg(cmloc)
        // TODO: add all input vars to abs state, currently only considering this
        //update existing spec instantiations
        val state1 = tracePredTransfer(CBEnter, (pkg,name),invar,outvar,pre)
        // Since this is a back message, instantiate any new instances of the spec
        //add new instantiations of specs
        //TODO: get rid of theta hat
        val states2 = newSpecInstanceTransfer(CBEnter,(pkg,name), invar, cmloc, state1)
        // Remove the top call stack frame from each candidate state since we are crossing the entry to a method
        val out = states2.copy(callStack = s)
        Set(out) // TODO: check that this output makes sense
      }
    }
    case (CallbackMethodInvoke(_, _, _), targetLoc@CallbackMethodReturn(_,_,mloc, _), pre) => {
      // Case where execution goes to the exit of another callback
      // TODO: nested callbacks not supported yet, assuming we can't go back to callin entry
      // TODO: note that the callback method invoke is to be ignored here.
      // Control flow resolver is responsible for the
      val appLoc = AppLoc(targetLoc.loc, targetLoc.line.get,false)
      val cmd = w.cmdBeforeLocation(appLoc).asInstanceOf[ReturnCmd]
      val thisId: PureExpr = PureVar()
      val thisTypeUpperBound: String = mloc.classType
      val newStackVars: Map[StackVar, PureExpr] = if (cmd.returnVar.isDefined) {
        ???
      } else Map()
      val newStack =
        CallStackFrame(targetLoc, None, newStackVars + (StackVar("this") -> thisId)) :: pre.callStack

      // TODO: symbolic trace transfer like above
//      val newStates = tracePredTransfer(targetLoc, pre)

//      val out = newStates.map(a => a.copy(callStack = newStack))
//      out
      ???
    }
    case t =>
      println(t)
      ???
  }

  /**
   * For a back message with a given package and name, instantiate each rule as a new trace abstraction
   * @param loc
   * @param postState
   * @return a new trace abstraction for each possible rule
   */
  def newSpecInstanceTransfer(mt: MessageType,
                              sig:(String,String), invar:List[Option[LocalWrapper]],
                              loc: Loc, postState: State): State = {
    //TODO: last element is list of varnames, should probably use that
    val applicableSpecs = specSpace.specsBySig(sig._1,sig._2)
    val (thisvar,newstack) = postState.getOrDefine(LocalWrapper("this",sig._1))
    val newLsAbstractions:Set[TraceAbstraction] = applicableSpecs.map{case LSSpec(pred, target) =>
      //TODO: find all args in abstract state
      val lsvars = target.lsVars
      assert(lsvars(0) == "_") // TODO: temporary assumption of no return val
//      val thisOption = postState.getLocal(LocalWrapper("this", pkg))

//      assert(thisOption.isDefined) // TODO: temporary assumption that this is always defined
//      val newLsAbstraction = LSAbstraction(pred, Map(lsvars(1) -> thisOption.get))
//      newLsAbstraction
      //TODO: update for new trace abstraction
      ???
    }
    postState.copy(traceAbstraction = postState.traceAbstraction.union(newLsAbstractions))
  }

  /**
   *
   * @param loc
   * @return (pkg, function name, app vars from pre state used, app vars assigned by cmd
   */
  private def msgCmdToMsg(loc: Loc): (String, String, List[Option[LocalWrapper]], List[Option[LocalWrapper]]) = loc match {
    case CallbackMethodReturn(pkg, name, _, None) => (pkg, name, List(None, Some(LocalWrapper("this",pkg))), List()) //TODO: first element return var
    case CallbackMethodReturn(pkg, name, m, Some(l)) =>
      val retvar:Option[LocalWrapper] = w.cmdBeforeLocation(AppLoc(m,l,false)) match {
        case v =>
          ???
      }
      (pkg, name, List(retvar, Some(LocalWrapper("this",pkg))), List()) //TODO: first element return var
    case _ =>
      ???
  }

  def predTransferTrace(pred:LSPred, mt:MessageType,
                        sig:(String,String), variables:List[Option[LocalWrapper]], postState:State):LSPred = pred match{
    case i@I(mtp, sigset, vars) if sigset.contains(sig) && mtp == mt =>
      Or(i, (variables zip vars).foldLeft(LSTrue:LSPred)((acc, v) => v match{
        case (None,_) => acc
        case (Some(sv),mv) => And(acc,LSAbsBind(mv, postState.getLocal(sv).get))
      }))
    case i@I(_,_,_) => i
    case v =>
      println(v)
      ???
  }
  /**
   * Update each trace abstraction in an abstract state
   * @param postState
   * @return
   */
  def tracePredTransfer(mt: MessageType,
                        sig:(String,String), invar:List[Option[LocalWrapper]], outvar:List[Option[LocalWrapper]],
                        postState: State):State = {
    //TODO: you were here 11/9/20
    // update state for
    val newTraceAbs: Set[TraceAbstraction] = postState.traceAbstraction.map {
      case _ => ??? //TODO: update
    //  case TopTraceAbstraction => TopTraceAbstraction
    //  case LSAbstraction(pred,bind) => {
    //    val combvar = invar.zipAll(outvar,None,None)
    //      .map( a => if(a._1 == None) a._2 else a._1)
    //    LSAbstraction(predTransferTrace(pred, mt, sig, combvar, postState), bind)
    //  }
    //  case Reg(v) => ???
    }
    postState.copy(traceAbstraction = newTraceAbs)
  }
  def cmdTransfer(cmd:CmdWrapper, state: State):Set[State] = (cmd,state) match{
    case (AssignCmd(LocalWrapper(name,_), NewCommand(className),_),
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
        case c =>
          println(c)
          throw new IllegalStateException("Assign object to primitive")
      }
    case (AssignCmd(target, FieldRef(base, containsType, declType, name),_), s) =>{
      if(s.getLocal(target).isDefined) {
        val (tgtval, s1) = s.getOrDefine(target)
        if(s.getLocal(base).isDefined){
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
            (FieldPtEdge(basePure.asInstanceOf[PureVar],name)-> tgtval)).clearLVal(target)
        }
      }else{
        Set(s) // No change to state if assignment doesn't affect anything in current state
      }
    }
    case (AssignCmd(target:LocalWrapper, LocalWrapper(name, localType),_),s@State(f::t,_,_,_)) => {
      f.locals.get(StackVar(target.name)) match {
        case Some(v) =>
          val (pval,s1) = s.getOrDefine(target)
          val s2 = s1.clearLVal(target).copy(pureFormula =
            s1.pureFormula + PureConstraint(pval, TypeComp, SubclassOf(localType)))
          Set(s2.copy(callStack = f.copy(locals=f.locals + (StackVar(name) -> pval))::t))
        case None => Set(s)
      }
    }
    case (AssignCmd(lw: LocalWrapper, ThisWrapper(thisTypename),a), s) =>
      cmdTransfer(AssignCmd(lw, LocalWrapper("this", thisTypename),a),s)
    case _ =>
      ???
  }
  //def canAlias(tc:TypeConstraint, target: LVal):Boolean = (tc,target) match{
  //  case (SubClassOf(pureTypeName),LocalWrapper(_,lvalType)) => w.canAlias(pureTypeName, lvalType)
  //  case _ =>
  //    ???
  //}
}
