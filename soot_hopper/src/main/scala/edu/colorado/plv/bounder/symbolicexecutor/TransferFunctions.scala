package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.{I, LSAbsBind, LSPred, LSSpec, LSTrue, Or}
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
      if (fc1 != fc2 || fn1 != fn2 || l1 != l2) Set() else {
        // Update each element in the trace abstraction for the current message
        val (pkg, name, invar, outvar) = msgCmdToMsg(cmloc)
        // TODO: add all input vars to abs state, currently only considering this
        //update existing spec instantiations
        val state1 = tracePredTransfer(CBEnter, (pkg,name),invar,outvar,pre)
        // Since this is a back message, instantiate any new instances of the spec
        //add new instantiations of specs
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
      val (pkg,name,invar,outvar) = msgCmdToMsg(target)
      println(s"$pkg $name $invar $outvar")
      val newStack =
        CallStackFrame(targetLoc, None, newStackVars + (StackVar("this") -> thisId)) :: pre.callStack
      val preWithNewFrame = pre.copy(callStack = newStack)
      val state1 = tracePredTransfer(CBExit, (pkg,name), invar, outvar, preWithNewFrame)
      val state2 = newSpecInstanceTransfer(CBExit, (pkg,name), invar, target, state1)
      Set(state2)
    }
    case (CallbackMethodReturn(_,_,mloc1,_), AppLoc(mloc2,_,_), state) =>
      assert(mloc1 == mloc2) ; Set(state) // transfer handled by processing callbackmethodreturn, nothing to do here
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
//    val (thisvar,newState) = postState.getOrDefine(LocalWrapper("this",sig._1))
    val (outState,newLsAbstractions) =
      applicableSpecs.foldLeft(postState, Set[TraceAbstraction]()) {
        case ((bstate,specset), LSSpec(pred, I(targetmt, _, lsVars))) if targetmt == mt =>{
          //TODO: find all args in abstract state
          val (introducedTA, newState) = (lsVars zip invar).foldLeft(List[TraceAbstraction](),bstate){
            case ((ta,cstate),(lsvar, Some(local))) => {
              val (newPv, newState) = cstate.getOrDefine(local)
              (AbsEq(lsvar,newPv)::ta,newState)
            }
            case (acc,(_,None)) => acc
          }
          val abstraction: TraceAbstraction =
            introducedTA.foldLeft(AbsFormula(pred): TraceAbstraction) { (acc, v) => AbsAnd(acc, v) }
          (newState,specset + abstraction)
        }
        case (bstate,_) => bstate
    }
    postState.copy(traceAbstraction = postState.traceAbstraction.union(newLsAbstractions))
  }

  /**
   * Get input and output vars of executing part of the app responsible for an observed message
   * TODO: currenlty only includes "this" should also include return vals and params
   * @param loc
   * @return (pkg, function name, app vars from pre state used, app vars assigned by cmd)
   */
  private def msgCmdToMsg(loc: Loc): (String, String, List[Option[LocalWrapper]], List[Option[LocalWrapper]]) = loc match {
    case CallbackMethodReturn(pkg, name, _, None) =>
      (pkg, name, List(None, Some(LocalWrapper("this",pkg))), List(None))
    case CallbackMethodReturn(pkg, name, m, Some(l:JimpleLineLoc)) if l.returnTypeIfReturn == Some("void") => {
      val cmd = w.cmdBeforeLocation(AppLoc(m, l, false))
      (pkg, name, List(None, Some(LocalWrapper("this", pkg))), List(None))
    }
    case v =>
          ???
  }

  /**
   * Assume state is updated with appropriate vars
   *
   * @return
   */
  def predTransferTrace(pred:TraceAbstraction, mt:MessageType,
                        sig:(String,String), invals:List[Option[PureVar]],
                        outvals: List[Option[PureVar]]):TraceAbstraction = pred match{
    case AbsAnd(lhs,rhs) =>
      AbsAnd(predTransferTrace(lhs, mt, sig, invals, outvals), predTransferTrace(rhs, mt, sig, invals, outvals))
    case AbsArrow(pred, m) => AbsArrow(predTransferTrace(pred,mt, sig, invals, outvals),m)
    case eq@AbsEq(_,_) => eq
    case f@AbsFormula(_) => {
      specSpace.getIWithFreshVars(mt,sig).map( newi =>
        // Add message before other arrows with assertions about the ls variables
        newi.lsVars.zipWithIndex.foldLeft(AbsArrow(f, newi):TraceAbstraction) {
          case (acc,(varname,varind)) if varname != "_" => {
            val acc1: TraceAbstraction = invals(varind).map(v => AbsAnd(acc,AbsEq(varname,v))).getOrElse(acc)
            if (outvals.size > varind) {
              outvals(varind).map(v =>
                AbsAnd(acc1, AbsEq(varname, v))).getOrElse(acc1)
            }else acc1
          }
          case (acc,_) => acc
        }
      )
    }.getOrElse(pred)

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
    val (invals, preState) = invar.foldLeft((List[Option[PureVar]](), postState)){
      case ((lpv,accSt), Some(local)) => {
        val (pv,state) = accSt.getOrDefine(local)
        (Some(pv)::lpv, state)
      }
      case ((lpv, accSt), None) => (None::lpv, accSt)
    }
    val outvals = outvar.map{
      case Some(local) => postState.get(local) match {
        case Some(p@PureVar()) => Some(p)
        case None => None
      }
      case None => None
    }
    val newTraceAbs: Set[TraceAbstraction] = postState.traceAbstraction.map {
      traceAbs => predTransferTrace(traceAbs, mt, sig, invals, outvals)
    }
    preState.copy(traceAbstraction = newTraceAbs)
  }

  def cmdTransfer(cmd:CmdWrapper, state:State):Set[State] = cmd match{
    case AssignCmd(lhs@LocalWrapper(_, _), NewCommand(className),_) => {
      Set(state.get(lhs) match {
        case Some(v) => state
          .clearLVal(lhs)
          .copy(pureFormula = state.pureFormula
            + PureConstraint(v, TypeComp, ClassType(className))
            + PureConstraint(v, NotEquals, NullVal)
          )
        case None => state
      })
    }
    case AssignCmd(lw: LocalWrapper, ThisWrapper(thisTypename),a) =>
      cmdTransfer(AssignCmd(lw, LocalWrapper("this", thisTypename),a),state)
    case AssignCmd(lhs: LocalWrapper,rhs:LocalWrapper,_) => { //
      val lhsv = state.get(lhs) // Find what lhs pointed to if anything
      lhsv.flatMap(pexpr =>{
        // remove lhs from abstract state (since it is assigned here)
        val state2 = state.clearLVal(lhs)
        state2.get(rhs).map(rexpr =>
          state2.copy(pureFormula = state2.pureFormula + PureConstraint(pexpr, Equals, rexpr))
        )
      }).map(Set(_)).getOrElse(Set(state))
    }
    case AssignCmd(lhs:LocalWrapper, FieldRef(base, fieldtype, declType, fieldName), _) =>{
      //TODO: find a better way to structure this pyramid of doom
      (state.get(lhs), state.get(base)) match {
        case (Some(lhsv),Some(recv)) =>{
          val state2 = state.clearLVal(lhs)
          ???
        }
        case (l,r) => {
          println(l)
          println(r)
          ???
        }
      }
//      state.get(lhs) match{
//        case Some(lhsv) => {
//          state.get(base) match {
//            case Some(recv:PureVar) => {
//              val state3 = state.clearLVal(lhs)
//              state3.heapConstraints.get(FieldPtEdge(recv, fieldName)) match {
//                case Some(heaptgt) =>
//                  ???
//                case None =>
//                  ???
//              }
//            }
//            case None => {
//              val state2 = state.clearLVal(lhs)
//              // Define base of deref since it is not in the state already
//              val (recv,state3) = state2.getOrDefine(base)
//              // find heap cells that may alias
//              val possibleHeapCells = state3.heapConstraints.filter {
//                case (FieldPtEdge(pv, heapFieldName), pureExpr) => fieldName == heapFieldName
//              }
//              ???
//            }
//          }
//        }
//        case None => Set(state)
//      }
    }
    case c =>
      println(c)
      ???
  }
  //TODO: structure assign operation better, split into
  // remove lhs from state and store thing that it points to
  // add assertion that thing on rhs is equal to what lhs pointed to
  def cmdTransferOld(cmd:CmdWrapper, state: State):Set[State] = (cmd,state) match{
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
      if(s.get(target).isDefined) {
        val (tgtval, s1) = s.getOrDefine(target)
        if(s.get(base).isDefined){
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
    case other =>
      println(other)
      ???
  }
}
