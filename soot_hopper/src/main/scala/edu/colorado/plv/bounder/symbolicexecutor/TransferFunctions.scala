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
    case (source@AppLoc(_, _, false), CallinMethodReturn(fmwClazz, fmwName,_), State(stack, heap, pure, reg)) =>
      Set(State(CallStackFrame(target, Some(source.copy(isPre = true)), Map()) :: stack, heap, pure, reg)) //TODO: lifestate rule transfer
    case (CallinMethodReturn(_, _,_), CallinMethodInvoke(_, _), state) => Set(state)
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
        val state1 = traceAllPredTransfer(CBEnter, (pkg,name),invar,outvar,pre)
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
      val state1 = traceAllPredTransfer(CBExit, (pkg,name), invar, outvar, preWithNewFrame)
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
      //TODO: this should return fmw type not specific type
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
    case f@AbsFormula(lsformula) if lsformula.contains(mt,sig) => {
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
    case f@AbsFormula(_) => f

    case v =>
      println(v)
      ???
  }
  /**
   * Update each trace abstraction in an abstract state
   * @param postState
   * @return
   */
  def traceAllPredTransfer(mt: MessageType,
                           sig:(String,String), invar:List[Option[LocalWrapper]], outvar:List[Option[LocalWrapper]],
                           postState: State):State = {
    val (invals, preState) = invar.foldLeft((List[Option[PureVar]](), postState)){
      case ((lpv,accSt), Some(local)) => {
        val (pv,state) = accSt.getOrDefine(local)
        (lpv :+ Some(pv), state)
      }
      case ((lpv, accSt), None) => (lpv:+ None, accSt)
    }
    val outvals = outvar.map{
      case Some(local) => postState.get(local) match {
        case Some(p@PureVar()) => Some(p)
        case None => None
        case _ =>
          ???
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
      // x = new T
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
      // x = y
      val lhsv = state.get(lhs) // Find what lhs pointed to if anything
      lhsv.map(pexpr =>{
        // remove lhs from abstract state (since it is assigned here)
        val state2 = state.clearLVal(lhs)
        val (rhsv, state3) = state2.getOrDefine(rhs)
        state3.copy(pureFormula = state3.pureFormula + PureConstraint(pexpr, Equals, rhsv))
      }).map(Set(_)).getOrElse(Set(state))
    }
    case AssignCmd(lhs:LocalWrapper, FieldRef(base, fieldtype, declType, fieldName), _) =>{
      // x = y.f
      //TODO: find a better way to structure this pyramid of doom
      (state.get(lhs), state.get(base)) match {
        case (None,_) => Set(state)
        case (Some(lhsv),Some(recv:PureVar)) =>{
          // Field ref base is in abstract state
          val state2 = state.clearLVal(lhs)
          state2.heapConstraints.get(FieldPtEdge(recv, fieldName)).map( a=>
            Set(state2.copy(pureFormula = state2.pureFormula + PureConstraint(lhsv, Equals, a))))
            .getOrElse(Set(state2))
        }
        case (Some(lhsv), None) => {
          // Field ref base is not in abstract state
          val state2 = state.clearLVal(lhs)
          val possibleHeapCells: Map[HeapPtEdge, PureExpr] = state2.heapConstraints.filter {
            case (FieldPtEdge(pv, heapFieldName), pureExpr) => fieldName == heapFieldName
            case _ =>
              ???
          } + (FieldPtEdge(PureVar(), fieldName) -> lhsv)
          val (basev,state3) = state.getOrDefine(base)
          possibleHeapCells.map{
            case (fpte@FieldPtEdge(p,n), pexp) =>
              state3.copy(pureFormula = state3.pureFormula +
                PureConstraint(basev, Equals, p) + PureConstraint(basev, TypeComp, SubclassOf(base.localType)) +
                PureConstraint(lhsv, Equals, pexp), heapConstraints = state3.heapConstraints + (fpte->pexp))
            case _ =>
              ???
          }.toSet
        }
        case _ =>
          ???
      }
    }
    case AssignCmd(FieldRef(base, fieldType, declType,fieldName), rhs, _) => {
      val possibleHeapCells = state.heapConstraints.filter {
        case (FieldPtEdge(pv, heapFieldName), _) => fieldName == heapFieldName
      }
      // Get or define right hand side
      val (rhsv,state2) = rhs match{ //TODO: seems like rhsv should be used?
        case NullConst => (NullVal,state)
        case lw@LocalWrapper(_,_) => state.getOrDefine(lw)
      }
      // get or define base of assignment
      val (basev,state3) = state2.getOrDefine(base)
      // Enumerate over existing base values that could alias assignment
      possibleHeapCells.map{
        case (pte@FieldPtEdge(heapPv, fieldName), tgt) =>
          state3.copy(heapConstraints = state3.heapConstraints - pte,
            pureFormula = state3.pureFormula + PureConstraint(basev, Equals, tgt)) //TODO: basv = target? this seems wrong
        case _ =>
          ???
      }.toSet
      // TODO: add case where nothing is aliased
    }
    case AssignCmd(FieldRef(base,_,_,name), NullConst,_) => {
      val (basev, state2) = state.getOrDefine(base)

      ???
    }
    case c =>
      println(c)
      ???
  }
}
