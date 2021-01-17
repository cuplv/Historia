package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.{I, LSAbsBind, LSPred, LSSpec, LSTrue, Or}
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.symbolicexecutor.state._

class TransferFunctions[M,C](w:IRWrapper[M,C], specSpace: SpecSpace) {

  def cbInvTransfer(pre:State, pkg:String, name:String, invars:List[Option[LocalWrapper]]):Set[State] = {
    ???
  }
  /**
   *
   * @param pre state before current location
   * @param target predecessor of current location
   * @param source current location
   * @return set of states that may reach the target state by stepping from source to target
   */
  def transfer(pre: State, target: Loc, source: Loc): Set[State] = (source, target, pre) match {
    case (source@AppLoc(_, _, false), CallinMethodReturn(fmwClazz, fmwName), State(stack, heap, pure, reg,_)) =>
      Set(State(CallStackFrame(target, Some(source.copy(isPre = true)), Map()) :: stack, heap, pure, reg))
    case (CallinMethodReturn(_, _), CallinMethodInvoke(_, _), state) => Set(state)
    case (CallinMethodInvoke(_, _), loc@AppLoc(_, _, true), s@State(h :: t, _, _, _,_)) => {
      //TODO: parameter mapping
      Set(s.copy(callStack = t))
    }
    case (AppLoc(_, _, true), AppLoc(_, _, false), pre) => Set(pre)
    case (appLoc@AppLoc(c1, m1, false), AppLoc(c2, m2, true), prestate) if c1 == c2 && m1 == m2 =>
      cmdTransfer(w.cmdBeforeLocation(appLoc), prestate)
    case (AppLoc(containingMethod, m, true), cmInv@CallbackMethodInvoke(fc1, fn1, l1), pre) => {
      // If call doesn't match return on stack, return bottom
      // Target loc of CallbackMethodInvoke means just before callback is invoked
      if(!pre.callStack.isEmpty){
        pre.callStack.head match {
          case CallStackFrame(CallbackMethodReturn(fc2,fn2,l2,_),_,_) if fc1 != fc2 || fn1 != fn2 || l1 != l2 =>
            ???
            return Set()//TODO: does this ever happen with callback entry? (remove ??? when this is figured out)
          case _ =>
        }
      }

      val (pkg, name) = msgCmdToMsg(cmInv)
      val invars: List[Option[LocalWrapper]] = None::containingMethod.getArgs
      // Add all parameters to abs state (note just moved these out of the trace transfer)
      val state0 = defineVars(pre, invars)
      //update existing spec instantiations
      val state1 = traceAllPredTransfer(CBEnter, (pkg,name),invars,state0)
      // Since this is a back message, instantiate any new instances of the spec
      //add new instantiations of specs
      val states2 = newSpecInstanceTransfer(CBEnter,(pkg,name), invars, cmInv, state1)
      // Remove the top call stack frame from each candidate state since we are crossing the entry to a method
      val newCallStack = if (states2.callStack.isEmpty) Nil else states2.callStack.tail
      val out = states2.copy(callStack = newCallStack)
      Set(out)
    }
    case (CallbackMethodInvoke(_, _, _), targetLoc@CallbackMethodReturn(_,_,mloc, _), pre) => {
      // Case where execution goes to the exit of another callback
      // TODO: nested callbacks not supported yet, assuming we can't go back to callin entry
      // TODO: note that the callback method invoke is to be ignored here.
      // TODO: case split on equality between args and params of trace abstraction? ------
      // Control flow resolver is responsible for the
      val appLoc = AppLoc(targetLoc.loc, targetLoc.line.get,false)
      val rvar = w.cmdBeforeLocation(appLoc) match{
        case ReturnCmd(v,_) =>v
        case c => throw new IllegalStateException(s"return from non return command $c ")
      }
      val newFrame = CallStackFrame(appLoc, None, Map())
      val pre_push = pre.copy(callStack = newFrame::pre.callStack)
      val (pkg,name) = msgCmdToMsg(target)
      val lsvars: List[Option[LocalWrapper]] = rvar::mloc.getArgs
      val state0 = defineVars(pre_push, lsvars)
      val state1 = traceAllPredTransfer(CBExit, (pkg,name), lsvars, state0)
      val state2 = newSpecInstanceTransfer(CBExit, (pkg,name), lsvars, target, state1)
      Set(state2)
    }
    case (CallbackMethodReturn(_,_,mloc1,_), AppLoc(mloc2,_,_), state) =>
      assert(mloc1 == mloc2) ; Set(state) // transfer handled by processing callbackmethodreturn, nothing to do here
    case t =>
      println(t)
      ???
  }

  private def defineVars(pre: State, invars: List[Option[LocalWrapper]]) = {
    invars.foldLeft(pre) {
      case (cstate, Some(invar)) => cstate.getOrDefine(invar)._2
      case (cstate, None) => cstate
    }
  }

  /**
   * For a back message with a given package and name, instantiate each rule as a new trace abstraction
 *
   * @param loc
   * @param postState
   * @return a new trace abstraction for each possible rule
   */
  def newSpecInstanceTransfer(mt: MessageType,
                              sig:(String,String), allVar:List[Option[LocalWrapper]],
                              loc: Loc, postState: State): State = {
    //TODO: last element is list of varnames, should probably use that
    val specOpt = specSpace.specsBySig(mt,sig._1,sig._2)

    // Split spec into pred and target if it exists, otherwise pre state is post state
    val (pred, target) = specOpt match{
      case Some(LSSpec(pred, target)) => (pred,target)
      case None => return postState
    }

    val parameterPairing: Seq[(String, Option[LocalWrapper])] = (target.lsVars zip allVar)

    // Match each lsvar to absvar if both exist
    val formula = parameterPairing.foldLeft(AbsFormula(pred):AbstractTrace) {
      case (abstTrace, (lsvar, Some(invar))) if lsvar != "_" =>
        AbsAnd(abstTrace, AbsEq(lsvar, postState.get(invar).get))
      case (abstTrace, (_, None)) => abstTrace
    }
    val newLsAbstraction = AbsArrow(formula, Nil)
    postState.copy(traceAbstraction = postState.traceAbstraction + newLsAbstraction)
  }

  /**
   * Get input and output vars of executing part of the app responsible for an observed message
   * Note: all vars used in invoke or assign/invoke can be in post state
   * @param loc
   * @return (pkg, function name)
   */
  private def msgCmdToMsg(loc: Loc): (String, String) = {

    loc match {
      //TODO: this should return fmw type not specific type
      case CallbackMethodReturn(pkg, name, _,_) => (pkg, name)
      case CallbackMethodInvoke(pkg, name, _) => (pkg,name)
      case CallinMethodInvoke(clazz, name) => (clazz,name)
      case CallinMethodReturn(clazz,name) => (clazz,name)
      case v =>
        ???
    }
  }

  /**
   * Assume state is updated with appropriate vars
   *
   * @return
   */
  def predTransferTrace(pred:TraceAbstractionArrow, mt:MessageType,
                        sig:(String,String), vals: List[Option[PureExpr]]):TraceAbstractionArrow = pred match{
    case AbsArrow(traceAbstraction, suffixAbstraction) =>
      specSpace.getIWithFreshVars(mt, sig) match{
        case Some(i@I(_,_,lsVars)) =>
          val modelVarConstraints: Seq[AbstractTrace] = (lsVars zip vals).flatMap{
            case (lsvar, Some(stateVal)) if lsvar != "_"  => Some(AbsEq(lsvar,stateVal))
            case _ => None
          }
          //TODO: handle case where no vars should be matched
          val modelVarFormula = if(modelVarConstraints.isEmpty){
            ???
          }else {
            modelVarConstraints.reduceRight{(a,b) => AbsAnd(a,b)}
          }
          AbsArrow(AbsAnd(modelVarFormula, traceAbstraction), // map lifestate vars to
            i::suffixAbstraction) // prepend message if in spec space
        case None => pred
      }
  }
  /**
   * Update each trace abstraction in an abstract state
   * @param postState
   * @return
   */
  def traceAllPredTransfer(mt: MessageType,
                           sig:(String,String), alvar:List[Option[LocalWrapper]],
                           postState: State):State = {
    // values we want to track should already be added to the state
    val allVal = alvar.map(_.flatMap(postState.get(_)))
    val newTraceAbs: Set[TraceAbstractionArrow] = postState.traceAbstraction.map {
      traceAbs => predTransferTrace(traceAbs, mt, sig, allVal)
    }
    postState.copy(traceAbstraction = newTraceAbs)
  }

  def cmdTransfer(cmd:CmdWrapper, state:State):Set[State] = cmd match{
    case AssignCmd(lhs@LocalWrapper(_, _), NewCommand(className),_) =>
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
    case AssignCmd(lw: LocalWrapper, ThisWrapper(thisTypename),a) =>
      cmdTransfer(AssignCmd(lw, LocalWrapper("@this", thisTypename),a),state)
    case AssignCmd(lhs: LocalWrapper,rhs:LocalWrapper,_) => //
      // x = y
      val lhsv = state.get(lhs) // Find what lhs pointed to if anything
      lhsv.map(pexpr =>{
        // remove lhs from abstract state (since it is assigned here)
        val state2 = state.clearLVal(lhs)
        val (rhsv, state3) = state2.getOrDefine(rhs)
        state3.copy(pureFormula = state3.pureFormula + PureConstraint(pexpr, Equals, rhsv))
      }).map(Set(_)).getOrElse(Set(state))
    case AssignCmd(lhs:LocalWrapper, FieldRef(base, fieldtype, declType, fieldName), _) =>
      // x = y.f
      state.get(lhs) match{
        case Some(lhsV) =>{
          val (basev, state1) = state.getOrDefine(base)
          val heapCell = FieldPtEdge(basev, fieldName)
          val state2 = state1.clearLVal(lhs)
          Set(state2.copy(
            heapConstraints = state1.heapConstraints + (heapCell -> lhsV),
            pureFormula = state1.pureFormula + PureConstraint(lhsV, TypeComp, SubclassOf(fieldtype))
          ))
        }
        case None => Set(state)
      }
      //TODO: find a better way to structure this pyramid of doom
//      (state.get(lhs), state.get(base)) match {
//        case (None,_) => Set(state)
//        case (Some(lhsv),Some(recv:PureVar)) =>
//          // Field ref base is in abstract state
//          val state2 = state.clearLVal(lhs)
//          state2.heapConstraints.get(FieldPtEdge(recv, fieldName)).map( a=>
//            Set(state2.copy(pureFormula = state2.pureFormula + PureConstraint(lhsv, Equals, a))))
//            .getOrElse(Set(state2))
//        case (Some(lhsv), None) =>
//          // Field ref base is not in abstract state
//          val state2 = state.clearLVal(lhs)
//          val possibleHeapCells: Map[HeapPtEdge, PureExpr] = state2.heapConstraints.filter {
//            case (FieldPtEdge(pv, heapFieldName), pureExpr) => fieldName == heapFieldName
//            case _ =>
//              ???
//          } + (FieldPtEdge(PureVar(), fieldName) -> lhsv)
//          val (basev,state3) = state.getOrDefine(base)
//          possibleHeapCells.map{
//            case (fpte@FieldPtEdge(p,n), pexp) =>
//              state3.copy(pureFormula = state3.pureFormula +
//                PureConstraint(basev, Equals, p) + PureConstraint(basev, TypeComp, SubclassOf(base.localType)) +
//                PureConstraint(lhsv, Equals, pexp), heapConstraints = state3.heapConstraints + (fpte->pexp))
//            case _ =>
//              ???
//          }.toSet
//        case _ =>
//          ???
//      }
    case AssignCmd(FieldRef(base, fieldType, _,fieldName), rhs, _) =>
      val (basev,state2) = state.getOrDefine(base)

      // get all heap cells with correct field name
      val possibleHeapCells = state.heapConstraints.filter {
        case (FieldPtEdge(pv, heapFieldName), _) => fieldName == heapFieldName
      }

      // Get or define right hand side
      val (rhsv,state3) = rhs match{
        case NullConst => (NullVal,state)
        case lw@LocalWrapper(_,_) => state2.getOrDefine(lw)
        case _ =>
          ??? //TODO: implement other const values
      }
      // get or define base of assignment
      // Enumerate over existing base values that could alias assignment
      val casesWithHeapCellAlias = possibleHeapCells.map{
        case (pte@FieldPtEdge(heapPv, _), tgt) =>
          state3.copy(heapConstraints = state3.heapConstraints - pte,
            pureFormula = state3.pureFormula +
              PureConstraint(basev, Equals, heapPv) +
              PureConstraint(tgt, Equals, rhsv))
        case _ =>
          ???
      }.toSet
      val notAlias = possibleHeapCells.map{
        case (FieldPtEdge(heapPv, _), _) => PureConstraint(basev, NotEquals, heapPv)
        case _ => ???
      }
      val caseWithNoHeapAlias = state3.copy(pureFormula = state3.pureFormula.union(notAlias.toSet))
      casesWithHeapCellAlias + caseWithNoHeapAlias
    case AssignCmd(FieldRef(base,_,_,name), NullConst,_) =>
      val (basev, state2) = state.getOrDefine(base)

      ???
    case c =>
      println(c)
      ???
  }
}
