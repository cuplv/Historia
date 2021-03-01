package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{NullConst, _}
import edu.colorado.plv.bounder.lifestate.LifeState._
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.TransferFunctions.{relevantAliases, relevantAliases2}
import edu.colorado.plv.bounder.symbolicexecutor.state._
import upickle.default._

object TransferFunctions{
  /**
   * Get set of things that if aliased, change the trace abstraction state
   * TODO: this is over approx
   * @param pre state before cmd that emits an observed message
   * @param dir callback/callin entry/exit
   * @param signature class and name of method
   * @return
   */
  def relevantAliases(pre: State,
                      dir: MessageType,
                      signature: (String, String)) :Set[List[LSParamConstraint]]  = {
    val relevantI: Set[(I, List[LSParamConstraint])] = pre.findIFromCurrent(dir, signature)
    relevantI.map{
      case (I(_, _, vars),p)=> p
    }
  }
  //TODO: replace relevantAliases with this
  // transfer should simply define any variables that aren't seen in the state but read
  // alias considerations are done later by the trace abstraction or by separation logic
  def relevantAliases2(pre:State,
                       dir:MessageType,
                       signature: (String,String),
                       lst : List[Option[RVal]]):List[Option[RVal]] = {
    val relevantI = pre.findIFromCurrent(dir,signature)
    lst.zipWithIndex.map{ case (rval,ind) =>
      val existsNAtInd = relevantI.exists{i =>
        val vars: Seq[String] = i._1.lsVars
        val out = (ind < vars.length) && !LSAnyVal.matches(vars(ind))
        out
      }
      if(existsNAtInd) rval else None
    }
  }
}

class TransferFunctions[M,C](w:IRWrapper[M,C], specSpace: SpecSpace,
                             classHierarchyConstraints: ClassHierarchyConstraints) {
  private val resolver = new DefaultAppCodeResolver(w)
  def defineVarsAs(state: State, comb: List[(Option[RVal], Option[PureExpr])]):State =
    comb.foldLeft(state){
      case (stateNext, (None,_)) => stateNext
      case (stateNext, (_,None)) => stateNext
      case (stateNext, (Some(rval), Some(pexp))) => stateNext.defineAs(rval, pexp)
    }

  /**
   *
   * @param postState state after current location in control flow
   * @param target predecessor of current location
   * @param source current location
   * @return set of states that may reach the target state by stepping from source to target
   */
  def transfer(postState: State, target: Loc, source: Loc): Set[State] = (source, target) match {
    case (source@AppLoc(_, _, false), cmret@CallinMethodReturn(_, _)) =>
      // traverse back over the retun of a callin
      // "Some(source.copy(isPre = true))" places the entry to the callin as the location of call
      val (pkg, name) = msgCmdToMsg(cmret)
      val inVars: List[Option[RVal]] = inVarsForCall(source)
      val relAliases = relevantAliases2(postState, CIExit, (pkg,name),inVars)
      val frame = CallStackFrame(target, Some(source.copy(isPre = true)), Map())
      val (rvals, state0) = getOrDefineRVals(relAliases, postState)
      val state1 = traceAllPredTransfer(CIExit, (pkg,name),rvals, state0)
      //TODO: better state names
      val outState = newSpecInstanceTransfer(CIExit, (pkg, name), inVars, cmret, state1)
      val outState1: Set[State] = inVars match{
        case Some(revar:LocalWrapper)::_ => outState.map(s3 => s3.clearLVal(revar))
        case _ => outState
      }
      val outState2 = outState1.map(s2 => s2.copy(callStack = frame::s2.callStack, nextCmd = None))

      val out = outState2.map{ oState =>
        //clear assigned var from stack if exists
        val statesWithClearedReturn = inVars.head match{
          case Some(v:LocalWrapper) => oState.clearLVal(v)
          case None => oState
          case v => throw new IllegalStateException(s"Malformed IR. Callin result assigned to non-local: $v")
        }
        statesWithClearedReturn
      }
      out
    case (CallinMethodReturn(_, _), CallinMethodInvoke(_, _)) => Set(postState)
    case (cminv@CallinMethodInvoke(_, _), ciInv@AppLoc(_, _, true)) =>
      assert(postState.callStack.nonEmpty, "Bad control flow, abstract stack must be non-empty.")
      val invars = inVarsForCall(ciInv)
      val (pkg,name) = msgCmdToMsg(cminv)
      val relAliases = relevantAliases2(postState, CIEnter, (pkg,name),invars)
      val ostates:Set[State] = {
        val (rvals, state0) = getOrDefineRVals(relAliases, postState)
        val state1 = traceAllPredTransfer(CIEnter, (pkg, name), rvals, state0)
        Set(state1)
      }
      ostates.map(s => s.copy(callStack = s.callStack.tail, nextCmd = Some(ciInv)))
    case (AppLoc(_, _, true), AppLoc(_, _, false)) => Set(postState)
    case (appLoc@AppLoc(c1, m1, false), postLoc@AppLoc(c2, m2, true)) if c1 == c2 && m1 == m2 =>
      cmdTransfer(w.cmdAtLocation(appLoc), postState).map(_.setNextCmd(Some(postLoc)))
    case (AppLoc(containingMethod, m, true), cmInv@CallbackMethodInvoke(fc1, fn1, l1)) =>
      // If call doesn't match return on stack, return bottom
      // Target loc of CallbackMethodInvoke means just before callback is invoked
      if(postState.callStack.nonEmpty){
        postState.callStack.head match {
          case CallStackFrame(CallbackMethodReturn(fc2,fn2,l2,_),_,_) if fc1 != fc2 || fn1 != fn2 || l1 != l2 =>
            throw new IllegalStateException("ControlFlowResolver should enforce stack matching")
          case _ =>
        }
      }

      val invars: List[Option[LocalWrapper]] = None :: containingMethod.getArgs
      val (pkg, name) = msgCmdToMsg(cmInv)
      val relAliases = relevantAliases2(postState, CBEnter, (pkg,name),invars)
      val (inVals, state0) = getOrDefineRVals(relAliases,postState)
      val state1 = traceAllPredTransfer(CBEnter, (pkg,name), inVals, state0)
      val b = newSpecInstanceTransfer(CBEnter, (pkg, name), invars, cmInv, state1)
      b.map(s => s.copy(callStack = if(s.callStack.isEmpty) Nil else s.callStack.tail, nextCmd = None))
    case (CallbackMethodInvoke(_, _, _), targetLoc@CallbackMethodReturn(_,_,mloc, _)) =>
      // Case where execution goes to the exit of another callback
      // TODO: nested callbacks not supported yet, assuming we can't go back to callin entry
      // TODO: note that the callback method invoke is to be ignored here.
      // Control flow resolver is responsible for the
      val appLoc = AppLoc(targetLoc.loc, targetLoc.line.get,isPre = false)
      val rvar = w.cmdAtLocation(appLoc) match{
        case ReturnCmd(v,_) =>v
        case c => throw new IllegalStateException(s"return from non return command $c ")
      }
      val newFrame = CallStackFrame(targetLoc, None, Map())
      val (pkg,name) = msgCmdToMsg(target)
      // Push frame regardless of relevance
      val pre_push = postState.copy(callStack = newFrame::postState.callStack)
      val localVarOrVal: List[Option[RVal]] = rvar::mloc.getArgs
      val relAliases = relevantAliases2(postState, CBExit, (pkg,name),localVarOrVal)
      // Note: no newSpecInstanceTransfer since this is an in-message
      val (rVals, state0) = getOrDefineRVals(relAliases, pre_push)
      val state1 = traceAllPredTransfer(CBExit, (pkg, name), rVals, state0)
      Set(state1)
    case (CallbackMethodReturn(_,_,mloc1,_), AppLoc(mloc2,_,false)) =>
      assert(mloc1 == mloc2)
      assert(postState.nextCmd.isEmpty)
      Set(postState) // transfer handled by processing callbackmethodreturn, nothing to do here
    case (_:InternalMethodInvoke, al@AppLoc(_, _, true)) =>
      val cmd = w.cmdAtLocation(al) match{
        case InvokeCmd(inv : Invoke, _) => inv
        case AssignCmd(_, inv: Invoke, _) => inv
        case c => throw new IllegalStateException(s"Malformed invoke command $c")
      }
      val receiverOption: Option[RVal] = cmd match{
        case v:VirtualInvoke => Some(v.target)
        case s:SpecialInvoke => Some(s.target)
        case _:StaticInvoke => None
      }
      val argOptions: List[Option[RVal]] = cmd.params.map(Some(_))
      val state0 = postState.setNextCmd(None)
      val receiverValueOption = state0.get(LocalWrapper("@this","_"))
      val frameArgVals: List[Option[PureExpr]] =
        (0 until cmd.params.length).map(i => state0.get(LocalWrapper(s"@parameter$i", "_"))).toList
      val allArgs = receiverOption :: argOptions
      val allParams: Seq[Option[PureExpr]] = (receiverValueOption::frameArgVals)
      val argsAndVals: List[(Option[RVal], Option[PureExpr])] = allArgs zip allParams
      // Possible stack frames for source of call being a callback or internal method call
      val out = if (postState.callStack.size == 1) {
        val newStackFrames: List[CallStackFrame] =
          BounderUtil.resolveMethodReturnForAppLoc(resolver, al).map(mr => CallStackFrame(mr, None, Map()))
        val newStacks = newStackFrames.map(frame => frame :: (if (postState.callStack.isEmpty) Nil else postState.callStack.tail))
        val nextStates = newStacks.map(newStack => postState.copy(callStack = newStack))
        nextStates.map(nextState => defineVarsAs(nextState, argsAndVals)).toSet
      }else if (postState.callStack.size > 1){
        val state1 = postState.copy(callStack = postState.callStack.tail)
        Set(defineVarsAs(state1, argsAndVals))
      }else{
        throw new IllegalStateException("Abstract state should always have a " +
          "stack when returning from internal method.")
      }
      out
    case (retloc@AppLoc(mloc, line, false), mRet: InternalMethodReturn) =>
      val retVal:Map[StackVar, PureExpr] = w.cmdAtLocation(retloc) match{
        case AssignCmd(tgt, _:Invoke, _) =>
          postState.get(tgt).map(v => Map(StackVar("@ret") -> v)).getOrElse(Map())
        case InvokeCmd(_,_) => Map()
        case _ => throw new IllegalStateException(s"malformed bytecode, source: $retloc  target: $mRet")
      }
      // Create call stack frame with return value
      // TODO: add @this to prove non-static invokes faster
      val newFrame = CallStackFrame(mRet, Some(AppLoc(mloc,line,true)), retVal)
      Set(postState.copy(callStack = newFrame::postState.callStack, nextCmd = None))
    case (mr@InternalMethodReturn(_,_,_), cmd@AppLoc(_,_,false)) =>
      w.cmdAtLocation(cmd) match{
        case ReturnCmd(_,_) => Set(postState)
        case _ => throw new IllegalStateException(s"malformed bytecode, source: $mr  target: ${cmd}")
      }
    case (_:AppLoc, _:InternalMethodInvoke) => Set(postState)
    case t =>
      println(t)
      ???
  }

  private def inVarsForCall(i:Invoke):List[Option[RVal]] = i match{
    case i@VirtualInvoke(tgt, _, _, _) =>
      Some(tgt) :: i.params.map(Some(_))
    case i@SpecialInvoke(tgt, _, _, _) =>
      Some(tgt) :: i.params.map(Some(_))
    case i@StaticInvoke(_, _, _) =>
      None :: i.params.map(Some(_))
  }
  private def inVarsForCall(source: AppLoc):List[Option[RVal]] = {
    w.cmdAtLocation(source) match {
      case AssignCmd(local : LocalWrapper, i:Invoke, _) =>
        Some(local) :: inVarsForCall(i)
      case InvokeCmd(i: Invoke, _) =>
        None :: inVarsForCall(i)
      case v =>
        println(v) //Note: jimple should restrict so that assign only occurs to locals from invoke
        ???
    }
  }

  /**
   * For a back message with a given package and name, instantiate each rule as a new trace abstraction
   *
   * @param loc callback invoke or callin return
   * @param postState state at point in app just before back message
   * @return a new trace abstraction for each possible rule
   */
  def newSpecInstanceTransfer(mt: MessageType,
                              sig:(String,String), allVar:List[Option[RVal]],
                              loc: Loc, postState: State): Set[State] = {
    val specsBySignature: Set[LSSpec] = specSpace.specsBySig(mt, sig._1, sig._2)


    val postStatesByConstAssume: Set[(LSSpec,State)] = specsBySignature.flatMap{ (s:LSSpec) =>
      val cv = s.target.constVals(s.rhsConstraints) zip allVar
      val definedCv: Seq[(PureExpr,CmpOp ,RVal)] = cv.flatMap{
        case (None,_) => None
        case (_,None) => None
        case (Some((op,cv)), Some(stateVar)) => Some((cv,op,stateVar))
      }
      if(definedCv.isEmpty) {
        // Spec does not assume any constants
        Set((s,postState))
      } else {
        // TODO: this has been changed so that if a spec exists,
        //  we assume that the negation also exists or is just false
        // Constants are assumed, split into cases
        //    1. where all const matches rhs of lifestate rule and
        //    2. where at least one const does not match
        val posState: State = definedCv.foldLeft(postState) {
          case (st, (pureExpr, op,stateVar)) =>
            val (vv, st1) = st.getOrDefine(stateVar)
            st1.copy(pureFormula = st.pureFormula + PureConstraint(vv, op, pureExpr))
        }
//        val negStates: Set[State] = definedCv.map {
//          case (pureExpr, stateVar) =>
//            val (vv, st1) = postState.getOrDefine(stateVar)
//            st1.copy(pureFormula = postState.pureFormula + PureConstraint(vv, NotEquals, pureExpr))
//        }.toSet

//        val negSpec = s.copy(pred=Not(s.pred))
//        val notSpec: Set[(LSSpec, State)] = negStates.map((negSpec,_))
//        val out = notSpec.+((s,posState))
        val out = Set((s,posState))
        out
      }
    }

    // If no lifestate rules match, no new specs are instantiated
    if(postStatesByConstAssume.isEmpty)
      return Set(postState)

    // For each applicable state and spec,
    //  instantiate ls variables in both the trace abstraction and abstract state
    postStatesByConstAssume.map {
      case (LSSpec(pred, target,_), newPostState) =>
        val parameterPairing: Seq[(String, Option[RVal])] = target.lsVars zip allVar

        // Define variables in rule in the state
        val state2 = parameterPairing.foldLeft(newPostState) {
          case (cstate, (LSAnyVal(), _)) => cstate
          case (cstate, (LSConst(_), _)) => cstate
          case (cstate, (_, Some(rval))) => cstate.getOrDefine(rval)._2
          case (cstate, _) => cstate
        }
        val lsVarConstraints = parameterPairing.flatMap {
          case (LSAnyVal(), _) => None
          case (LSVar(k), Some(l: LocalWrapper)) =>
            Some((k, state2.get(l).get))
          case (_, None) => None
          case (LSConst(_), Some(_: LocalWrapper)) => None
          case (k, v) =>
            println(k)
            println(v)
            ??? //TODO: handle primitives e.g. true "string" 1 2 etc
        }
        // Match each lsvar to absvar if both exist
        val newLsAbstraction = AbstractTrace(pred, Nil, lsVarConstraints.toMap)
        state2.copy(traceAbstraction = state2.traceAbstraction + newLsAbstraction)
    }
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
  def predTransferTrace(pred:AbstractTrace, mt:MessageType,
                        sig:(String,String),
                        vals: List[Option[PureExpr]]):AbstractTrace = {
    if (pred.a.contains(mt,sig)) {
      specSpace.getIWithFreshVars(mt, sig) match {
        case Some(i@I(_, _, lsVars)) =>
          val modelVarConstraints: Map[String, PureExpr] = (lsVars zip vals).flatMap {
            case (LSVar(lsVar), Some(stateVal)) => Some((lsVar, stateVal))
            case _ => None //TODO: cases where transfer needs const values (e.g. setEnabled(true))
          }.toMap
          assert(!modelVarConstraints.isEmpty) //TODO: can this ever happen?
          assert(pred.modelVars.keySet.intersect(modelVarConstraints.keySet).isEmpty,
            "Previous substitutions must be made so that comflicting model " +
              "var constraints aren't added to trace abstraction")
          AbstractTrace(pred.a,
            i :: pred.rightOfArrow, pred.modelVars ++ modelVarConstraints)
        case None => pred
      }
    } else pred
  }

  /**
   * Update each trace abstraction in an abstract state
   * @param allVal values to apply transfer with
   * @return
   */
  def traceAllPredTransfer(mt: MessageType,
                           sig:(String,String), allVal:List[Option[PureExpr]],
                           postState: State):State = {
    // values we want to track should already be added to the state
//    val allVal = alvar.map(_.flatMap(postState.get(_)))
    val newTraceAbs: Set[AbstractTrace] = postState.traceAbstraction.map {
      traceAbs => predTransferTrace(traceAbs, mt, sig, allVal)
    }
    postState.copy(traceAbstraction = newTraceAbs)
  }

  def pureCanAlias(pv:PureVar, otherType:String, state:State):Boolean =
    classHierarchyConstraints.typeSetForPureVar(pv,state).contains(otherType)

  def cmdTransfer(cmd:CmdWrapper, state:State):Set[State] = cmd match{
    case AssignCmd(lhs:LocalWrapper, TopExpr(_),_) => Set(state.clearLVal(lhs))
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
        if (state2.containsLocal(rhs)) {
          // rhs constrained by refutation state, lhs should be equivalent
          Set(state2.copy(pureFormula = state2.pureFormula + PureConstraint(pexpr,Equals, state2.get(rhs).get)))
        } else{
          // rhs unconstrained by refutation state, should now be same as lhs
          val state3 = state2.defineAs(rhs, pexpr)
          Set(state3)
        }
      }).getOrElse{
        Set(state) // if lhs points to nothing, no change in state
      }
    case ReturnCmd(Some(v), _) =>
      val fakeRetLocal = LocalWrapper("@ret", "_")
      val retv = state.get(fakeRetLocal)
      val state1 = state.clearLVal(fakeRetLocal)
      Set(retv.map(state1.defineAs(v, _)).getOrElse(state))
    case ReturnCmd(None, _) => Set(state)
    case AssignCmd(lhs:LocalWrapper, FieldReference(base, fieldType, _, fieldName), _) =>
      // x = y.f
      state.get(lhs) match{
        case Some(lhsV) =>{
          val (basev, state1) = state.getOrDefine(base)
          // get all heap cells with correct field name that can alias
          val possibleHeapCells = state1.heapConstraints.filter {
            case (FieldPtEdge(pv, heapFieldName), _) =>
              val fieldEq = fieldName == heapFieldName
              val canAlias = pureCanAlias(pv,base.localType,state1)
              fieldEq && canAlias
            case _ =>
              false
          }
          val statesWhereBaseAliasesExisting:Set[State] = possibleHeapCells.map{
            case (FieldPtEdge(p,_), heapV) =>
              state1.copy(pureFormula = state1.pureFormula +
                PureConstraint(basev, Equals, p) +
                PureConstraint(lhsV, Equals, heapV))
            case _ => throw new IllegalStateException()
          }.toSet
          val heapCell = FieldPtEdge(basev, fieldName)
          val stateWhereNoHeapCellIsAliased = state1.copy(
            heapConstraints = state1.heapConstraints + (heapCell -> lhsV),
            pureFormula = state1.pureFormula ++ possibleHeapCells.map{
              case (FieldPtEdge(p,_),_) => PureConstraint(p, NotEquals, basev)
              case _ => throw new IllegalStateException()
            }
          )
          val res = statesWhereBaseAliasesExisting + stateWhereNoHeapCellIsAliased
          res.map(s => s.clearLVal(lhs))
        }
        case None => Set(state)
      }
    case AssignCmd(FieldReference(base, fieldType, _,fieldName), rhs, _) =>
      // x.f = y
      val (basev,state2) = state.getOrDefine(base)

      // get all heap cells with correct field name that can alias
      val possibleHeapCells = state2.heapConstraints.filter {
        case (FieldPtEdge(pv, heapFieldName), _) =>
          val fieldEq = fieldName == heapFieldName
          val canAlias = pureCanAlias(pv,base.localType,state2)
          fieldEq && canAlias
        case _ =>
          false
      }

      // Get or define right hand side
      val possibleRhs = Set(state2.getOrDefine2(rhs))
      // get or define base of assignment
      // Enumerate over existing base values that could alias assignment
      // Enumerate permutations of heap cell and rhs
      // TODO: remove repeatingPerm here since only one possible rhs
      val perm = BounderUtil.repeatingPerm(a => if(a ==0) possibleHeapCells else possibleRhs , 2)
      val casesWithHeapCellAlias: Set[State] = perm.map{
        case (pte@FieldPtEdge(heapPv, _), tgtVal:PureExpr)::(rhsPureExpr:PureExpr,state3:State)::Nil =>
          val withPureConstraint = state3.copy(pureFormula = state3.pureFormula + PureConstraint(basev, Equals, heapPv))
          val swapped = withPureConstraint.copy(
            heapConstraints = withPureConstraint.heapConstraints - pte,
            pureFormula = withPureConstraint.pureFormula +
              PureConstraint( tgtVal, Equals, rhsPureExpr) +
              PureConstraint(heapPv, NotEquals, NullVal) // Base must be non null for normal control flow
          )
          swapped
        case v =>
          println(v)
          ???
      }.toSet
      val caseWithNoAlias = state2.copy(pureFormula = state2.pureFormula ++ possibleHeapCells.flatMap{
        case (FieldPtEdge(pv, _),_) => Some(PureConstraint(basev, NotEquals, pv))
        case _ => None
      })
      casesWithHeapCellAlias + caseWithNoAlias
    case AssignCmd(target :LocalWrapper, source, _) if source.isConst =>
      state.get(target) match{
        case Some(v) =>
          val src = Set(state.getOrDefine2(source))
          src.map{
            case (pexp, s2) => s2.copy(pureFormula = s2.pureFormula + PureConstraint(v, Equals, pexp)).clearLVal(target)
          }
        case None => Set(state)
      }
    case _:InvokeCmd => Set(state)// Invoke not relevant and skipped
    case AssignCmd(_, _:Invoke, _) => Set(state)
    //TODO: handle if, when transfering over if, assume b was true.
      // Note: ignoring if stmts is sound but not precise
      // TODO: needed info about where control flow came from. If statement is encountered on both branches through the unit graph
    case If(b,trueLoc,_) =>
      assert(state.nextCmd.isDefined, "Malformed transfer, next command must be defined to transfer If node.")
      val stateLocationFrom: AppLoc = state.nextCmd.get
      if(stateLocationFrom == trueLoc)
        assumeInState(b,state,negate=false).toSet
      else
        assumeInState(b,state,negate=true).toSet
    case AssignCmd(l,Cast(castT, local),cmdloc) =>
      val state1 = state.get(local) match{
        case Some(v) => state.copy(pureFormula = state.pureFormula + PureConstraint(v, TypeComp, SubclassOf(castT)))
        case None => state
      }
      cmdTransfer(AssignCmd(l,local,cmdloc),state1)
    case AssignCmd(l:LocalWrapper, StaticFieldReference(declaringClass, fname, containedType), _) =>
      if(state.containsLocal(l)){
        val v = state.get(l).get
        val state1 = state.clearLVal(l)
        Set(state1.copy(heapConstraints = state1.heapConstraints + (StaticPtEdge(declaringClass,fname) -> v),
          pureFormula = state1.pureFormula + PureConstraint(v, TypeComp, SubclassOf(containedType))
        ))
      }else Set(state)
    case AssignCmd(StaticFieldReference(declaringClass,fieldName,_), l,_) =>
      val edge = StaticPtEdge(declaringClass, fieldName)
      if(state.heapConstraints.contains(edge)){
        val v = state.heapConstraints(edge)
        val state1 = state.defineAs(l, v)
        Set(state1.copy(heapConstraints = state1.heapConstraints - edge))
      }else Set(state)
    case NopCmd(_) => Set(state)
    case ThrowCmd(v) => Set() //TODO: implement exceptional control flow
    case SwitchCmd(_,targets,_) => //TODO: precise implementation of switch
      targets.foldLeft(Set[State]()){
        case (acc, cmd) => acc ++ cmdTransfer(cmd, state)
      }
    case AssignCmd(lhs:LocalWrapper, ArrayReference(base, index),_) =>
      state.get(lhs) match{
        case Some(v) =>
          val (basev,state1) = state.getOrDefine(base)
          val (indexv,state2) = state1.getOrDefine(index)
          val arrayRef = ArrayPtEdge(basev, indexv)
          Set(state2.copy(heapConstraints = state2.heapConstraints + (arrayRef -> v)).clearLVal(lhs))
        case None => Set(state)
      }
    case AssignCmd(ArrayReference(base,index), lhs:LocalWrapper,_) =>
      val possibleAliases = state.heapConstraints.filter{
        case (ArrayPtEdge(basev,_),_) => true
        case _ => false
      }
      if (possibleAliases.isEmpty)
        Set(state)
      else
        ???

    case AssignCmd(lhs:LocalWrapper, ArrayLength(l),_) =>
      state.get(lhs) match{
        case Some(v) =>
          ???
        case None => Set(state)
      }
    case AssignCmd(_:LocalWrapper, CaughtException(_), _) =>
      Set[State]() //TODO: handle exceptional control flow
    case AssignCmd(lhs:LocalWrapper, Binop(_,_,_),_) if state.get(lhs).isEmpty =>
      Set(state) // lhs of binop is not defined
    case AssignCmd(lhs:LocalWrapper, Binop(_,_,_), _) =>
      // TODO: sound to drop constraint, add precision when necessary
      Set(state.clearLVal(lhs))
    case AssignCmd(lhs:LocalWrapper, InstanceOf(clazz, target),_) =>
      // TODO: sound to drop constraint, handle instanceof when needed
      state.get(lhs) match{
        case Some(v) => Set(state.clearLVal(lhs))
        case None => Set(state)
      }
    case c =>
      println(c)
      ???
  }

  private def getOrDefineRVals(rhs:List[Option[RVal]], state:State): (List[Option[PureExpr]], State) ={
    rhs.foldRight((List[Option[PureExpr]](),state)){
      case (Some(rval),(vlist,cstate)) =>
        val (pexp,nstate) = cstate.getOrDefine2(rval)//enumerateAliasesForRVal(rval,cstate)
        (Some(pexp)::vlist, nstate)
      case (None,(vlist,cstate)) => (None::vlist, cstate)
    }
  }


  def assumeInState(bExp:RVal, state:State, negate: Boolean): Option[State] = bExp match{
    case BoolConst(b) if b != negate => Some(state)
    case BoolConst(b) if b == negate => None
    case Binop(v1, op, v2) =>
      val (v1Val,state0) = state.getOrDefine2(v1)
      val (v2Val,state1) = state0.getOrDefine2(v2)
      //TODO: Handle boolean expressions, integer expressions, etc
      // it is sound, but not precise, to drop constraints
      Some((op, negate) match{
        case (Eq,false) => state1.copy(pureFormula = state1.pureFormula + PureConstraint(v1Val, Equals, v2Val))
        case (Ne,false) => state1.copy(pureFormula = state1.pureFormula + PureConstraint(v1Val, NotEquals, v2Val))
        case (Eq,true) => state1.copy(pureFormula = state1.pureFormula + PureConstraint(v1Val, NotEquals, v2Val))
        case (Ne,true) => state1.copy(pureFormula = state1.pureFormula + PureConstraint(v1Val, Equals, v2Val))
        case _ => state
      })
    case v =>
      throw new IllegalStateException(s"Invalid rval for assumeInState: $v")
  }
}
