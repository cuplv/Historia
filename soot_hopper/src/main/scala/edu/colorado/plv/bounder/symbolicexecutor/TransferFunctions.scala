package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.{I, LSSpec}
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.symbolicexecutor.TransferFunctions.relevantAliases
import edu.colorado.plv.bounder.symbolicexecutor.state._

object TransferFunctions{
  /**
   * Get set of things that if aliased, change the trace abstraction state
   * @param pre state before cmd that emits an observed message
   * @param dir callback/callin entry/exit
   * @param signature class and name of method
   * @return
   */
  def relevantAliases(pre: State,
                      dir: MessageType,
                      signature: (String, String)) :Set[List[LSParamConstraint]]  = {
    val relevantI = pre.findIFromCurrent(dir, signature)
    relevantI.map{
      case (I(_, _, vars),p)=> p
    }
  }
}

class TransferFunctions[M,C](w:IRWrapper[M,C], specSpace: SpecSpace) {
  def defineVarsAs(state: State, comb: List[(Option[RVal], LSParamConstraint)]):State = {
    comb.foldLeft(state){
      case (state, (Some(l:LocalWrapper), LSPure(v:PureVar))) =>
        val (oldLocVal,state2) = state.getOrDefine(l)
        state2.swapPv(oldLocVal, v)
      case (state, (Some(l:LocalWrapper), LSPure(v))) =>
        println(v) //TODO: other kinds of v
        ???
      case (state, (Some(l:LocalWrapper), LSModelVar(v,ta))) =>
        val (oldLocVal,state2) = state.getOrDefine(l)
        assert(state2.traceAbstraction.contains(ta), "model var constraint not contained in current state")
        state2.copy(traceAbstraction = (state2.traceAbstraction - ta) + ta.addModelVar(v,oldLocVal) )
      case (state, (Some(NullConst), _)) => ??? //TODO: These cases shouldn't come up until const values are added to ls
      case (state, (Some(l:BoolConst), _)) => ???
      case (state, (Some(l:IntConst), _)) => ???
      case (state, (Some(l:StringConst), _)) => ???
      case (statemap, (_, _)) => statemap
    }
  }
  def statesWhereOneVarNot(state: State, comb: List[(Option[RVal], LSParamConstraint)]): Set[State] = {
    comb.toSet.flatMap{(a:(Option[RVal], LSParamConstraint)) => a match{
      case (None, _) => None
      case (_,LSAny) => None
      case (Some(l), LSPure(pv)) =>
        val (locval,state0)  = state.getOrDefine(l)
        Some(state0.copy(pureFormula = state0.pureFormula + PureConstraint(locval, NotEquals, pv)))
      case (Some(l), LSModelVar(mv,ta)) =>
        val (locval, state0) = state.getOrDefine(l)
        val (pv :PureVar, state1:State) = state0.nextPv()
        assert(state1.traceAbstraction.contains(ta), "model var constraint not contained in current state")
        Some(state1.copy(
          traceAbstraction = (state1.traceAbstraction - ta) + ta.addModelVar(mv,pv),
          pureFormula = state1.pureFormula + PureConstraint(pv, NotEquals, locval)
        ))
    }}
  }

  /**
   *
   * @param pre state before current location
   * @param target predecessor of current location
   * @param source current location
   * @return set of states that may reach the target state by stepping from source to target
   */
  def transfer(pre: State, target: Loc, source: Loc): Set[State] = (source, target, pre) match {
    case (source@AppLoc(_, _, false), cmret@CallinMethodReturn(_, _), preState) =>
      // traverse back over the retun of a callin
      // "Some(source.copy(isPre = true))" places the entry to the callin as the location of call
      //TODO:relevant transition enumeration
      val (pkg, name) = msgCmdToMsg(cmret)
      val relAliases: Set[List[LSParamConstraint]] = relevantAliases(pre, CIExit, (pkg,name))
      val frame = CallStackFrame(target, Some(source.copy(isPre = true)), Map())
      val ostates = if(relAliases.isEmpty){
        Set(pre)
      }else {
        val invars: List[Option[RVal]] = inVarsForCall(source)
        // add all args except assignment to state
        val state0 = defineVars(preState, invars.tail)
        val state1 = traceAllPredTransfer(CIExit, (pkg, name), invars, state0)
        val states2 = newSpecInstanceTransfer(CIExit, (pkg, name), invars, cmret, state1)

        // clear assigned var from stack if exists
        val states3 = invars.head.map {
          case localWrapper: LocalWrapper => states2.clearLVal(localWrapper)
          case _ => states2
        }.getOrElse(states2)
        println(???) //TODO
//        Set(states3.copy(callStack = frame :: preState.callStack))
        Set(states3)
      }
      ostates.map(a => a.copy(callStack = frame::a.callStack))
    case (CallinMethodReturn(_, _), CallinMethodInvoke(_, _), state) => Set(state)
    case (cminv@CallinMethodInvoke(_, _), ciInv@AppLoc(_, _, true), s@State(_ :: t, _, _, _,_)) =>
      //TODO: relevant transition enumeration
       val (pkg,name) = msgCmdToMsg(cminv)
      val relAliases: Set[List[LSParamConstraint]] = relevantAliases(pre, CIEnter, (pkg,name))
      val ostates = if(relAliases.isEmpty)
        Set(pre)
      else {
        println(???) //TODO: enumerate aliases
        val invars = inVarsForCall(ciInv)
        val state0 = defineVars(s, invars.tail)
        val state1 = traceAllPredTransfer(CIEnter, (pkg, name), invars, state0)
//        val states2 = newSpecInstanceTransfer(CIExit, (pkg, name), invars, ciInv, state1)
//        Set(states2.copy(callStack = t))
//        ???
        Set(state1)
        ???
      }
      ostates.map(s => s.copy(if (s.callStack.isEmpty) Nil else s.callStack.tail))
    case (AppLoc(_, _, true), AppLoc(_, _, false), pre) => Set(pre)
    case (appLoc@AppLoc(c1, m1, false), AppLoc(c2, m2, true), prestate) if c1 == c2 && m1 == m2 =>
      cmdTransfer(w.cmdAtLocation(appLoc), prestate)
    case (AppLoc(containingMethod, m, true), cmInv@CallbackMethodInvoke(fc1, fn1, l1), pre) => {
      // If call doesn't match return on stack, return bottom
      // Target loc of CallbackMethodInvoke means just before callback is invoked
      if(pre.callStack.nonEmpty){
        pre.callStack.head match {
          case CallStackFrame(CallbackMethodReturn(fc2,fn2,l2,_),_,_) if fc1 != fc2 || fn1 != fn2 || l1 != l2 =>
            ???
            return Set()//TODO: does this ever happen with callback entry? (remove ??? when this is figured out)
          case _ =>
        }
      }

      val (pkg, name) = msgCmdToMsg(cmInv)
      val relAliases: Set[List[LSParamConstraint]] = relevantAliases(pre, CBEnter, (pkg,name))
      val ostates = if (relAliases.isEmpty){
        Set(pre)
      }else {
        val invars: List[Option[LocalWrapper]] = None :: containingMethod.getArgs
        relAliases.flatMap(relAliases =>{
          val comb = invars zip relAliases
          val state0 = defineVarsAs(pre, comb)
          val state1 = traceAllPredTransfer(CBEnter, (pkg,name), invars, state0)
          val otherStates = statesWhereOneVarNot(pre, comb)
          otherStates + state1
        })
      }
      ostates.map(a => {
        val invars: List[Option[LocalWrapper]] = None :: containingMethod.getArgs
        val c = defineVars(a, invars)
        val b = newSpecInstanceTransfer(CBEnter, (pkg, name), invars, cmInv, c)
        b.copy(callStack = if(a.callStack.isEmpty) Nil else a.callStack.tail)
      })
    }
    case (CallbackMethodInvoke(_, _, _), targetLoc@CallbackMethodReturn(_,_,mloc, _), pre) => {
      // Case where execution goes to the exit of another callback
      // TODO: nested callbacks not supported yet, assuming we can't go back to callin entry
      // TODO: note that the callback method invoke is to be ignored here.
      // Control flow resolver is responsible for the
      val appLoc = AppLoc(targetLoc.loc, targetLoc.line.get,false)
      val rvar = w.cmdAtLocation(appLoc) match{
        case ReturnCmd(v,_) =>v
        case c => throw new IllegalStateException(s"return from non return command $c ")
      }
      val newFrame = CallStackFrame(appLoc, None, Map())
      val (pkg,name) = msgCmdToMsg(target)
      // Push frame regardless of relevance
      val pre_push = pre.copy(callStack = newFrame::pre.callStack)
      val relAliases: Set[List[LSParamConstraint]] = relevantAliases(pre, CBExit, (pkg,name))
      val localVarOrVal: List[Option[RVal]] = rvar::mloc.getArgs
      // Note: no newSpecInstanceTransfer since this is an in-message
      if(relAliases.isEmpty){
        Set(pre_push)
      }else {
        relAliases.flatMap( aliases => {
          val comb = localVarOrVal zip aliases

          // State where all local vars are aliased with required
//          val state0 = defineVars(pre_push, localVarOrVal)
          val state0 = defineVarsAs(pre_push, comb)
          val state1 = traceAllPredTransfer(CBExit, (pkg, name), localVarOrVal, state0)

          // States where at least one var is not aliased with required
          val otherStates:Set[State] = statesWhereOneVarNot(pre_push, comb)
          otherStates + state1
        })
      }
    }
    case (CallbackMethodReturn(_,_,mloc1,_), AppLoc(mloc2,_,_), state) =>
      assert(mloc1 == mloc2) ; Set(state) // transfer handled by processing callbackmethodreturn, nothing to do here
    case (InternalMethodInvoke(clazz, name, loc), AppLoc(mloc, line, false), state) =>
      println()
      ???
    case (retloc@AppLoc(mloc, line, false), mRet@InternalMethodReturn(clazz, name, loc), state) =>
      // Create call stack frame with empty
      val retVal:Map[StackVar, PureExpr] = w.cmdAtLocation(retloc) match{
        case AssignCmd(tgt, _:InvokeCmd, _) => state.get(tgt).map(v => Map(StackVar("@ret") -> v)).getOrElse(Map())
        case InvokeCmd(_,_) => Map()
        case _ => throw new IllegalStateException(s"malformed bytecode, source: $retloc  target: $mRet")
      }
      val newFrame = CallStackFrame(mRet, Some(AppLoc(mloc,line,true)), retVal)
      Set(state.copy(callStack = newFrame::state.callStack))
    case (mr@InternalMethodReturn(_,_,_), cmd@AppLoc(_,_,_),state) =>
      // TODO: case where return value is important
      w.cmdAtLocation(cmd) match{
        case ReturnCmd(_,_) => Set(state)
        case _ => throw new IllegalStateException(s"malformed bytecode, source: $mr  target: ${cmd}")
      }
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

  private def defineVars(pre: State, invars: List[Option[RVal]]) = {
    invars.foldLeft(pre) {
      case (cstate, Some(invar : LocalWrapper)) =>
        cstate.getOrDefine(invar)._2
      case (cstate, _) => cstate
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
                              loc: Loc, postState: State): State = {
    //TODO: last element is list of varnames, should probably use that
    val specOpt = specSpace.specsBySig(mt,sig._1,sig._2)

    // Split spec into pred and target if it exists, otherwise pre state is post state
    val (pred, target) = specOpt match{
      case Some(LSSpec(pred, target)) => (pred,target)
      case None => return postState
    }

    val parameterPairing: Seq[(String, Option[RVal])] = (target.lsVars zip allVar)

    // Match each lsvar to absvar if both exist
    val newLsAbstraction = AbstractTrace(pred, Nil, parameterPairing.flatMap{
      case (k,_) if k == "_" => None
      case (k,Some(l : LocalWrapper)) =>
        Some((k,postState.get(l).get))
      case (_,None) => None
      case (k,v) =>
        println(k)
        println(v)
        ??? //TODO: handle primitives e.g. true "string" 1 2 etc
    }.toMap)
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
  def predTransferTrace(pred:AbstractTrace, mt:MessageType,
                        sig:(String,String),
                        vals: List[Option[PureExpr]]):AbstractTrace = {
    if (pred.a.contains(mt,sig)) {
      specSpace.getIWithFreshVars(mt, sig) match {
        case Some(i@I(_, _, lsVars)) =>
          val modelVarConstraints = (lsVars zip vals).flatMap {
            case (lsvar, Some(stateVal)) if lsvar != "_" => Some((lsvar, stateVal))
            case _ => None
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
   * @param postState
   * @return
   */
  def traceAllPredTransfer(mt: MessageType,
                           sig:(String,String), alvar:List[Option[RVal]],
                           postState: State):State = {
    // values we want to track should already be added to the state
    val allVal = alvar.map(_.flatMap(postState.get(_)))
    val newTraceAbs: Set[AbstractTrace] = postState.traceAbstraction.map {
      traceAbs => predTransferTrace(traceAbs, mt, sig, allVal)
    }
    postState.copy(traceAbstraction = newTraceAbs)
  }

  def pureCanAlias(pv:PureVar, otherType:String, state:State):Boolean =
    state.pvTypeUpperBound(pv) match{
      case Some(ot) => w.canAlias(otherType, ot)
      case None => true //Assume alias possible with no type constraints
    }
  def possibleAliasesOf(local: LocalWrapper, state:State):Set[PureVar] = {
    //TODO: use this function to enumerate all alias possibilities when stepping into the return point of callback
    //TODO: or possibly whenever encountering an undefined variable? (This seems less ideal right now)
    val stackVars = state.callStack.headOption.map(_.locals.flatMap{
      case (_,v:PureVar) if state.pvTypeUpperBound(v).exists(ot => w.canAlias(local.localType, ot)) =>
        Some(v)
      case _ => None
    }).getOrElse(Set()).toSet
    val traceVars = state.allTraceVar().flatMap{
      case v if pureCanAlias(v, local.localType, state) => Some(v)
      case _ => None
    }
    val heapVars:Set[PureVar] = state.heapConstraints.flatMap{a => a match {
      case (FieldPtEdge(pureVar, _), pureVar2:PureVar) =>
        List(pureVar,pureVar2).filter(pureCanAlias(_,local.localType, state))
      case _ =>
        ???
    }}.toSet
    stackVars.union(traceVars).union(heapVars)
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
      // TODO: enumerate possible aliases
      val lhsv = state.get(lhs) // Find what lhs pointed to if anything
      lhsv.map(pexpr =>{
        // remove lhs from abstract state (since it is assigned here)
        val state2 = state.clearLVal(lhs)
        if (state2.containsLocal(rhs)) {
          // rhs constrained by refutation state, lhs should be equivalent
          val state3 = state2.swapPv(pexpr.asInstanceOf[PureVar], state2.get(rhs).get.asInstanceOf[PureVar])
          Set(state3) // no type constraint added since both existed before hand
        } else{
          // rhs unconstrained by refutation state, should now be same as lhs
          val state3 = state2.defineAs(rhs, pexpr)
          Set(state3)
        }
      }).getOrElse{
        Set(state)
      }
    case AssignCmd(lhs:LocalWrapper, FieldRef(base, fieldtype, declType, fieldName), _) =>
      // x = y.f
      // TODO: enumerate possible aliases
      state.get(lhs) match{
        case Some(lhsV) =>{
          val (basev, state1) = state.getOrDefine(base)
          val heapCell = FieldPtEdge(basev, fieldName)
          val state2 = state1.clearLVal(lhs)
          if (state2.heapConstraints.contains(heapCell))
            Set(state2.swapPv(lhsV.asInstanceOf[PureVar], state2.heapConstraints(heapCell).asInstanceOf[PureVar]))
          else {
            Set(state2.copy(
              heapConstraints = state2.heapConstraints + (heapCell -> lhsV),
              pureFormula = state2.pureFormula + PureConstraint(lhsV, TypeComp, SubclassOf(fieldtype))
            ))
          }
        }
        case None => Set(state)
      }
    case ReturnCmd(Some(v), _) =>
      val fakeRetLocal = LocalWrapper("@ret", "_")
      val retv = state.get(fakeRetLocal)
      val state1 = state.clearLVal(fakeRetLocal)
      Set(retv.map(state1.defineAs(v, _)).getOrElse(state))
    case ReturnCmd(None, _) => Set(state)
    case AssignCmd(FieldRef(base, fieldType, _,fieldName), rhs, _) =>
      // x.f = y
      val (basev,state2) = state.getOrDefine(base)

      // get all heap cells with correct field name
      val possibleHeapCells = state2.heapConstraints.filter {
        case (FieldPtEdge(pv, heapFieldName), _) =>
          val fieldEq = fieldName == heapFieldName
          val canAlias = pureCanAlias(pv,base.localType,state2)
          fieldEq && canAlias
        case other =>
          println(other)
          false
      }

      // Get or define right hand side
      val possibleRhs : Set[(PureExpr,State)] = rhs match{
        case NullConst => Set((NullVal,state2))
        case lw: LocalWrapper =>
          // TODO: make sure thi works
          val posAlias = possibleAliasesOf(lw, state2)
          val (v,state3) = state2.getOrDefine(lw)
          posAlias.map(a => (a,state3.swapPv(v,a)))
        case _ =>
          ??? //TODO: implement other const values
      }
      // get or define base of assignment
      // Enumerate over existing base values that could alias assignment
      // Enumerate permutations of heap cell and rhs
      val perm = BounderUtil.repeatingPerm(a => if(a ==0) possibleHeapCells else possibleRhs , 2)
      val casesWithHeapCellAlias: Set[State] = perm.map{
        case (pte@FieldPtEdge(heapPv, _), tgtVal:PureExpr)::(rhsPureExpr:PureExpr,state3:State)::Nil =>
          val swapped0 = state3.swapPv(basev, heapPv)
          val swapped = swapped0.copy(
            heapConstraints = swapped0.heapConstraints - pte,
            pureFormula = swapped0.pureFormula + PureConstraint(tgtVal, Equals, rhsPureExpr)
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
    case _:InvokeCmd => Set(state)// Invoke not relevant and skipped
    case AssignCmd(_, _:Invoke, _) => Set(state)
    case If(b,_) =>
      Set(assumeInState(b,state))
    case c =>
      println(c)
      ???
  }
  def assumeInState(b:RVal, state:State): State = b match{
    case Binop(l@LocalWrapper(name,_), op, const) if state.containsLocal(l) =>
      ???
    case Binop(l:LocalWrapper,_,const) if !state.containsLocal(l) =>
      assert(!const.isInstanceOf[LocalWrapper])
      state
    case v =>
      println(v)
      ???
  }
}
