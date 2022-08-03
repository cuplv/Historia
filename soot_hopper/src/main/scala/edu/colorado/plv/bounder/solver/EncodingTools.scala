package edu.colorado.plv.bounder.solver

import edu.colorado.plv.bounder.ir.MessageType
import edu.colorado.plv.bounder.lifestate.LifeState.{And, CLInit, Exists, Forall, FreshRef, LSAtom, LSConstraint, LSFalse, LSImplies, LSPred, LSSingle, LSSpec, LSTrue, NS, Not, Once, Or, SignatureMatcher}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{ArrayPtEdge, CallStackFrame, Equals, FieldPtEdge, NPureVar, NamedPureVar, NotEquals, PureConstraint, PureExpr, PureVal, PureVar, State, StaticPtEdge, TopVal}

object EncodingTools {
  private def filterAny(s:Seq[(PureExpr,PureExpr)]):Seq[(PureExpr,PureExpr)] = s.filter{
    case (TopVal,_) => false
    case (_,TopVal) => false
    case _ => true
  }
  def eqOnce(i1:Once, i2:Once):LSPred =
    if(i1.signatures != i2.signatures || i1.mt != i2.mt)
      LSFalse
    else {
      val pairs = filterAny(i1.lsVars zip i2.lsVars)
      pairs.map(v => LSConstraint.mk(v._1, Equals,v._2)).reduce(And)
    }

  private def neqOnce(i1:Once, i2:Once):LSPred = {
    if(i1.signatures != i2.signatures || i1.mt != i2.mt)
      LSTrue
    else {
      val pairs = filterAny(i1.lsVars zip i2.lsVars)
      pairs.map(v => LSConstraint.mk(v._1,NotEquals,v._2)).reduce(Or)
    }
  }
  private def updArrowPhi(i:Once, lsPred:LSPred):LSPred = lsPred match {
    case Forall(v,p) => Forall(v,updArrowPhi(i:Once, p:LSPred))
    case Exists(v,p) => Exists(v,updArrowPhi(i:Once, p:LSPred))
    case l:LSConstraint => l
    case And(l1, l2) => And(updArrowPhi(i,l1), updArrowPhi(i,l2))
    case Or(l1, l2) => Or(updArrowPhi(i,l1), updArrowPhi(i,l2))
    case LifeState.LSTrue => LifeState.LSTrue
    case LifeState.LSFalse => LifeState.LSFalse
    case LSImplies(l1,l2) => LSImplies(updArrowPhi(i,l1), updArrowPhi(i,l2))
    case FreshRef(v) =>
      throw new IllegalStateException("RefV cannot be updated (encoding handled elsewhere)")
    case Not(i1:Once) =>
      if(i1.mt == i.mt && i1.signatures == i.signatures)
        And(neqOnce(i1,i), lsPred)
      else lsPred
    case ni@NS(i1,i2) =>
      And(Or(eqOnce(i1,i), And(ni, neqOnce(i1,i))), neqOnce(i,i2))
    case i1:Once =>
      if(i1.mt == i.mt && i1.signatures == i.signatures)
        Or(eqOnce(i1,i), lsPred)
      else lsPred
    case Not(_) =>
      throw new IllegalArgumentException("Negation only supported on I")
    case CLInit(_) => ???
  }
  private def updArrowPhi(rhs:LSSingle, lSPred: LSPred):LSPred = rhs match {
    case FreshRef(_) =>
      // Creation of reference (occurs earlier than instantiation)
      lSPred
    case i:Once => updArrowPhi(i,lSPred)
    //    case CLInit(sig) => lSPred //TODO: make all I/NI referencing sig positively "false" =====
    case CLInit(sig) => clInitRefToFalse(lSPred, sig)
  }
  private def clInitRefToFalse(lsPred: LSPred, sig:String):LSPred = lsPred match {
    case lc:LSConstraint => lc
    case Forall(vars, p) => Forall(vars, clInitRefToFalse(p, sig))
    case Exists(vars, p) => Exists(vars, clInitRefToFalse(p, sig))
    case LSImplies(l1, l2) => LSImplies(clInitRefToFalse(l1,sig), clInitRefToFalse(l2,sig))
    case And(l1, l2) => And(clInitRefToFalse(l1,sig), clInitRefToFalse(l2, sig))
    case Not(l) => Not(clInitRefToFalse(l, sig))
    case Or(l1, l2) => Or(clInitRefToFalse(l1,sig), clInitRefToFalse(l2, sig))
    case LifeState.LSTrue => LifeState.LSTrue
    case LifeState.LSFalse => LifeState.LSFalse
    case Once(_,mSig, _) if mSig.matchesClass(sig) => LSFalse
    case i:Once => i
    case NS(Once(_,mSig, _),_) if mSig.matchesClass(sig) => LSFalse
    case ni:NS => ni
    case CLInit(sig2) if sig == sig2 => LSFalse
    case f:FreshRef => f
  }
  private def instArrowPhi(target:LSSingle,specSpace: SpecSpace, includeDis:Boolean):LSPred= target match {
    case i:Once =>
      val applicableSpecs: Set[LSSpec] =
        if(includeDis) specSpace.specsByI(i).union(specSpace.disSpecsByI(i)) else specSpace.specsByI(i)
      val swappedPreds = applicableSpecs.map{s =>
        s.instantiate(i, specSpace)
      }
      if(swappedPreds.isEmpty) LSTrue
      else if(swappedPreds.size == 1) swappedPreds.head
      else swappedPreds.reduce(And)
    case FreshRef(_) => LSTrue
    case CLInit(_) => LSTrue
  }
  def rhsToPred(rhs: Seq[LSSingle], specSpace: SpecSpace): Set[LSPred] = {
    rhs.foldRight((Set[LSPred](), true)) {
      case (v, (acc, includeDis)) =>
        val updated = acc.map(lsPred => updArrowPhi(v, lsPred))
        val instantiated = instArrowPhi(v, specSpace, includeDis)
        (updated + instantiated, false)
    }._1.filter(p => p != LSTrue)
  }
  def simplifyPred(pred:LSPred):LSPred = pred match {
    case LifeState.Exists(Nil, p) => simplifyPred(p)
    case LifeState.Forall(Nil, p) => simplifyPred(p)
    case c@LSConstraint(v1, op, v2) => c
    case LifeState.Forall(vars, p) =>
      LifeState.Forall(vars, simplifyPred(p))
    case LifeState.Exists(vars, p) =>
      LifeState.Exists(vars, simplifyPred(p))
    case LSImplies(_,LSTrue) =>
      LSTrue
    case LSImplies(LSTrue, l2) =>
      simplifyPred(l2)
    case LSImplies(l1, LSFalse) => Not(simplifyPred(l1))
    case LSImplies(l1, l2) =>
      val p1 = simplifyPred(l1)
      val p2 = simplifyPred(l2)
      if(p1 == l1 && p2 == l2)
        LSImplies(p1, p2)
      else
        simplifyPred(LSImplies(p1,p2))
    case And(LSTrue, l2) => simplifyPred(l2)
    case And(l1, LSTrue) => simplifyPred(l1)
    case And(_, LSFalse) => LSFalse
    case And(LSFalse,_) => LSFalse
    case And(l1, l2) =>
      val p1 = simplifyPred(l1)
      val p2 = simplifyPred(l2)
      if(p1 == l1 && p2 == l2)
        And(p1, p2)
      else
        simplifyPred(And(p1,p2))
    case Not(l) => Not(simplifyPred(l))
    case Or(LSFalse, l2) => simplifyPred(l2)
    case Or(l1, LSFalse) => simplifyPred(l1)
    case Or(l1, l2) => Or(simplifyPred(l1), simplifyPred(l2))
    case LifeState.LSTrue => LSTrue
    case LifeState.LSFalse => LSFalse
    case atom: LSAtom =>
      atom
  }
  private def mustISet(s1Pred: LSPred):Set[(MessageType, SignatureMatcher)] = s1Pred match {
    case LSConstraint(v1, op, v2) => Set()
    case Forall(vars, p) => mustISet(p)
    case Exists(vars, p) => mustISet(p)
    case LSImplies(l1, l2) => Set()
    case And(l1, l2) => mustISet(l1).union(mustISet(l2))
    case Not(l) => Set()
    case Or(l1, l2) => mustISet(l1).intersect(mustISet(l2))
    case LifeState.LSTrue => Set()
    case LifeState.LSFalse => Set()
    case CLInit(sig) => Set()
    case FreshRef(v) => Set()
    case Once(mt, signatures, lsVars) => Set((mt,signatures))
    case NS(i1, i2) => mustISet(i1)
  }

  def mustISet(s:State, specSpace: SpecSpace):Set[String] = {
    val pred = rhsToPred(s.traceAbstraction.rightOfArrow, specSpace)
    def mustI(lsPred: LSPred):Set[String] = lsPred match {
      case LSConstraint(v1, op, v2) => Set()
      case Forall(vars, p) => mustI(p)
      case Exists(vars, p) => mustI(p)
      case LSImplies(l1, l2) => Set()
      case And(l1, l2) => mustI(l1).union(mustI(l2))
      case Not(l) => Set()
      case Or(l1, l2) => mustI(l1).intersect(mustI(l2))
      case LifeState.LSTrue => Set()
      case LifeState.LSFalse => Set()
      case i:Once => Set(s"I_${i.identitySignature}")
      case NS(i1,i2) => Set(s"NI_${i1.identitySignature}__${i2.identitySignature}") ++ mustI(i1)
    }
    pred.flatMap(mustI)
  }
  def mayISet(s:State, specSpace: SpecSpace):Set[String] = {
    val pred = rhsToPred(s.traceAbstraction.rightOfArrow, specSpace)
    def mayI(lsPred: LSPred):Set[String] = lsPred match {
      case LSConstraint(v1, op, v2) => Set()
      case Forall(vars, p) => mayI(p)
      case Exists(vars, p) => mayI(p)
      case LSImplies(l1, l2) => Set()
      case And(l1, l2) => mayI(l1).union(mayI(l2))
      case Not(i:Once) => Set()
      case Not(p) => throw new IllegalStateException(s"expected normal form in pred: ${p}")
      case Or(l1, l2) => mayI(l1).union(mayI(l2))
      case LifeState.LSTrue => Set()
      case LifeState.LSFalse => Set()
      case i:Once => Set(s"I_${i.identitySignature}")
      case NS(i1,i2) => Set(s"NI_${i1.identitySignature}__${i2.identitySignature}") ++ mayI(i1)
    }
    pred.flatMap(mayI)
  }

  def reduceStatePureVars(state: State): Option[State] = {
    assert(state.isSimplified, "reduceStatePureVars must be called on feasible state.")
    // TODO: test for trace enforcing that pure vars are equivalent
    def mergePV(state:State,oldPv:PureVar, newPv:PureVar):Option[State] = {
      val pv1tc = state.typeConstraints.get(oldPv)
      val pv2tc = state.typeConstraints.get(newPv)
      val joinedTc = (pv1tc,pv2tc) match{
        case (Some(tc),None) => Some(tc)
        case (None,Some(tc)) => Some(tc)
        case (None,None) => None
        case (Some(tc1),Some(tc2)) =>
          Some(tc1.intersect(tc2))
      }
      joinedTc match{
        case Some(tc) if tc.isEmpty => None
        case Some(tc) => Some(state.swapPv(oldPv,newPv).addTypeConstraint(newPv,tc)) //.copy(typeConstraints = state.typeConstraints + (newPv -> tc)))
        case None => Some(state.swapPv(oldPv,newPv))
      }
    }
    def containsEq(state: State):Boolean = {
      state.pureFormula.exists{
        case PureConstraint(lhs:PureVar, Equals, rhs:PureVar) => true
        case _ => false
      }
    }
    def existsNegation(pc:PureConstraint, state:State):Boolean = pc match{
      case PureConstraint(lhs, Equals, rhs) => state.pureFormula.exists{
        case PureConstraint(lhs1, NotEquals, rhs1) if lhs == lhs1 && rhs == rhs1 => true
        case PureConstraint(lhs1, NotEquals, rhs1) if lhs == rhs1 && rhs == lhs1 => true
        case _ => false
      }
      case PureConstraint(lhs, NotEquals, rhs) => state.pureFormula.exists{
        case PureConstraint(lhs1, Equals, rhs1) if lhs == lhs1 && rhs == rhs1 => true
        case PureConstraint(lhs1, Equals, rhs1) if lhs == rhs1 && rhs == lhs1 => true
        case _ => false
      }
    }
    // Iterate until all equal variables are cleared
    var swappedForSmallerPvOpt:Option[State] = Some(state)

    while(swappedForSmallerPvOpt.isDefined && containsEq(swappedForSmallerPvOpt.get)) {
      swappedForSmallerPvOpt = {
        swappedForSmallerPvOpt.get.pureFormula.foldLeft(Some(swappedForSmallerPvOpt.get): Option[State]) {
          case (Some(acc),pc) if existsNegation(pc,acc) => None
          case (Some(acc), pc@PureConstraint(v1@NPureVar(id1), Equals, v2@NPureVar(id2))) if id1 < id2 =>
            val res = mergePV(acc.removePureConstraint(pc),v2,v1)
            res
          case (Some(acc), pc@PureConstraint(v1@NPureVar(id1), Equals, v2@NPureVar(id2))) if id1 > id2 =>
            //              val res = mergePV(acc.copy(pureFormula = acc.pureFormula - pc), v1, v2)
            val res = mergePV(acc.removePureConstraint(pc), v1,v2)
            res
          case (Some(acc), pc@PureConstraint(v1:NamedPureVar,Equals, v2:NPureVar)) =>
            val res = mergePV(acc.removePureConstraint(pc), v1,v2)
            res
          case (Some(acc), pc@PureConstraint(v1:NPureVar,Equals, v2:NamedPureVar)) =>
            val res = mergePV(acc.removePureConstraint(pc), v2,v1)
            res
          case (Some(acc), pc@PureConstraint(pv1:PureVar, Equals, pv2:PureVar)) if pv1 == pv2 =>
            //            Some(acc.copy(pureFormula = acc.pureFormula - pc))
            Some(acc.removePureConstraint(pc))
          case (acc, PureConstraint(lhs, NotEquals, rhs)) => acc
          case (acc, PureConstraint(_, _, _:PureVal)) => acc
          case (acc, _) =>
            ???
        }
      }
    }

    if(swappedForSmallerPvOpt.isEmpty)
      return None
    val swappedForSmallerPv = swappedForSmallerPvOpt.get
    val allPv = swappedForSmallerPv.pureVars()
    val out = if (allPv.nonEmpty) {
      val maxPvValue = allPv.map {
        case NPureVar(id) => id
        case NamedPureVar(_) => -1
      }.max
      swappedForSmallerPv.copy(nextAddr = maxPvValue + 1)
    } else
      swappedForSmallerPv
    Some(out)
  }

  /**
   * Remove all pure variables that are not reachable from a local, heap edge, or trace constraint
   * TODO: note that this could be optimized by dropping pure variables that are not reachable from a framework "registered" set when quiescent
   * @param state
   * @return
   */
  def gcPureVars(state:State):State = {
    val allPv = state.pureVars()

    // marked pure vars
    val localPVs = state.callStack.flatMap{
      case CallStackFrame(_, _, locals) => locals.collect{case (_,pv:PureVar) => pv}
    }.toSet
    val heapPVs = state.heapConstraints.flatMap{
      case (FieldPtEdge(pv1, _), pv2) => Set(pv1,pv2)
      case (StaticPtEdge(_,_), pv) => Set(pv)
      case (ArrayPtEdge(pv1,pv2),pv3) => Set(pv1,pv2,pv3)
    }.toSet
    val tracePVs = state.traceAbstraction.modelVars
    val markedSet = localPVs ++ heapPVs ++ tracePVs
    // TODO: Currently, pv contains no relations that requires the "mark" phase of
    //  mark and sweep so we just move to sweep.
    //  all sources of heap edges are part of the root set since the framework may point to them.
    if (allPv == markedSet){
      state
    }else {
      state.copy(sf = state.sf.copy(pureFormula = state.pureFormula.filter{
        case PureConstraint(lhs:PureVar, NotEquals, _) if !markedSet.contains(lhs) =>
          false
        case PureConstraint(_, NotEquals, rhs:PureVar) if !markedSet.contains(rhs) =>
          false
        case PureConstraint(lhs, _, rhs) => markedSet.contains(lhs) || markedSet.contains(rhs)
        case _ => true
      }, typeConstraints = state.typeConstraints.filter{
        case (pv,_) => markedSet.contains(pv)
      }))
    }
  }
}
