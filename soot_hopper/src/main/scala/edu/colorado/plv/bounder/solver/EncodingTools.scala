package edu.colorado.plv.bounder.solver

import edu.colorado.plv.bounder.ir.MessageType
import edu.colorado.plv.bounder.lifestate.LifeState.{And, CLInit, Exists, Forall, FreshRef, LSAtom, LSConstraint, LSFalse, LSImplies, LSPred, LSSingle, LSSpec, LSTrue, NS, Not, Once, Or, SignatureMatcher}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{Equals, NotEquals, PureExpr, State, TopVal}

object EncodingTools {
  private def filterAny(s:Seq[(PureExpr,PureExpr)]):Seq[(PureExpr,PureExpr)] = s.filter{
    case (TopVal,_) => false
    case (_,TopVal) => false
    case _ => true
  }
  private def eq(i1:Once, i2:Once):LSPred =
    if(i1.signatures != i2.signatures || i1.mt != i2.mt)
      LSFalse
    else {
      val pairs = filterAny(i1.lsVars zip i2.lsVars)
      pairs.map(v => LSConstraint.mk(v._1, Equals,v._2)).reduce(And)
    }

  private def neq(i1:Once, i2:Once):LSPred = {
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
        And(neq(i1,i), lsPred)
      else lsPred
    case ni@NS(i1,i2) =>
      And(Or(eq(i1,i), And(ni, neq(i1,i))), neq(i,i2))
    case i1:Once =>
      if(i1.mt == i.mt && i1.signatures == i.signatures)
        Or(eq(i1,i), lsPred)
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
}
