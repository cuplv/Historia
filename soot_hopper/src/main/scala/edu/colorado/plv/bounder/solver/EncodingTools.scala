package edu.colorado.plv.bounder.solver

import edu.colorado.plv.bounder.ir.{MessageType, TMessage, TraceElement}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, CLInit, Exists, Forall, FreshRef, HNOE, LSAnyPred, LSAtom, LSBexp, LSConstraint, LSFalse, LSImplies, LSPred, LSSingle, LSSpec, LSTrue, NS, Not, OAbsMsg, Or, SignatureMatcher}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{ArrayPtEdge, CallStackFrame, ConcreteVal, Equals, FieldPtEdge, HeapPtEdge, NPureVar, NamedPureVar, NotEquals, PureConstraint, PureExpr, PureVal, PureVar, State, StaticPtEdge, TopVal}

import scala.collection.mutable

object EncodingTools {

  private def filterAny(s:Seq[(PureExpr,PureExpr)]):Seq[(PureExpr,PureExpr)] = s.filter{
    case (TopVal,_) => false
    case (_,TopVal) => false
    case _ => true
  }
  def eqOnce(i1:AbsMsg, i2:AbsMsg):LSPred =
    if(i1.signatures != i2.signatures || i1.mt != i2.mt)
      LSFalse
    else {
      val pairs = filterAny(i1.lsVars zip i2.lsVars)
      pairs.map(v => LSConstraint.mk(v._1, Equals,v._2)).reduceOption(And).getOrElse(LSTrue)
    }

  private def neqOnce(i1:AbsMsg, i2:AbsMsg):LSPred = {
    if(i1.signatures != i2.signatures || i1.mt != i2.mt)
      LSTrue
    else {
      val pairs = filterAny(i1.lsVars zip i2.lsVars)
      pairs.map(v => LSConstraint.mk(v._1,NotEquals,v._2)).reduceOption(Or).getOrElse(LSTrue)
    }
  }
  private def updArrowPhi(i:AbsMsg, lsPred:LSPred):LSPred = lsPred match {
    case LSAnyPred => LSAnyPred
    case Forall(v,p) => Forall(v,updArrowPhi(i:AbsMsg, p:LSPred))
    case Exists(v,p) => Exists(v,updArrowPhi(i:AbsMsg, p:LSPred))
    case l:LSConstraint => l
    case And(l1, l2) => And(updArrowPhi(i,l1), updArrowPhi(i,l2))
    case Or(l1, l2) => Or(updArrowPhi(i,l1), updArrowPhi(i,l2))
    case LifeState.LSTrue => LifeState.LSTrue
    case LifeState.LSFalse => LifeState.LSFalse
    case LSImplies(l1,l2) => LSImplies(updArrowPhi(i,l1), updArrowPhi(i,l2))
    case FreshRef(v) =>
      throw new IllegalStateException("RefV cannot be updated (encoding handled elsewhere)")
    case HNOE(v,i1,extV) =>
      if(i1.mt == i.mt && i1.signatures == i.signatures){
        val arityOfv = i1.lsVars.indexOf(v)
        val pairs = filterAny(i1.lsVars zip i.lsVars).zipWithIndex
        val out = pairs.map{
          case (v,ind) if ind!=arityOfv =>  LSConstraint.mk(v._1,NotEquals,v._2)
          case (v,_) => LSConstraint.mk(extV, Equals, v._2)
        }.reduceOption(Or).getOrElse(LSTrue)
        And(out,lsPred)
      }else lsPred
    case Not(i1:AbsMsg) =>
      if(i1.mt == i.mt && i1.signatures == i.signatures)
        And(neqOnce(i1,i), lsPred)
      else lsPred
    case ni@NS(i1,i2) =>
      And(Or(eqOnce(i1,i), And(ni, neqOnce(i1,i))), neqOnce(i,i2))
    case i1:AbsMsg =>
      if(i1.mt == i.mt && i1.signatures == i.signatures)
        Or(eqOnce(i1,i), lsPred)
      else lsPred
    case Not(x) =>
      throw new IllegalArgumentException(s"Negation only supported on I, found ${x}")
    case CLInit(_) => ???
  }
  private def updArrowPhi(rhs:LSSingle, lSPred: LSPred):LSPred = rhs match {
    case FreshRef(_) =>
      // Creation of reference (occurs earlier than instantiation)
      lSPred
    case i:AbsMsg => updArrowPhi(i,lSPred)
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
    case OAbsMsg(_,mSig, _) if mSig.matchesClass(sig) => LSFalse
    case i:AbsMsg => i
    case NS(OAbsMsg(_,mSig, _),_) if mSig.matchesClass(sig) => LSFalse
    case ni:NS => ni
    case CLInit(sig2) if sig == sig2 => LSFalse
    case f:FreshRef => f
  }
  private def instArrowPhi(target:LSSingle,specSpace: SpecSpace, includeDis:Boolean,
                           instCount:Map[LSSpec,Int]):(LSPred, Map[LSSpec,Int]) = target match {
    case i:AbsMsg =>
      val applicableSpecsAll: Set[LSSpec] =
        if(includeDis) specSpace.specsByI(i).union(specSpace.disSpecsByI(i)) else specSpace.specsByI(i)
      val (instCountUpd,applicableSpecs) = applicableSpecsAll.foldLeft((instCount, Set[LSSpec]())){
        case ((instCount, specs), cSpec) if !instCount.contains(cSpec) =>
          (instCount, specs + cSpec) // case where spec is disallow
        case ((instCount, specs), cSpec) if instCount(cSpec) > 0 =>
          (instCount + (cSpec -> (instCount(cSpec) - 1)), specs + cSpec)
        case (acc, _) => acc
      }
      val swappedPreds = applicableSpecs.map{s =>
        s.instantiate(i, specSpace)
      }
      val outPred = if(swappedPreds.isEmpty) LSTrue
      else if(swappedPreds.size == 1) swappedPreds.head
      else swappedPreds.reduce(And)
      (outPred, instCountUpd)
    case FreshRef(_) => (LSTrue, instCount)
    case CLInit(_) => (LSTrue,instCount)
  }

  /**
   *
   * @param rhs
   * @param specSpace
   * @param post preds to update in addition to current encode
   * @return
   */
  def rhsToPred(rhs: Seq[LSSingle], specSpace: SpecSpace, post:Set[LSPred] = Set()): Set[LSPred] = {
    var instCount = specSpace.getSpecs.map{s =>(s,3)}.toMap //TODO: get this parameter from somewhere
    rhs.foldRight((post, true)) {
      case (v, (acc, includeDis)) =>
        val updated = acc.map(lsPred => updArrowPhi(v, lsPred))
        val (instantiated, instCountP) = instArrowPhi(v, specSpace, includeDis, instCount)
        instCount = instCountP
        (updated + instantiated, false)
    }._1.filter(p => p != LSTrue)
  }

  /**
   * State in register machine
   * @param id unique integer identifier
   */
  case class Q(id:Int) extends Nameable{
    override def solverName: String = s"Q_${id}"
  }

  /**
   * Transition in register machine
   */
  sealed trait Delta{
    def dst:Q
    def b:LSBexp
  }

  type Assign = Map[PureVar, ConcreteVal]
  case class MDelta(dst:Q, b:LSBexp, m:LSAtom) extends Delta
  case class AnyDelta(dst:Q, b:LSBexp) extends Delta
  case class EpsDelta(dst:Q, b:LSBexp) extends Delta

  case class RegMachine(initQ:Set[Q], delta:Map[Q,Set[Delta]], finalQ:Set[Q]){
    def union(other:RegMachine):RegMachine = {
      ???
    }
    def intersect(other:RegMachine):RegMachine = {
      ???
    }
    def negate():RegMachine = {
      ???
    }
    lazy val allQ = initQ.union(finalQ) ++ delta.flatMap{
      case (q, value) => value.map(delt => delt.dst) + q
    }
    def containsTrace(trace:List[TraceElement])(implicit cha:ClassHierarchyConstraints):Option[Assign] = {
      def iContainsTrace(q:Q, assign:Assign, trace:List[TraceElement]):Option[Assign] = trace match {
        case TMessage(mType, method, args, receiverType)::next =>
          delta(q).view.flatMap {
            case AnyDelta(dst, b) => ???
            case EpsDelta(dst, b) => ???
            case MDelta(dst, b, m:AbsMsg) if m.contains(mType, method.fwkSig.get) =>
              ???
            case _:MDelta => None
          }.headOption
        case Nil => if(finalQ.contains(q)) Some(assign) else None
      }
      //initQ.exists(q => iContainsTrace(q, Map.empty, trace).nonEmpty)
      initQ.view.flatMap{q => iContainsTrace(q,Map.empty, trace)}.headOption
    }
  }
  private val q0 = Q(0)
  private val q1 = Q(1)
  private val q2 = Q(2)
  private def selfAny(q: Q): (Q,Set[Delta]) = q->Set(AnyDelta(q, LSTrue))
  private val topRM = RegMachine(
    Set(q0),
    Map(selfAny(q0)),
    Set(q0))
  private val botRM = RegMachine(Set.empty, Map.empty, Set.empty)
  /**
   * Convert pred to register machine
   */
  def predToRM(pred:LSPred,maxPv:NPureVar): (RegMachine,NPureVar) = pred match {
    case Forall(vars, p) => {
      def allNE(pred:LSPred):Set[LSConstraint] = {
        ???
      }
      def findHN(pred:LSPred):Not = {
        ???
      }
      ???
    }
    case Exists(vars, p) => ???
    case LSImplies(l1, l2) => ???
    case Not(o:AbsMsg) =>
      val init = Set(q0)
      val fin = Set(q0)
      val delt = Map[Q,Set[Delta]](
        q0-> Set(
          MDelta(q1, LSTrue, o),
          MDelta(q0, LSTrue, Not(o))
        )
      )
      (RegMachine(init, delt, fin), maxPv)
    case Not(pred) => throw new IllegalArgumentException("arbitrary negation of pred not supported")
    case Or(l1, l2) =>
      val (rm1,maxPv_) = predToRM(l1, maxPv)
      val (rm2,maxPv__) = predToRM(l2, maxPv_)
      (rm1.union(rm2), maxPv__)
    case And(l1,l2) =>
      val (rm1,maxPv_) = predToRM(l1, maxPv)
      val (rm2,maxPv__) = predToRM(l2, maxPv_)
      (rm1.intersect(rm2), maxPv__)
    case LSTrue => (topRM, maxPv)
    case LSFalse => (botRM, maxPv)
    case o:AbsMsg =>
      val init = Set(q0)
      val fin = Set(q1)
      val delt = Map[Q,Set[Delta]](
        q0 -> Set(
          MDelta(q1, LSTrue, o),
          MDelta(q0, LSTrue, Not(o))
        ),
        selfAny(q1)
      )
      (RegMachine(init, delt, fin), maxPv)
    case NS(i1,i2) => ???
    case FreshRef(v) => ???
  }

  def simplifyPred(pred:LSPred):LSPred = pred match {
    case h:HNOE => h
    case LSAnyPred => LSAnyPred
    case Exists(Nil, p) => simplifyPred(p)
    case Forall(Nil, p) => simplifyPred(p)
    case c:LSConstraint => c
    case Forall(vars, p) =>
      Forall(vars, simplifyPred(p))
    case Exists(vars, p) =>
      Exists(vars, simplifyPred(p))
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
    case OAbsMsg(mt, signatures, lsVars) => Set((mt,signatures))
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
      case Not(l:AbsMsg) => Set()
      case _:HNOE => Set()
      case Or(l1, l2) => mustI(l1).intersect(mustI(l2))
      case LifeState.LSTrue => Set()
      case LifeState.LSFalse => Set()
      case i:AbsMsg => Set(s"I_${i.identitySignature}")
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
      case Not(i:AbsMsg) => Set()
      case _:HNOE => Set()
      case Not(p) => throw new IllegalStateException(s"expected normal form in pred: ${p}")
      case Or(l1, l2) => mayI(l1).union(mayI(l2))
      case LifeState.LSTrue => Set()
      case LifeState.LSFalse => Set()
      case i:AbsMsg => Set(s"I_${i.identitySignature}")
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
          case (acc, PureConstraint(lhs:PureVar, Equals, v:PureVal)) => acc.map{s => s.swapPv(lhs,v)}
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

    // State is infeasible if FreshRef is duplicated
    def freshIsDup(roa: List[LSSingle]):Boolean = roa match {
      case FreshRef(pv)::t => {
        val cDup = t.exists{
          case FreshRef(pv2) => pv==pv2
          case _ => false
        }
        cDup || freshIsDup(t)
      }
      case _::t => freshIsDup(t)
      case Nil => false
    }
    if(freshIsDup(out.sf.traceAbstraction.rightOfArrow))
      return None
    // remove FreshRef where value is never referenced
    val freshRefs = out.sf.traceAbstraction.rightOfArrow.foldLeft(out){
      case (acc,f@FreshRef(pv))  => {
        val sf = acc.sf
        val clrSF = sf.clearFreshRef(f)
        if(clrSF.posPureVars().contains(pv)){
          acc
        }else{
          val a = clrSF.clearNegPvAndConstraints(pv)
          acc.copy(sf=a)
        }
      }
      case (acc,_) => acc
    }
    Some(freshRefs)
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

  private val dummyPv = NPureVar(-10)
  /**
   * Used for groupBy on heap cells to match for entailment or group for widening
   * TODO: may want to expand to type sets at some point to improve efficiency
   * @param cell heap cell and target location
   * @return
   */
  def repHeapCells(cell: (HeapPtEdge, PureExpr)): HeapPtEdge = cell match {
    case (FieldPtEdge(pv, fn), _) => FieldPtEdge(dummyPv, fn)
    case (StaticPtEdge(clazz, fn), _) => StaticPtEdge(clazz, fn)
  }

  def prenexNormalForm(pred: LSPred): LSPred = {

    def mergeQuant(ql1:List[Quant], ql2:List[Quant]):List[Quant] = (ql1,ql2) match{
      case (Nil, ql2) => ql2
      case (ql1, Nil) => ql1
      case ((e:QExists)::t1, ql2) => e::mergeQuant(t1,ql2)
      case (ql1, (e:QExists)::t2) => e::mergeQuant(ql1,t2)
      case (h1::t1, h2::t2) => h1::h2::mergeQuant(t1,t2)
    }

    sealed trait Quant{
      def pv:List[PureVar]
    }
    def doQuant(vars:List[PureVar], defined:Set[PureVar], pred:LSPred):(LSPred,List[PureVar]) ={
      val oldToNew: Map[PureVar, PureVar] =
        vars.map { oldVar =>
          (oldVar -> defined.foldLeft(oldVar) { case (acc, v) => acc.noCollide(v).asInstanceOf[PureVar] }) }.toMap

      (pred.swap(oldToNew.filter{a => a._1 != a._2}),oldToNew.values.toList)
    }
    case class QForall(pv:List[PureVar]) extends Quant
    case class QExists(pv:List[PureVar]) extends Quant
    // renames
    def iLift(pred:LSPred, defined:Set[PureVar]):(LSPred,List[Quant]) = pred match{
      case And(l1,l2) =>
        val (l1s, newQuant1) = iLift(l1,defined)
        val (l2s, newQuant2) = iLift(l2,defined ++ newQuant1.flatMap{f => f.pv})
        (And(l1s,l2s), mergeQuant(newQuant1,newQuant2))
      case Or(l1, l2) =>
        val (l1s, newQuant1) = iLift(l1, defined)
        val (l2s, newQuant2) = iLift(l2, defined ++ newQuant1.flatMap { f => f.pv })
        (Or(l1s, l2s), mergeQuant(newQuant1, newQuant2))
      case Exists(vars,pred) =>
        val (newPred,newPV) = doQuant(vars,defined,pred)
        val (recPred,recQuant) = iLift(newPred, defined ++ newPV)
        (recPred,QExists(newPV)::recQuant)
      case Forall(vars,pred) =>
        val (newPred, newPV) = doQuant(vars, defined, pred)
        val (recPred, recQuant) = iLift(newPred, defined ++ newPV)
        (recPred, QForall(newPV) :: recQuant)
      case o:LSSingle => (o,Nil)
      case n:Not => (n,Nil)
      case l:LSConstraint => (l,Nil)
      case ns:NS => (ns,Nil)
      case LSTrue => (LSTrue, Nil)
      case LSFalse => (LSFalse, Nil)
      case v =>
        println(v)
        ???
    }
    val (newPred, newQuant) = iLift(pred, Set.empty)
    newQuant.reverse.foldLeft(newPred){
      case (acc, QForall(pv)) => Forall(pv,acc)
      case (acc, QExists(pv)) => Exists(pv,acc)
    }
  }

  /**
   * Converts a lifestate logical formula to conjunctive normal form
   *
   * @param pred the logical formula to convert
   * @return an equivalent formula in conjunctive normal form
   */
  def toCNF(pred:LSPred):LSPred = {
    val liftedQuant:LSPred = prenexNormalForm(pred)


    def iCnf(pred:LSPred):LSPred = pred match {
      case _:Exists => throw new IllegalArgumentException("exists and forall should be removed before callign iCnf")
      case _:Forall=> throw new IllegalArgumentException("exists and forall should be removed before callign iCnf")
      case Or(And(p1,p2),p3) => And(Or(p1,p3), Or(p2,p3))
      case Or(p1, And(p2,p3)) => iCnf(Or(And(p2,p3),p1))
      case And(p1,p2) => And(iCnf(p1),iCnf(p2))
      case Or(p1,p2) => Or(iCnf(p1), iCnf(p2))
      case l => l
    }

    def stripQuant(pred:LSPred):(LSPred,LSPred =>LSPred) = pred match{
      case Exists(vars,p) =>
        val (strippedPred, recApp) = stripQuant(p)
        (strippedPred, p => Exists(vars, recApp(p)))
      case Forall(vars, p) =>
        val (strippedPred, recApp) = stripQuant(p)
        (strippedPred, p => Forall(vars, recApp(p)))
      case p => (p, p => p)
    }

    def isCnf(pred:LSPred):Boolean = pred match{
      case _:Exists => throw new IllegalArgumentException("Quant should be removed")
      case _:Forall=> throw new IllegalArgumentException("Quant should be removed")
      case Or(p1, p2) => isCnfOr(p1) && isCnfOr(p2)
      case And(p1,p2) => isCnf(p1) && isCnf(p2)
      case _ => true
    }

    def isCnfOr(pred:LSPred):Boolean = pred match{
      case _: Exists => throw new IllegalArgumentException("Quant should be removed")
      case _: Forall => throw new IllegalArgumentException("Quant should be removed")
      case Or(p1, p2) => isCnfOr(p1) && isCnfOr(p2)
      case And(_,_) => false
      case _ => true
    }

    val (strippedQuant, reapplyQuant) = stripQuant(liftedQuant)
    var predIter = strippedQuant
    while(!isCnf(predIter)){
      predIter = iCnf(predIter)
    }
    reapplyQuant(predIter)
  }
}
