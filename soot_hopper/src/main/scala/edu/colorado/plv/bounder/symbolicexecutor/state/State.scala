package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, EncodingTools, Nameable}
import edu.colorado.plv.bounder.ir.{AppLoc, BitTypeSet, BoolConst, CallbackMethodInvoke, CallbackMethodReturn, ClassConst, ConstVal, EmptyTypeSet, IRWrapper, IntConst, InternalMethodInvoke, InternalMethodReturn, LVal, Loc, LocalWrapper, MessageType, MethodLoc, NullConst, RVal, StringConst, TopTypeSet, TypeSet}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecSpace}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, FreshRef, LSPred, LSSingle, LSTrue, NS, Not, OAbsMsg, Or, Signature}
import edu.colorado.plv.bounder.symbolicexecutor.state.State.findIAF
import scalaz.Memo
import upickle.default.{macroRW, ReadWriter => RW}

import scala.annotation.tailrec
import scala.collection.{BitSet, View}

object State {

  def topState:State =
    State(StateFormula(Nil,Map(),Set(),Map(),AbstractTrace(Nil)),0)

  def findIAF(messageType: MessageType, signature: Signature,
              pred: LSPred)(implicit ch:ClassHierarchyConstraints):Set[AbsMsg] = pred match{
    case i@OAbsMsg(mt, sigs, _) if mt == messageType && sigs.matches(signature) => Set(i)
    case NS(i1,i2) => Set(i1,i2).flatMap(findIAF(messageType, signature, _))
    case And(l1,l2) => findIAF(messageType,signature,l1).union(findIAF(messageType,signature,l2))
    case Or(l1,l2) => findIAF(messageType,signature,l1).union(findIAF(messageType,signature,l2))
    case Not(l) => findIAF(messageType, signature, l)
    case _ => Set()
  }
  implicit var rw:RW[State] = macroRW
}

// pureFormula is a conjunction of constraints
// callStack is the call string from thresher paper
//sealed trait TraceAbstractionArrow
case class AbstractTrace(rightOfArrow:List[LSSingle]) extends AnyVal{

  def modelVars:Set[PureVar] = rightOfArrow.flatMap{pred => pred.lsVar}.toSet

  override def toString:String = {
//    val generated = modelVars.filter{case (k,_) => LifeState.LSGenerated.matches(k) }
//    val notGenerated = modelVars.removedAll(generated.keySet)
//    val replace: String => String = str => generated.foldLeft(str){case (str, (k,v)) =>
//      str.replaceAll(s"([ (),])$k([ (),])", "$1" + v.toString + "$2")}
//    val rhs = replace(rightOfArrow.mkString(";"))
//    s"(${notGenerated} - |> $rhs)"
    rightOfArrow.mkString(";")
  }
}
object AbstractTrace{
  implicit var rw:RW[AbstractTrace] = macroRW[AbstractTrace]
  //got rid of lspred in abstract trace TODO: remove below
  @deprecated
  def apply(a:LSPred, rightOfArrow:List[LSSingle], modelVars: Map[Any,PureExpr]):AbstractTrace = ???
  // def apply(rightOfArrow:List[LSSingle], modelVars:Map[String,PureExpr]):AbstractTrace = ???
}

sealed trait LSParamConstraint{
  def optTraceAbs: Option[AbstractTrace]
}
case class LSPure(p: PureExpr) extends LSParamConstraint {
  override def optTraceAbs: Option[AbstractTrace] = None
}

object LSAny extends LSParamConstraint {
  override def optTraceAbs: Option[AbstractTrace] = None
}
case class LSConstConstraint(pureExpr: PureExpr, trace:AbstractTrace) extends LSParamConstraint{
  override def optTraceAbs: Option[AbstractTrace] = Some(trace)
}

/**
 *
 * @param callStack Application only call stack abstraction, emtpy stack or callin on top means framework control.
 * @param heapConstraints Separation logic heap representation
 * @param pureFormula Constraints on values in separation logic formula including:
 *                    - null/not null
 *                    - type bounds
 * @param traceAbstraction Trace required to reach this point in the program execution
 */
case class StateFormula(callStack: List[CallStackFrame],
                        heapConstraints: Map[HeapPtEdge, PureExpr],
                        pureFormula: Set[PureConstraint],
                        typeConstraints: Map[PureVar, TypeSet],
                        traceAbstraction: AbstractTrace,
                        isAbstract:Boolean = true //concrete or abstract
                       ){
  // Remember if this state has been checked for satisfiability
  var isSimplified = false
  def setSimplified(): StateFormula = {
    isSimplified = true
    this
  }

  /**
   * Remove fresh ref from state
   * @param freshRef
   * @return
   */
  def clearFreshRef(freshRef: FreshRef):StateFormula = {
    val newTraceAbstraction = AbstractTrace(traceAbstraction.rightOfArrow.filter(_ != freshRef))
    this.copy(traceAbstraction = newTraceAbstraction)
  }

  def allIRefByState(spec:SpecSpace): Set[AbsMsg] = allIRef(spec)
  def clearTC:StateFormula = {
    this.copy(typeConstraints = Map())
  }

  private val allIRef = Memo.mutableHashMapMemo {
    (spec: SpecSpace) =>
      EncodingTools.rhsToPred(traceAbstraction.rightOfArrow, spec)
        .flatMap(p => SpecSpace.allI(p))
  }
  def swapPv(oldPv : PureVar, newPv: PureVar):StateFormula = {
    if(oldPv == newPv)
      this
    else {
      this.copy(
        callStack = callStack.map(f => stackSwapPv(oldPv, newPv, f)),
        heapConstraints = heapConstraints.map(hc => heapSwapPv(oldPv, newPv, hc)),
        pureFormula = pureFormula.map(pf => pureSwapPv(oldPv, newPv, pf)),
        traceAbstraction = traceSwapPv(oldPv, newPv, traceAbstraction),
        typeConstraints = typeConstraints.map {
          case (k, v) if k == oldPv => (newPv, v)
          case (k, v) => (k, v)
        }
      )
    }
  }

  private def pureExprSwap[T<:PureExpr](oldPv : PureVar, newPv : PureVar, expr:T): T = expr match{
    case p:PureVar if p==oldPv =>
      newPv.asInstanceOf[T]
    case pv:PureVar =>
      pv.asInstanceOf[T]
    case pv: PureVal =>
      pv.asInstanceOf[T]
  }
  private def stackSwapPv(oldPv : PureVar, newPv : PureVar, frame: CallStackFrame): CallStackFrame =
    frame.copy(locals = frame.locals.map{
      case (k,v) => (k->pureExprSwap(oldPv, newPv, v))
    })

  private def heapSwapPv(oldPv : PureVar, newPv : PureVar, hv: (HeapPtEdge, PureExpr)):(HeapPtEdge, PureExpr) = hv match{
    case (FieldPtEdge(pv, fieldName), pe) =>
      (FieldPtEdge(pureExprSwap(oldPv, newPv, pv), fieldName), pureExprSwap(oldPv, newPv, pe))
    case (StaticPtEdge(clazz,fname), pe) =>
      (StaticPtEdge(clazz,fname), pureExprSwap(oldPv,newPv,pe))
    case (ArrayPtEdge(base, index), pe) =>
      (ArrayPtEdge(pureExprSwap(oldPv,newPv, base), pureExprSwap(oldPv,newPv,index)),pureExprSwap(oldPv,newPv,pe))
  }
  private def pureSwapPv(oldPv : PureVar, newPv : PureVar,
                         pureConstraint: PureConstraint):PureConstraint = pureConstraint match{
    case PureConstraint(lhs, op, rhs) =>
      PureConstraint(pureExprSwap(oldPv, newPv, lhs),op, pureExprSwap(oldPv, newPv, rhs))
  }

  private def traceSwapPv(oldPv : PureVar, newPv : PureVar, tr: AbstractTrace):AbstractTrace = {
//    val nmv = tr.modelVars.map{
//      case (k,v) => (k,pureExprSwap(oldPv, newPv, v))
//    }
//    tr.copy(modelVars = nmv)
    tr.copy(rightOfArrow = tr.rightOfArrow.map(single => single.swap(Map(oldPv->newPv)).asInstanceOf[LSSingle]))
  }

  /**
   * Remove all negative instances of pure var
   * @param pv
   * @return
   */
  def clearNegPvAndConstraints(pv:PureVar):StateFormula =
    this.copy(traceAbstraction = AbstractTrace(traceAbstraction.rightOfArrow.filter {
      case FreshRef(v) if v == pv => false
      case _ => true
      }),
      pureFormula = pureFormula.filter{
        case PureConstraint(lhs, _, rhs) => lhs != pv && rhs!=pv
      },
      typeConstraints = typeConstraints.removed(pv)
    )
  /**
   * Pure variables that are referenced as existing in the past trace abstraction heap or stack.
   * Pv cannot only occur in:
   * - FreshRef(pv) - since it says existing values are not equal to pv
   * - pure constraints
   * - type constraints
   * @return set of pure variables
   */
  def posPureVars():Set[PureVar] = {
    val pureVarOpt = (a:PureExpr) => a match {
      case p: PureVar => Some(p)
      case _ => None
    }
    val pureVarOptH = (a:HeapPtEdge) => a match {
      case FieldPtEdge(p, _) => Some(p)
      case ArrayPtEdge(p, _) => Some(p)
      case _ => None
    }
    val pureVarFromLocals: Set[PureVar] = callStack.headOption match {
      case Some(CallStackFrame(_, _, locals)) =>
        locals.flatMap(a => pureVarOpt(a._2)).toSet
      case None => Set()
    }
    val pureVarFromHeap = heapConstraints
      .flatMap(a => Set() ++ pureVarOptH(a._1) ++ pureVarOpt(a._2)).toSet

    val pureVarFromTrace = traceAbstraction.rightOfArrow.flatMap {
      case LifeState.CLInit(_) => None
      case FreshRef(_) => None
      case o:AbsMsg => o.lsVar
    }
    pureVarFromHeap ++ pureVarFromLocals ++ pureVarFromTrace
  }

  def iPureVars():Set[PureVar] = {
    val pureVarOpt = (a:PureExpr) => a match {
      case p: PureVar => Some(p)
      case _ => None
    }
    val pureVarOptH = (a:HeapPtEdge) => a match {
      case FieldPtEdge(p, _) => Some(p)
      case ArrayPtEdge(p, _) => Some(p)
      case _ => None
    }
    val pureVarFromLocals: Set[PureVar] = callStack.headOption match {
      case Some(CallStackFrame(_, _, locals)) =>
        locals.flatMap(a => pureVarOpt(a._2)).toSet
      case None => Set()
    }
    val pureVarFromHeap = heapConstraints
      .flatMap(a => Set() ++ pureVarOptH(a._1) ++ pureVarOpt(a._2)).toSet
    val pureVarFromConst = pureFormula.flatMap{
      case PureConstraint(p1,_,p2) => Set() ++ pureVarOpt(p1) ++ pureVarOpt(p2)
    }
    val pureVarFromTrace = traceAbstraction.modelVars
    pureVarFromHeap ++ pureVarFromLocals ++ pureVarFromConst ++ typeConstraints.keySet ++ pureVarFromTrace
  }
}
object StateFormula{
  implicit var rw:RW[StateFormula] = macroRW
  def initialState:StateFormula = StateFormula(Nil, Map.empty, Set(), Map.empty, AbstractTrace(Nil))
}

/**
 *
 * @param nextAddr Int val of next pure val to be declared
 * @param nextCmd Command just processed while executing backwards.
 */
case class State(sf:StateFormula,
                 nextAddr:Int,
                 nextCmd: List[Loc] = Nil,
                 alternateCmd: List[Loc] = Nil
                ) {
  def equivPv(pv: PureVar):Set[PureVar] = {
    def innerFP(pvs:Set[PureVar]) : Set[PureVar]= {
      val nextpvs = sf.pureFormula.foldLeft(pvs){
        case (acc,PureConstraint(lhs:PureVar, Equals, rhs:PureVar)) if acc.contains(lhs) => acc + rhs
        case (acc,PureConstraint(lhs:PureVar, Equals, rhs:PureVar)) if acc.contains(rhs) => acc + lhs
        case (acc,_) => acc
      }
      if(nextpvs == pvs) pvs else innerFP(nextpvs)
    }
    innerFP(Set(pv))
  }

  def traceKey: List[String] =
    this.traceAbstraction.rightOfArrow.map(m => m.identitySignature)
  def heapKey: List[String] = sf.heapConstraints.map{
    case (FieldPtEdge(_, fieldName), _) => s"df:${fieldName}"
    case (StaticPtEdge(obj,fieldName), _) => s"sf:${obj}:${fieldName}"
    case _ => ???
  }.toList

  def isSimplified:Boolean = sf.isSimplified
  def setSimplified():State = {
    sf.setSimplified()
    this
  }
  // sf accessors
  def callStack: List[CallStackFrame] = sf.callStack
  def heapConstraints: Map[HeapPtEdge, PureExpr] = sf.heapConstraints
  def pureFormula: Set[PureConstraint] = sf.pureFormula
  def typeConstraints: Map[PureVar, TypeSet] = sf.typeConstraints
  def traceAbstraction: AbstractTrace = sf.traceAbstraction

  // sf copy methods
  def clearTC:State = {
    this.copy(sf = this.sf.clearTC)
  }
  def addTypeConstraint(pv:PureVar, typeSet:TypeSet):State =
    this.copy(sf = sf.copy(typeConstraints = sf.typeConstraints + (pv -> typeSet)))
  def addPureConstraint(p:PureConstraint):State = {
    this.copy(sf = sf.copy(pureFormula = sf.pureFormula + p))
  }
  def swapPv(oldPv : PureVar, newPv: PureVar):State = {
    this.copy(sf = sf.swapPv(oldPv, newPv))
  }
  def removePureConstraint(pc:PureConstraint) = {
    this.copy(sf = sf.copy(pureFormula = sf.pureFormula - pc))
  }
  def setCallStack(callStack: List[CallStackFrame]):State =
    this.copy(sf = sf.copy(callStack = callStack))

  def constrainOneOfType(pv: PureVar, classNames: Set[String], ch:ClassHierarchyConstraints):State = {
    if(classNames.contains("_")) {
      return this
    }
    if(classNames.isEmpty){
//      return this.copy(typeConstraints = typeConstraints + (pv -> EmptyTypeSet))
      addTypeConstraint(pv,EmptyTypeSet)
    }
    val typeSets: Set[BitSet] = classNames.map(n => ch.classToIntCache(n))
    val mask = BitTypeSet(typeSets.reduce((a,b) => a.union(b)))
    val newTS = sf.typeConstraints.get(pv).map(_.intersect(mask)).getOrElse(mask)
//    this.copy(typeConstraints = typeConstraints + (pv -> newTS))
    addTypeConstraint(pv,newTS)
  }

  def constrainIsType(pv: PureVar, className: String, ch: ClassHierarchyConstraints): State = {
    if(className == "_") {
      return this
    }
    val mask = BitTypeSet(ch.classToIntCache(className))
    val newTS = sf.typeConstraints.get(pv).map(_.intersect(mask)).getOrElse(mask)
//    this.copy(typeConstraints= typeConstraints + (pv -> newTS))
    addTypeConstraint(pv,newTS)
  }

  def constrainUpperType(pv:PureVar, clazz:String, ch:ClassHierarchyConstraints):State = {
    if(clazz == "_"){
      return this
    }
    val newTc = sf.typeConstraints.get(pv) match{
      case Some(tc) => tc.filterSubTypeOf(Set(clazz))(ch)
      case None =>
        TopTypeSet
    }
    addTypeConstraint(pv,newTc)
  }

  def canAliasPv(pv1:PureVar, pv2:PureVar):Boolean ={
    val typeCanAlias = (sf.typeConstraints.get(pv1), sf.typeConstraints.get(pv2)) match {
      case (Some(t1), Some(t2)) =>
        t1.intersectNonEmpty(t2)
      case _ => true
    }
    lazy val constraintCanAlias = sf.pureFormula.forall{
      case PureConstraint(v1, NotEquals, v2) => pv1 != v1 || pv2 != v2
      case _ => true
    }
    typeCanAlias && constraintCanAlias
  }
  def canAliasPe[M,C](pv:PureVar, lv:PureExpr):Boolean = lv match {
    case pureVal: PureVal => true // equality is handled by StateSolver
    case pv2:PureVar => canAliasPv(pv, pv2)
  }
  def canAliasEE(pe1:PureExpr, pe2:PureExpr):Boolean = pe1 match {
    case pureVal: PureVal => pe2 match{
      case _:PureVal => true // equality is handled by StateSolver
      case pv2:PureVar => canAliasPe(pv2, pureVal)
    }
    case pv:PureVar => canAliasPe(pv,pe2)
  }

  /**
   * Can a pure variable alias a local variable?
   * @param pv pure variable from state
   * @param method method containing the local variable
   * @param lw the local
   * @param w IR of the program under analysis
   * @param inCurrentStackFrame should we restrict the aliasing with the current stack frame?
   *                            (should be true if used to determine materialization, false for relevance)
   * @tparam M
   * @tparam C
   * @return
   */
  def canAlias[M,C](pv:PureVar, method:MethodLoc, lw:LocalWrapper, w:IRWrapper[M,C],
                    inCurrentStackFrame:Boolean):Boolean = {
    implicit val wr = w
    sf.typeConstraints.get(pv) match{
      case Some(pvPt) =>
        val pt = w.pointsToSet(method, lw)
        if(inCurrentStackFrame && containsLocal(lw)){
          assert(sf.callStack.headOption.forall(s => s.exitLoc.containingMethod.get == method),
            "Error, call string and variable name must match if inCurrentStackFrame is set to true." +
              s"Otherwise pts to sets for variable are incomparable. " +
              s"Stack frame method: ${sf.callStack.headOption.map(_.exitLoc)}.  " +
              s"Local: $lw . " +
              s"Method containing local: $method")
          val lv = get(lw).get
          canAliasPe(pv,lv) && pt.intersectNonEmpty(pvPt)
        }else {
          pt.intersectNonEmpty(pvPt)
        }
      case None => true
    }
  }

  /**
   * Use for over approximate relevant methods
   * @return set of field names that could be referenced by abstract state
   */
  def fieldNameSet():Set[String] = sf.heapConstraints.keySet.flatMap{
    case FieldPtEdge(_,fieldName) => Some(fieldName)
    case StaticPtEdge(_, fieldName) => Some(fieldName)
    case ArrayPtEdge(_,_) => None
  }

  def allIRefByState(spec:SpecSpace):Set[AbsMsg] = sf.allIRefByState(spec)
  def fastIMatches(subsignature: String, spec:SpecSpace):Boolean =
    allIRefByState(spec:SpecSpace).exists(i => i.signatures.matchesSubSig(subsignature))

  def entryPossible(loc: Loc): Boolean = loc match{
    case CallbackMethodInvoke(sig, _) =>
      sf.callStack.headOption match{
        case Some(CallStackFrame(CallbackMethodReturn(sig2,_,_),_,_)) =>
          sig==sig2
        case None => true
        case _ => false
      }
    case InternalMethodInvoke(clazz,name,_) =>
      sf.callStack.headOption match{
        case Some(CallStackFrame(InternalMethodReturn(clazz2, name2,_),_,_)) =>
          clazz == clazz2 && name == name2
        case None => true
        case _ => false
      }
    case v => throw new IllegalStateException(s"$v is not a entry location")
  }


  /**
   * move newPV to a fresh pure variable and then swap all instances of oldPV to newPV
   * @param oldPv
   * @param newPv
   * @return
   */
  def swapPvUnique(oldPv:PureVar, newPv:PureVar):State = {
    if(oldPv == newPv)
      this
    else {
      val freshPv = NPureVar(nextAddr)
      val sFresh = this.copy(nextAddr = nextAddr + 1, sf = sf.swapPv(newPv, freshPv))
      sFresh.copy(sf = sFresh.sf.swapPv(oldPv, newPv))
    }
  }

  def setNextCmd(cmd: List[Loc]):State = this.copy(nextCmd = cmd)

  def nextPv() = (NPureVar(nextAddr), this.copy(nextAddr = nextAddr+1))

//  def lsVarConstraint(f: AbstractTrace, lsvar: String): Option[LSParamConstraint] = f match{
//    case AbstractTrace(_,mv) => mv.get(lsvar).map(LSPure)
//  }

  def findIFromCurrent(dir: MessageType,
                       signature: Signature, specSpace: SpecSpace)(implicit
                                                    ch:ClassHierarchyConstraints): Set[AbsMsg] = {
    allIRefByState(specSpace).filter(i => i.mt == dir&& i.signatures.matches(signature))
  }


  private def pformulaVars(p:PureExpr):Set[PureVar] = p match{
    case p:PureVar => Set(p)
    case _ => Set()
  }
  private def tformulaVars(t : LSPred):Set[PureVar] = t match{
    case And(lhs,rhs) => tformulaVars(lhs).union(tformulaVars(rhs))
    case Or(lhs,rhs) => tformulaVars(lhs).union(tformulaVars(rhs))
    case Not(v) => tformulaVars(v)
    case _ => Set()
  }

  override def toString:String = {
    def sfString(sfl:List[CallStackFrame], frames: Int):String = (sfl,frames) match{
      case (sf::t, fr) if fr > 0 =>
        val locals: Map[StackVar, PureExpr] = sf.locals
        s"${sf.exitLoc.msgSig.getOrElse("")} " +
          s"locals: " + locals.map(k => k._1.toString + " -> " + k._2.toString).mkString(",") + "     " +
          sfString(t, fr-1)
      case (Nil,_) => ""
      case (_::_,_) => "..."
    }
    val stackString = sfString(sf.callStack, 2)

    val heapString = s"   heap: ${sf.heapConstraints.map(a => a._1.toString + "->" +  a._2.toString).mkString(" * ")}    "
    val pureFormulaString = "   pure: " + sf.pureFormula.map(a => a.toString).mkString(" && ") +"    "
    val traceString = s"   trace: ${sf.traceAbstraction}"
    val typeString = s"    types: ${sf.typeConstraints.map{case (k,v) => k.toString + ":" + v.toString}}"
    s"($stackString $heapString   $pureFormulaString $typeString $traceString)"
  }
  def containsLocal(localWrapper: LocalWrapper):Boolean = {
    val sVar = StackVar(localWrapper.name)
    sf.callStack.headOption.exists(f => f.locals.contains(sVar))
  }

  // helper functions to find pure variable
  private def expressionContains(expr: PureExpr, pureVar: PureVar):Boolean = expr match {
    case p2:PureVar => pureVar == p2
    case _ => false
  }
  private def callStackContains(p :PureVar):Boolean = {
    sf.callStack.exists({
      case CallStackFrame(_,_,locals) => locals.exists(r => expressionContains(r._2,p))
    })
  }

  private def ptEdgeContains(edge: HeapPtEdge, p: PureVar): Boolean = edge match{
    case FieldPtEdge(p2, _) => p == p2
    case _ => ???
  }

  private def heapContains(p:PureVar):Boolean =
    sf.heapConstraints.exists(r => expressionContains(r._2,p) || ptEdgeContains(r._1,p))

  private def pureFormulaContains(p: PureVar): Boolean =
    sf.pureFormula.exists(c => expressionContains(c.lhs,p) || expressionContains(c.rhs,p))

  def traceAbstractionContains(p: PureVar): Boolean = {
//    sf.traceAbstraction.modelVars.exists{
//      case (k,v) if v == p => true
//      case _ => false
//    }
    ???
  }

  def contains(p:PureVar):Boolean = {
     callStackContains(p) || heapContains(p) || pureFormulaContains(p) || traceAbstractionContains(p)
  }

  /**
   * get local without searching for @this
   * @param localWrapper local to find
   * @return pointed to value
   */
  def testGet(localWrapper: LocalWrapper): Option[PureExpr] ={
    sf.callStack match{
      case CallStackFrame(_,_,locals)::_ => locals.get(StackVar(localWrapper.name))
      case _ => None
    }
  }


  // If an RVal exists in the state, get it
  // for a field ref, e.g. x.f if x doesn't exist, create x
  // if x.f doesn't exist and x does
  def get[M,C](l:RVal)(implicit w:IRWrapper[M,C]):Option[PureExpr] = l match {
    case lw@LocalWrapper(name,_) =>
//      val ch = w.getClassHierarchyConstraints
      sf.callStack match{
        case CallStackFrame(exitLoc,_,locals)::_ if exitLoc.containingMethod.isDefined =>
          if(locals.contains(StackVar(name)))
            locals.get(StackVar(name)) //TODO:====== check that containingMethod does something reasonable here
          else {
            val thisV = exitLoc.containingMethod.flatMap(w.getThisVar)
            thisV.flatMap{
              case tv if tv == lw =>
                val r = locals.get(StackVar("@this"))
                r
              case _ => None
            }
          }
        case CallStackFrame(_,_,locals)::_ => locals.get(StackVar(name))
        case Nil => None
      }
    case IntConst(v) =>
      Some(IntVal(v))
    case StringConst(v) =>
      Some(StringVal(v))
    case NullConst => Some(NullVal)
    case BoolConst(v) => Some(BoolVal(v))
    case ClassConst(clazz) => Some(ClassVal(clazz))
    case ConstVal(_) => Some(TopVal)//TODO: For now losing precision with floats longs chars etc
    case l =>
      println(l)
      ???
  }
  // TODO: does this ever need to "clobber" old value?
  //TODO: refactor so local always points to pv
  def defineAs[M,C](l : RVal, pureExpr: PureExpr)
                   (implicit ch:ClassHierarchyConstraints, w:IRWrapper[M,C]): State = {
    val cshead: CallStackFrame = sf.callStack.headOption.getOrElse{
      throw new IllegalStateException("Expected non-empty stack")
    }
    val l2 = cshead.exitLoc.containingMethod match{
      case Some(v) if w.getThisVar(v).contains(l) =>
        LocalWrapper("@this","_")
      case _ => l
    }
    l2 match{
      case LocalWrapper(localName, localType) =>

        if(cshead.locals.contains(StackVar(localName))){
          val v = cshead.locals.get(StackVar(localName))
//          this.copy(sf = sf.copy(pureFormula = sf.pureFormula + PureConstraint(v.get , Equals, pureExpr)))
          addPureConstraint(PureConstraint(v.get, Equals, pureExpr))
        }else {
          val csheadNew = cshead.copy(locals = cshead.locals + (StackVar(localName) -> pureExpr))
          pureExpr match {
            case pureVar:PureVar =>
              this.copy(sf = sf.copy(callStack = csheadNew :: sf.callStack.tail))
                .constrainUpperType (pureVar, localType, ch)
            case v =>
              println(s"TODO: defineAs used on value: ${v}")
              ???
          }
//            pureFormula = pureFormula + PureConstraint(pureExpr, TypeComp, SubclassOf(localType)))
        }
      case v if v.isConst =>
        val v2 = get(v).get
//        this.copy(pureFormula = this.pureFormula + PureConstraint(v2, Equals, pureExpr))
        addPureConstraint(PureConstraint(v2, Equals, pureExpr))
      case v =>
        println(v)
        ???
    }
  }

  //TODO: this should probably be the behavior of getOrDefine, refactor later
  def getOrDefine2[M,C](l : RVal, method:MethodLoc)
                       (implicit ch:ClassHierarchyConstraints, w:IRWrapper[M,C]): (PureExpr, State) = l match{
    case l:LocalWrapper => getOrDefine(l, Some(method))
    case v if v.isConst =>
      (get(l).getOrElse(???),this)
    case _ =>
      ???
  }

  /**
   *
   * @param l rVal to define, usually a local
   * @param method method where rVal exists (for points to set)
   * @return
   */
  def getOrDefine[M,C](l : RVal, method:Option[MethodLoc])
                      (implicit ch: ClassHierarchyConstraints, w:IRWrapper[M,C]): (PureVar,State) = l match{
    case lw@LocalWrapper(name,localType) =>
      val cshead = sf.callStack.headOption.getOrElse(???) //TODO: add new stack frame if empty?
      val thisVar:Option[LocalWrapper] = w.getThisVar(cshead.exitLoc)
      val ts: Option[TypeSet] = method.map(w.pointsToSet(_, LocalWrapper(name,localType)))
      //TODO: constrain types based on points to set
      val cstail = if (sf.callStack.isEmpty) Nil else sf.callStack.tail
//      cshead.locals.get(StackVar(name)) match {
      get(lw) match {
        case Some(v:PureVar) => (v, this)
        case None if thisVar.contains(l) && cshead.locals.contains(StackVar("@this")) =>
          // case where we are getting/defining the variable representing "this" typically "r0"
          // note that "@this" is defined when processing the caller and may constrain the types
          // further than the type system
          val thisV = cshead.locals(StackVar("@this")).asInstanceOf[PureVar]
          val newStack = cshead.copy(locals = cshead.locals + (StackVar(name) -> thisV)) :: cstail
          val combinedTs: Option[(PureVar,TypeSet)] = (sf.typeConstraints.get(thisV),ts) match{
            case (Some(ts1),Some(ts2)) =>
              Some(thisV -> ts1.intersect(ts2))
            case (Some(ts),_) => Some(thisV->ts)
            case (_,Some(ts)) => Some(thisV->ts)
            case _ => None
          }
          val state = this.copy(sf = sf.copy(callStack = newStack,pureFormula = sf.pureFormula +
            PureConstraint(thisV, NotEquals, NullVal),
            typeConstraints = sf.typeConstraints ++ combinedTs), nextAddr = nextAddr)
          (thisV, state)
        case None =>
          val newident = NPureVar(nextAddr)
          val newStack = cshead.copy(locals = cshead.locals + (StackVar(name) -> newident)) :: cstail
          val combinedTs: Option[(PureVar,TypeSet)] = (sf.typeConstraints.get(newident),ts) match{
            case (Some(ts1),Some(ts2)) => Some(newident -> ts1.intersect(ts2))
            case (Some(ts),_) => Some(newident->ts)
            case (_,Some(ts)) => Some(newident->ts)
            case _ => None
          }
          val state = this.copy(sf = sf.copy(callStack = newStack,typeConstraints = sf.typeConstraints ++ combinedTs),
            nextAddr = nextAddr + 1)
          val st2 = state.constrainUpperType(newident, localType, ch)
          (newident, st2)
      }
    case NullConst =>
      val (pv, newState) = nextPv()
      val stateWithPC = newState.addPureConstraint(PureConstraint(pv, Equals, NullVal))
      (pv,stateWithPC)
    case IntConst(v) =>
      val (pv, newState) = nextPv()
      val stateWithPC = newState.addPureConstraint(PureConstraint(pv, Equals, IntVal(v)))
      (pv,stateWithPC)
    case v =>
      ??? //TODO: should probably restrict this function to only take locals
  }

  /**
   * When a var is assigned, we remove it from our constraint set
   * @param l variable being assigned
   * @return new state
   */
  def clearLVal(l : LVal): State = (l,sf.callStack) match {
    case (LocalWrapper(name,_), cshead::cstail) =>
      val newCsHead = cshead.removeStackVar(StackVar(name))
      this.copy(sf = sf.copy(callStack = newCsHead::cstail))
    case _ =>
      ???
  }

  private var pvCache:Option[Set[PureVar]] = None
  def pureVars():Set[PureVar] = {
    val out = pvCache match{
      case None =>
        val computed = sf.iPureVars()
        pvCache = Some(computed)
        computed
      case Some(v) => v
    }
    out
  }

  def isNull(pv:PureVar):Boolean = {
    sf.pureFormula.contains(PureConstraint(pv,Equals,NullVal))
  }
}

sealed trait Var
object Var{
  implicit val rw:RW[Var] = RW.merge(macroRW[StackVar])
}

case class StackVar(name : String) extends Var{
  override def toString:String = name
}
object StackVar{
  implicit val rw:RW[StackVar] = macroRW
}

sealed trait CmpOp
object CmpOp{
  implicit val rw:RW[CmpOp] = RW.merge(
    macroRW[Equals.type], macroRW[NotEquals.type], macroRW[TypeComp.type])
}
case object Equals extends CmpOp{
  override def toString:String = " == "
}
case object NotEquals extends CmpOp{
  override def toString:String = " != "
}

case object TypeComp extends CmpOp

case class PureConstraint(lhs:PureExpr, op: CmpOp, rhs:PureExpr) {
  override def toString:String = s"$lhs $op $rhs"
}
object PureConstraint {
  implicit val rw:RW[PureConstraint] = macroRW
}

sealed abstract class PureExpr {
  def substitute(toSub : PureExpr, subFor : PureVar) : PureExpr
  def isStringExpr : Boolean = false
  def isBitwiseExpr : Boolean = false
  def isFloatExpr : Boolean = false
  def isLongExpr : Boolean = false
  def isDoubleExpr : Boolean = false
  def getVars(s : Set[PureVar] = Set.empty) : Set[PureVar]
}
object PureExpr{
  implicit val rw:RW[PureExpr] = RW.merge(PureVal.rw, PureVar.rw)
}

// primitive values
sealed abstract class PureVal(v:Any) extends PureExpr with Nameable {
  override def substitute(toSub : PureExpr, subFor : PureVar) : PureVal = ???

  def >(p : PureVal) : Boolean = sys.error("GT for arbitrary PureVal")
  def <(p : PureVal) : Boolean = sys.error("LT for arbitrary PureVal")
  def >=(p : PureVal) : Boolean = sys.error("GE for arbitrary PureVal")
  def <=(p : PureVal) : Boolean = sys.error("LE for arbitrary PureVal")
  override def isStringExpr : Boolean = ??? //this.isInstanceOf[StringVal]
  override def getVars(s : Set[PureVar] = Set.empty) : Set[PureVar] = s

//  override def hashCode : Int = ???
//  override def equals(other : Any) : Boolean = other match {
//    case p : PureVal => this.v == p.v
//    case _ => false
//  }
  override def toString : String = v.toString
//  def z3Tag:Option[String]
}
case object PureVal{
  implicit val rw:RW[PureVal] = RW.merge(
    macroRW[NullVal.type], macroRW[TopVal.type],
    macroRW[IntVal],macroRW[BoolVal],macroRW[StringVal], ClassVal.rw)
}

trait ConcreteVal extends PureVal{
  def pe:PureExpr
}
object ConcreteVal{
  implicit var rw:RW[ConcreteVal] = RW.merge(macroRW[ConcreteAddr], macroRW[NullVal.type])
}
//case object T_ extends TVal
case class ConcreteAddr(i:Int) extends ConcreteVal{
  override def toString: String = s"@$i"

  override def pe: PureExpr = ???

  override def solverName: String = ???
}
case object NullVal extends ConcreteVal {
  override def toString:String = "NULL"

  //override def z3Tag: Option[String] = Some("NULL")
  implicit val rw:RW[NullVal.type] = macroRW

  override def solverName: String = "const_NULL"

  override def pe: PureExpr = ???
}

case class IntVal(v : Int) extends PureVal(v){
  override def solverName: String = s"const_I$v"
}
//TODO: is BoolVal ever actually used?
case class BoolVal(v : Boolean) extends PureVal(v) {
  override def solverName: String = s"const_B$v"
}
case class StringVal(v : String) extends PureVal(v) {
  override def solverName: String = s"const_S${v.hashCode}"
}
case class ClassVal(name:String) extends PureVal(name) {
  override def solverName: String = s"C$name"
}
object ClassVal{
  implicit val rw:RW[ClassVal] = macroRW
}
case object TopVal extends PureVal(null) {
  override def solverName:String = "const_T_"
  override def toString:String = "_T_"
}
case object BotVal extends PureVal(null) {
  override def solverName:String = "const_Bot_"
}

sealed trait TypeConstraint
case class SubclassOf(clazz: String) extends TypeConstraint{
  assert(clazz != "_")
  override def toString:String = s"<: $clazz"
}
case class SuperclassOf(clazz:String) extends TypeConstraint {
  override def toString:String = s">: $clazz"
}
case class ClassType(typ:String) extends TypeConstraint {
  override def toString:String = s": $typ"
}
case class OneOfClass(possibleClass: Set[String]) extends TypeConstraint {
  override def toString:String = {
    val possibleDots = if(possibleClass.size > 3) ", ..." else ""
    s": {${possibleClass.slice(0,3).mkString(",") + possibleDots}}"
  }
}
case class ImplementsInterface(typ:String) extends TypeConstraint {
  override def toString:String = s"<: I-$typ"
}


// pure var is a symbolic var (e.g. this^ from the paper)

sealed trait PureVar extends PureExpr
object PureVar{
  def apply(id:Int):PureVar = NPureVar(id)
  def unapply(pv:PureVar):Option[Any] = pv match {
    case NPureVar(id) => Some(id)
    case NamedPureVar(n) => Some(n)
    case _ => None
  }
  implicit val rw:RW[PureVar] = RW.merge(NPureVar.rw, NamedPureVar.rw)
}

sealed case class NPureVar(id:Int) extends PureVar with Nameable {
//  val id : Int = State.getId()
  override def getVars(s : Set[PureVar]) : Set[PureVar] = s + this

  override def substitute(toSub : PureExpr, subFor : PureVar) : PureExpr = if (subFor == this) toSub else this

  override def hashCode : Int = id*100271

  override def toString : String = "p-" + id

  override def solverName: String = s"pv-$id"
}
object NPureVar{
  implicit val rw:RW[NPureVar] = macroRW
}

sealed case class NamedPureVar(n:String) extends PureVar with Nameable {
  override def substitute(toSub: PureExpr, subFor: PureVar): PureExpr = if (subFor == this) toSub else this

  override def getVars(s: Set[PureVar]): Set[PureVar] = s + this

  override def toString : String = "p-" + n

  override def solverName: String = s"npv-$n"
}

object NamedPureVar{
  implicit val rw:RW[NamedPureVar] = macroRW
}
