package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, StateSolver}
import edu.colorado.plv.bounder.ir.{AppLoc, BoolConst, CallbackMethodInvoke, CallbackMethodReturn, ClassConst, IntConst, InternalMethodInvoke, InternalMethodReturn, LVal, Loc, LocalWrapper, MessageType, NullConst, RVal, StringConst}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecSpace}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSAnyVal, LSPred, NI, Not, Or}
import edu.colorado.plv.bounder.symbolicexecutor.state.State.findIAF
import upickle.default.{macroRW, ReadWriter => RW}

import scala.annotation.tailrec
import scala.collection.View

object State {
  private var id:Int = -1

  /**
   * Only use in tests
   * //TODO: move to test file
   * @return
   */
  def getId_TESTONLY():Int = {
    id = id + 1
    id
  }
  def topState:State =
    State(Nil,Map(),Set(),Map(),Set(),0)

  def findIAF(messageType: MessageType, tuple: (String, String), pred: LSPred):Set[I] = pred match{
    case i@I(mt, sigs, _) if mt == messageType && sigs.contains(tuple) => Set(i)
    case NI(i1,i2) => Set(i1,i2).flatMap(findIAF(messageType, tuple, _))
    case And(l1,l2) => findIAF(messageType,tuple,l1).union(findIAF(messageType,tuple,l2))
    case Or(l1,l2) => findIAF(messageType,tuple,l1).union(findIAF(messageType,tuple,l2))
    case Not(l) => findIAF(messageType, tuple, l)
    case _ => Set()
  }
  implicit var rw:RW[State] = macroRW
}

// pureFormula is a conjunction of constraints
// callStack is the call string from thresher paper
//sealed trait TraceAbstractionArrow
case class AbstractTrace(a:LSPred,rightOfArrow:List[I], modelVars: Map[String,PureExpr]){
  def addModelVar(v: String, pureVar: PureExpr): AbstractTrace = {
    assert(LifeState.LSVar.matches(v))
    assert(!modelVars.contains(v), s"model var $v already in trace abstraction.")
    this.copy(modelVars= modelVars + (v->pureVar))
  }

  override def toString:String = {
    val generated = modelVars.filter{case (k,_) => LifeState.LSGenerated.matches(k) }
    val notGenerated = modelVars.removedAll(generated.keySet)
    val replace: String => String = str => generated.foldLeft(str){case (str, (k,v)) => str.replaceAll(k, v.toString)}
    val lhs = replace(a.toString)
    val rhs = replace(rightOfArrow.mkString(";"))
    s"(${notGenerated} - $lhs |> $rhs)"
  }
}
object AbstractTrace{
  implicit var rw:RW[AbstractTrace] = macroRW[AbstractTrace]
}

sealed trait LSParamConstraint{
  def optTraceAbs: Option[AbstractTrace]
}
case class LSPure(p: PureExpr) extends LSParamConstraint {
  override def optTraceAbs: Option[AbstractTrace] = None
}
case class LSModelVar(s:String, trace:AbstractTrace) extends LSParamConstraint {
  assert(LifeState.LSVar.matches(s), s"Failure parsing $s as model var")
  override def optTraceAbs: Option[AbstractTrace] = Some(trace)
}
object LSAny extends LSParamConstraint {
  override def optTraceAbs: Option[AbstractTrace] = None
}
case class LSConstConstraint(pureExpr: PureExpr, trace:AbstractTrace) extends LSParamConstraint{
  override def optTraceAbs: Option[AbstractTrace] = Some(trace)
}
sealed trait TypeSet{
  def join(tc2: TypeSet, ch:ClassHierarchyConstraints):TypeSet

  def typeSet(ch: ClassHierarchyConstraints): Set[String]

  def optionalConstrainUpper(upper:Option[String], ch:ClassHierarchyConstraints):TypeSet = upper match{
    case Some(v) => this.constrainSubtypeOf(v,ch)
    case None => this
  }
  def optionalConstrainLower(lower:Option[String], ch:ClassHierarchyConstraints):TypeSet = lower match{
    case Some(v) => this.constrainSupertypeOf(v, ch)
    case None => this
  }
  def subtypeOfCanAlias(localType: String, ch: ClassHierarchyConstraints): Boolean

  def contains(set: TypeSet)(implicit ch:ClassHierarchyConstraints): Boolean

  def constrainSubtypeOf(name:String, hierarchyConstraints: ClassHierarchyConstraints):TypeSet
  def constrainSupertypeOf(name:String, hierarchyConstraints: ClassHierarchyConstraints):TypeSet
  def constrainIsType(name:String, hierarchyConstraints: ClassHierarchyConstraints):TypeSet
  def setInterfaces(iFaces:Set[String]):TypeSet
  def isEmpty(hierarchyConstraints: ClassHierarchyConstraints):Boolean

}
object TypeSet{
  implicit var rw:RW[TypeSet] = RW.merge(macroRW[EmptyTypeSet.type], BoundedTypeSet.rw, DisjunctTypeSet.rw)
  def isClass(className: String, ch:ClassHierarchyConstraints) = {
    if(ch.isInterface(className))
      throw new IllegalArgumentException(s"$className is an interface")
    BoundedTypeSet(Some(className), Some(className), Set())
  }

  def subclassOf(name:String, hierarchyConstraints: ClassHierarchyConstraints):TypeSet = {
    if(hierarchyConstraints.isInterface(name))
      BoundedTypeSet(None,None,Set(name))
    else
      BoundedTypeSet(upper = Some(name),None,Set())
  }
}
case object EmptyTypeSet extends TypeSet {
  override def constrainSubtypeOf(name: String, hc: ClassHierarchyConstraints): TypeSet = EmptyTypeSet
  override def constrainSupertypeOf(name: String, hc: ClassHierarchyConstraints): TypeSet = EmptyTypeSet
  override def constrainIsType(name: String, hc: ClassHierarchyConstraints): TypeSet = EmptyTypeSet
  override def isEmpty(hierarchyConstraints:ClassHierarchyConstraints): Boolean = true

  override def contains(set: TypeSet)(implicit ch:ClassHierarchyConstraints): Boolean = set match{
    case EmptyTypeSet => true
    case _ => false
  }

  override def subtypeOfCanAlias(localType: String, ch: ClassHierarchyConstraints): Boolean = false

  override def typeSet(ch: ClassHierarchyConstraints): Set[String] = Set()

  override def join(tc2: TypeSet, ch:ClassHierarchyConstraints): TypeSet = tc2

  override def setInterfaces(iFaces: Set[String]): TypeSet = EmptyTypeSet
}

case class BoundedTypeSet(upper:Option[String], lower:Option[String], interfaces: Set[String]) extends TypeSet{
  override def toString:String = (upper,lower) match{
    case (Some(upper),Some(lower)) => s"<:$upper >:$lower" + interfaces.headOption.map("<: I( " + _ + ")").getOrElse("")
    case (Some(upper),None) => s"<:$upper" + interfaces.headOption.map("<: I( " + _ + ")").getOrElse("")
    case (None,Some(lower)) => s">:$lower" + interfaces.headOption.map("<: I( " + _ + ")").getOrElse("")
    case (None,None) => s":none " + interfaces.headOption.map("<: I( " + _ + ")").getOrElse("")

  }
  override def constrainSubtypeOf(name: String, hierarchyConstraints: ClassHierarchyConstraints): TypeSet = {
    val newTS = if(hierarchyConstraints.isInterface(name))
      this.copy(interfaces = interfaces + name)
    else {
      upper match{
        case Some(v) if hierarchyConstraints.getSubtypesOf(name).contains(v) => this
        case Some(v) if hierarchyConstraints.getSubtypesOf(v).contains(name) => this.copy(upper = Some(name))
        case None => this.copy(upper = Some(name))
        case _ => EmptyTypeSet
      }
    }
    if(newTS.isEmpty(hierarchyConstraints)) EmptyTypeSet else newTS
  }

  override def constrainSupertypeOf(name: String, hierarchyConstraints: ClassHierarchyConstraints): TypeSet = {
    if(hierarchyConstraints.isInterface(name))
      throw new IllegalArgumentException(s"$name is an interface")
    val newTS = lower match{
      case Some(v) if hierarchyConstraints.getSubtypesOf(v).contains(name) => this
      case Some(v) if hierarchyConstraints.getSubtypesOf(name).contains(v) => this.copy(lower = Some(name))
      case None => this.copy(lower = Some(name))
      case _ =>
        EmptyTypeSet
    }
    if(newTS.isEmpty(hierarchyConstraints)) EmptyTypeSet else newTS
  }

  override def constrainIsType(name: String, hierarchyConstraints: ClassHierarchyConstraints): TypeSet = {
    if(lower.exists(!hierarchyConstraints.getSubtypesOf(name).contains(_)))
      return EmptyTypeSet // name doesn't contain lower bound as subclass
    if(upper.exists(!hierarchyConstraints.getSubtypesOf(_).contains(name)))
      return EmptyTypeSet // name isn't a subclass of upper
    if(interfaces.exists(iface => !hierarchyConstraints.getSubtypesOf(iface).contains(name)))
      return EmptyTypeSet // name doesn't implement one of the interfaces
    this.copy(upper = Some(name), lower = Some(name))
  }

  private var empty:Option[Boolean] = None
  override def isEmpty(hierarchyConstraints: ClassHierarchyConstraints): Boolean = {
    if(empty.isDefined)
      return empty.get
    val shouldBeSubClassOfAll = interfaces ++ upper
    assert(shouldBeSubClassOfAll.nonEmpty, "Empty type constraint")
    val typeSets = shouldBeSubClassOfAll.toList.map(hierarchyConstraints.getSubtypesOf)
    @tailrec
    def isIntersectEmpty(typeSets:List[Set[String]], acc: Set[String]):Boolean = {
      if(acc.isEmpty)
        return true // no types can satisfy all constraints
      if(typeSets.nonEmpty) {
        isIntersectEmpty(typeSets.tail, acc.intersect(typeSets.head))
      }else
        false
    }
    val res = lower match{
      case None => isIntersectEmpty(typeSets.tail, typeSets.head)
      case Some(v) => isIntersectEmpty(typeSets, hierarchyConstraints.getSupertypesOf(v))
    }
    empty = Some(res)
    res
  }


  override def contains(set: TypeSet)(implicit ch: ClassHierarchyConstraints): Boolean =
    set match{
      case EmptyTypeSet => false
      case BoundedTypeSet(upperBound, lowerBound, iface) =>
        val s2: TypeSet = this.optionalConstrainUpper(upperBound,ch).optionalConstrainLower(lowerBound,ch)
        !iface.foldLeft(s2){case (acc,v) => acc.constrainSubtypeOf(v,ch)}.isEmpty(ch)
      case DisjunctTypeSet(oneOf) => oneOf.forall(ts => this.contains(ts))
    }

  override def subtypeOfCanAlias(localType: String, ch: ClassHierarchyConstraints): Boolean = {
    this.constrainIsType(localType,ch) match{
      case EmptyTypeSet => false
      case _ => true
    }
  }

  override def typeSet(ch: ClassHierarchyConstraints): Set[String] = {
    val subtypes = (interfaces ++ upper).map(ch.getSubtypesOf)
    val cSub = subtypes.reduce((acc,v) => acc.intersect(v))
    lower match{
      case Some(l) => cSub.intersect(ch.getSupertypesOf(l))
      case None => cSub
    }
  }

  override def join(tc2: TypeSet, ch:ClassHierarchyConstraints): TypeSet = {
    val merged:TypeSet = tc2 match{
      case EmptyTypeSet => EmptyTypeSet
      case BoundedTypeSet(Some(upper), Some(lower), ifaces) =>
        val upperc = this.constrainSubtypeOf(upper,ch)
        val lowerc = upperc.constrainSupertypeOf(lower,ch)
        lowerc.setInterfaces(ifaces ++ this.interfaces)
      case BoundedTypeSet(Some(upper), None, ifaces) =>
        val upperc: TypeSet = this.constrainSubtypeOf(upper,ch)
        upperc.setInterfaces(ifaces ++ this.interfaces)
      case BoundedTypeSet(None, Some(lower), ifaces) =>
        val lowerc = this.constrainSupertypeOf(lower,ch)
        lowerc.setInterfaces(ifaces ++ this.interfaces)
      case BoundedTypeSet(None,None,ifaces) =>
        this.setInterfaces(ifaces)
      case dts@DisjunctTypeSet(_) => dts.join(this,ch)
    }
    if(merged.isEmpty(ch)){
      EmptyTypeSet
    }else
      merged
  }

  override def setInterfaces(iFaces: Set[String]): TypeSet = this.copy(interfaces = iFaces)
}
object BoundedTypeSet{
  implicit var rw:RW[BoundedTypeSet] = macroRW
}
case class DisjunctTypeSet(oneOf: Set[TypeSet]) extends TypeSet{
  override def toString():String = {
    oneOf.headOption.map(_.toString() + " disj").getOrElse(":nonedisj")
  }
  private def filterOp(op: TypeSet => TypeSet):TypeSet = {
    val outSet = oneOf.map(op).filter{
      case EmptyTypeSet => false
      case _ => true
    }
    if(outSet.isEmpty)
      EmptyTypeSet
    else
      DisjunctTypeSet(outSet)
  }
  override def constrainSubtypeOf(name: String, hierarchyConstraints: ClassHierarchyConstraints): TypeSet = {
    filterOp(ts => ts.constrainSubtypeOf(name,hierarchyConstraints))
  }

  override def constrainSupertypeOf(name: String, hierarchyConstraints: ClassHierarchyConstraints): TypeSet = {
    filterOp(ts => ts.constrainSupertypeOf(name,hierarchyConstraints))
  }

  override def constrainIsType(name: String, hierarchyConstraints: ClassHierarchyConstraints): TypeSet = {
    filterOp(ts => ts.constrainIsType(name,hierarchyConstraints))
  }

  override def isEmpty(hierarchyConstraints: ClassHierarchyConstraints): Boolean =
    oneOf.exists(v => v.isEmpty(hierarchyConstraints))

  override def subtypeOfCanAlias(localType: String, ch: ClassHierarchyConstraints): Boolean =
    oneOf.exists(_.subtypeOfCanAlias(localType,ch))

  override def contains(set: TypeSet)(implicit ch: ClassHierarchyConstraints): Boolean = set match{
    case d:DisjunctTypeSet if this == d => true
    case DisjunctTypeSet(otherOneOf) =>
      //TODO: this is likely to be slow
      otherOneOf.forall(other => oneOf.exists(thisD => thisD.contains(other)))
    case _ => oneOf.exists(_.contains(set))
  }

  override def typeSet(ch: ClassHierarchyConstraints): Set[String] =
    oneOf.flatMap(_.typeSet(ch))

  override def join(tc2: TypeSet, ch:ClassHierarchyConstraints): TypeSet =
    this.copy(oneOf = oneOf.map(_.join(tc2,ch)))

  override def setInterfaces(iFaces: Set[String]): TypeSet = this.copy(oneOf.map(_.setInterfaces(iFaces)))
}
object DisjunctTypeSet{
  implicit var rw:RW[DisjunctTypeSet] = macroRW
}

//TODO: this case class is getting to the point where pattern matches are unreadable
/**
 *
 * @param callStack Application only call stack abstraction, emtpy stack or callin on top means framework control.
 * @param heapConstraints Separation logic heap representation
 * @param pureFormula Constraints on values in separation logic formula including:
 *                    - null/not null
 *                    - type bounds
 * @param traceAbstraction Trace required to reach this point in the program execution
 * @param nextAddr Int val of next pure val to be declared
 * @param nextCmd Command just processed while executing backwards.
 */
case class State(callStack: List[CallStackFrame],
                 heapConstraints: Map[HeapPtEdge, PureExpr],
                 pureFormula: Set[PureConstraint],
                 typeConstraints: Map[PureVar, TypeSet],
                 traceAbstraction: Set[AbstractTrace],
                 nextAddr:Int,
                 nextCmd: Option[AppLoc] = None) {

//  if(!typeConstraints.keySet.forall{case PureVar(id) => id < nextAddr}){
//    assert(false)
//  }

  def constrainOneOfType(pv: PureVar, classNames: Set[String], ch:ClassHierarchyConstraints):State = {
    if(typeConstraints.contains(pv)){
      val oldTc = typeConstraints(pv)
      val constraints = classNames.map{className => oldTc.constrainSubtypeOf(className,ch)}
      val flatConstraints = constraints.flatMap{
        case DisjunctTypeSet(oneOf) => oneOf
        case v => Set(v)
      }
      this.copy(typeConstraints = typeConstraints + (pv -> DisjunctTypeSet(flatConstraints)))
    }else {
      val constraints = classNames.map { className =>
        TypeSet.subclassOf(className,ch)
      }
      this.copy(typeConstraints = typeConstraints + (pv -> DisjunctTypeSet(constraints)))
    }
  }

  def constrainIsType(pv: PureVar, className: String, ch: ClassHierarchyConstraints): State = {
    val newTC = typeConstraints.get(pv) match{
      case Some(v) => v.constrainIsType(className,ch)
      case None => TypeSet.isClass(className,ch)
    }
    this.copy(typeConstraints = typeConstraints + (pv->newTC))
  }

  def constrainUpperType(pv:PureVar, clazz:String, hierarchy:ClassHierarchyConstraints):State = {
    val newTC = typeConstraints.get(pv) match{
      case Some(v) => v.constrainSubtypeOf(clazz,hierarchy)
      case None => TypeSet.subclassOf(clazz,hierarchy)
    }
    this.copy(typeConstraints = typeConstraints + (pv -> newTC))
  }

  /**
   * Use for over approximate relevant methods
   * @return set of field names that could be referenced by abstract state
   */
  def fieldNameSet():Set[String] = heapConstraints.keySet.flatMap{
    case FieldPtEdge(_,fieldName) => Some(fieldName)
    case StaticPtEdge(_, fieldName) => Some(fieldName)
    case ArrayPtEdge(_,_) => None
  }

  /**
   * Use for over approximate relevant methods
   * @return set of simple method names referenced by trace abstraction
   */
  def traceMethodSet():Set[String] =
    traceAbstraction.flatMap{ at =>
      val allISet = SpecSpace.allI(at.a)
      allISet.flatMap(i => i.signatures.map(_._2))
    }

  def entryPossible(loc: Loc): Boolean = loc match{
    case CallbackMethodInvoke(clazz, name, _) =>
      callStack.headOption match{
        case Some(CallStackFrame(CallbackMethodReturn(clazz2, name2,_,_),_,_)) =>
          clazz == clazz2 && name == name2
        case None => true
        case _ => false
      }
    case InternalMethodInvoke(clazz,name,_) =>
      callStack.headOption match{
        case Some(CallStackFrame(InternalMethodReturn(clazz2, name2,_),_,_)) =>
          clazz == clazz2 && name == name2
        case None => true
        case _ => false
      }
    case v => throw new IllegalStateException(s"$v is not a entry location")
  }

  var isSimplified = false
  def setSimplified(): State = {
    isSimplified = true
    this
  }

  def setNextCmd(cmd: Option[AppLoc]):State = this.copy(nextCmd = cmd)

  def nextPv() = (PureVar(nextAddr), this.copy(nextAddr = nextAddr+1))

  def lsVarConstraint(f: AbstractTrace, lsvar: String): Option[LSParamConstraint] = f match{
    case AbstractTrace(_,_,mv) => mv.get(lsvar).map(LSPure)
  }

  def findIFromCurrent(dir: MessageType, signature: (String, String)): Set[(I, List[LSParamConstraint])] = {
    //TODO: constant constraints
    traceAbstraction.flatMap(ar =>{
      val iset = findIAF(dir,signature,ar.a)
      iset.map(i => (i, i.lsVars.map{
        case LifeState.LSVar(mv) =>
          ar.modelVars.get(mv).map(LSPure).getOrElse(LSModelVar(mv,ar))
        case LifeState.LSConst(constV) => LSConstConstraint(constV, ar)
        case LifeState.LSAnyVal() => LSAny
      }))
    })
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
  private def formulaVars(trace: AbstractTrace):Set[PureVar] = {
    tformulaVars(trace.a).union(trace.modelVars.flatMap{
      case (_,v) => pformulaVars(v)
    }.toSet)
  }
  def allTraceVar():Set[PureVar] = traceAbstraction.flatMap(formulaVars)

  override def toString:String = {
    def sfString(sfl:List[CallStackFrame], frames: Int):String = (sfl,frames) match{
      case (sf::t, fr) if fr > 0 =>
        val locals: Map[StackVar, PureExpr] = sf.locals
        s"${sf.methodLoc.msgSig.getOrElse("")} " +
          s"locals: " + locals.map(k => k._1.toString + " -> " + k._2.toString).mkString(",") + "     " +
          sfString(t, fr-1)
      case (Nil,_) => ""
      case (_::_,_) => "..."
    }
    val stackString = sfString(callStack, 2)

    val heapString = s"   heap: ${heapConstraints.map(a => a._1.toString + "->" +  a._2.toString).mkString(" * ")}    "
    val pureFormulaString = "   pure: " + pureFormula.map(a => a.toString).mkString(" && ") +"    "
    val traceString = s"   trace: ${traceAbstraction.mkString(" ; ")}"
    val typeString = s"    types: ${typeConstraints.map{case (k,v) => k.toString + ":" + v.toString}}"
    s"($stackString $heapString   $pureFormulaString $typeString $traceString)"
  }
  def containsLocal(localWrapper: LocalWrapper):Boolean = {
    val sVar = StackVar(localWrapper.name)
    callStack.headOption.exists(f => f.locals.contains(sVar))
  }

  private def pureExprSwap[T<:PureExpr](oldPv : PureVar, newPv : PureVar, expr:T): T = expr match{
    case PureVar(id) if id==oldPv.id => newPv.asInstanceOf[T]
    case pv@PureVar(_) => pv.asInstanceOf[T]
    case pv: PureVal => pv.asInstanceOf[T]
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
    val nmv = tr.modelVars.map{
      case (k,v) => (k,pureExprSwap(oldPv, newPv, v))
    }
    tr.copy(modelVars = nmv)
  }

  /**
   *
   * @param oldPv
   * @param newPv
   */
  def swapPv(oldPv : PureVar, newPv: PureVar):State = {
    if(oldPv == newPv)
      this
    else {
      this.copy(
        callStack = callStack.map(f => stackSwapPv(oldPv, newPv, f)),
        heapConstraints = heapConstraints.map(hc => heapSwapPv(oldPv, newPv, hc)),
        pureFormula = pureFormula.map(pf => pureSwapPv(oldPv, newPv, pf)),
        traceAbstraction = traceAbstraction.map(ta => traceSwapPv(oldPv, newPv, ta)),
        typeConstraints = typeConstraints.map {
          case (k, v) if k == oldPv => (newPv, v)
          case (k, v) => (k, v)
        }
      )
    }
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
      val freshPv = PureVar(nextAddr)
      val sFresh = this.copy(nextAddr = nextAddr + 1).swapPv(newPv, freshPv)
      sFresh.swapPv(oldPv, newPv)
    }
  }

  // helper functions to find pure variable
  private def expressionContains(expr: PureExpr, pureVar: PureVar):Boolean = expr match {
    case p2@PureVar(_) => pureVar == p2
    case _ => false
  }
  private def callStackContains(p :PureVar):Boolean = {
    callStack.exists({
      case CallStackFrame(_,_,locals) => locals.exists(r => expressionContains(r._2,p))
    })
  }

  private def ptEdgeContains(edge: HeapPtEdge, p: PureVar): Boolean = edge match{
    case FieldPtEdge(p2, _) => p == p2
    case _ => ???
  }

  private def heapContains(p:PureVar):Boolean =
    heapConstraints.exists(r => expressionContains(r._2,p) || ptEdgeContains(r._1,p))

  private def pureFormulaContains(p: PureVar): Boolean =
    pureFormula.exists(c => expressionContains(c.lhs,p) || expressionContains(c.rhs,p))

  def traceAbstractionContains(p: PureVar): Boolean = {
    traceAbstraction.exists(_.modelVars.exists{
      case (k,v) if v == p => true
      case _ => false
    })
  }

  def contains(p:PureVar):Boolean = {
     callStackContains(p) || heapContains(p) || pureFormulaContains(p) || traceAbstractionContains(p)
  }
  // If an RVal exists in the state, get it
  // for a field ref, e.g. x.f if x doesn't exist, create x
  // if x.f doesn't exist and x does
  def get(l:RVal):Option[PureExpr] = l match {
    case LocalWrapper(name,_) =>
      callStack match{
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
    case l =>
      println(l)
      ???
  }
  // TODO: does this ever need to "clobber" old value?
  //TODO: refactor so local always points to pv
  def defineAs(l : RVal, pureExpr: PureExpr)(implicit ch:ClassHierarchyConstraints): State = l match{
    case LocalWrapper(localName, localType) =>
      val cshead: CallStackFrame = callStack.headOption.getOrElse{
        throw new IllegalStateException("Expected non-empty stack")
      }
      if(cshead.locals.contains(StackVar(localName))){
        val v = cshead.locals.get(StackVar(localName))
        this.copy(pureFormula = pureFormula + PureConstraint(v.get , Equals, pureExpr))
      }else {
        val csheadNew = cshead.copy(locals = cshead.locals + (StackVar(localName) -> pureExpr))
        pureExpr match {
          case pureVar:PureVar =>
            this.copy(callStack = csheadNew :: callStack.tail).constrainUpperType (pureVar, localType, ch)
          case v =>
            println(s"TODO: defineAs used on value: ${v}")
            ???
        }
//          pureFormula = pureFormula + PureConstraint(pureExpr, TypeComp, SubclassOf(localType)))
      }
    case v if v.isConst =>
      val v2 = get(v).get
      this.copy(pureFormula = this.pureFormula + PureConstraint(v2, Equals, pureExpr))
    case v =>
      println(v)
      ???
  }

  //TODO: this should probably be the behavior of getOrDefine, refactor later
  def getOrDefine2(l : RVal)(implicit ch:ClassHierarchyConstraints): (PureExpr, State) = l match{
    case l:LocalWrapper => getOrDefine(l)
    case v if v.isConst => (get(l).getOrElse(???),this)
    case _ =>
      ???
  }
  def getOrDefine(l : RVal)(implicit ch: ClassHierarchyConstraints): (PureVar,State) = l match{
    case LocalWrapper(name,localType) =>
      val cshead = callStack.headOption.getOrElse(???) //TODO: add new stack frame if empty?
      val cstail = if (callStack.isEmpty) Nil else callStack.tail
      cshead.locals.get(StackVar(name)) match {
        case Some(v@PureVar(_)) => (v, this)
        case None =>
          val newident = PureVar(nextAddr)
//          (newident, State(
//            callStack = cshead.copy(locals = cshead.locals + (StackVar(name) -> newident)) :: cstail,
//            heapConstraints,
//            pureFormula + PureConstraint(newident, TypeComp, SubclassOf(localType)),
//            traceAbstraction,
//            nextAddr + 1
//          ))
          val newStack = cshead.copy(locals = cshead.locals + (StackVar(name) -> newident)) :: cstail
          (newident, this.copy(callStack = newStack, nextAddr = nextAddr + 1).constrainUpperType(newident, localType, ch))
      }
    case v =>
      ??? //TODO: should probably restrict this function to only take locals
  }

  /**
   * When a var is assigned, we remove it from our constraint set
   * @param l variable being assigned
   * @return new state
   */
  def clearLVal(l : LVal): State = (l,callStack) match {
    case (LocalWrapper(name,_), cshead::cstail) =>
      val newCsHead = cshead.removeStackVar(StackVar(name))
      this.copy(newCsHead::cstail)
    case _ =>
      ???
  }

  def clearPureVar(p:PureVar):State = {
    ???
  }

  private var pvCache:Option[Set[PureVar]] = None
  def pureVars():Set[PureVar] = {
    val out = pvCache match{
      case None =>
        val computed = iPureVars()
        pvCache = Some(computed)
        computed
      case Some(v) => v
    }
    out
  }

  private def iPureVars():Set[PureVar] = {
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
    val pureVarFromTrace = traceAbstraction.flatMap{
      case AbstractTrace(_, _, modelVars) => modelVars.collect{case (_,pv: PureVar) => pv}
    }
    pureVarFromHeap ++ pureVarFromLocals ++ pureVarFromConst ++ typeConstraints.keySet ++ pureVarFromTrace
  }
  def isNull(pv:PureVar):Boolean = {
    pureFormula.contains(PureConstraint(pv,Equals,NullVal))
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
case object TypeComp extends CmpOp{
  override def toString:String = ""
}

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
sealed abstract class PureVal(v:Any) extends PureExpr {
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
}
case object PureVal{
  implicit val rw:RW[PureVal] = RW.merge(
    macroRW[NullVal.type], macroRW[TopVal.type],
    macroRW[IntVal],macroRW[BoolVal],macroRW[StringVal])
}

case object NullVal extends PureVal{
  override def toString:String = "NULL"
}
case class IntVal(v : Int) extends PureVal(v)
case class BoolVal(v : Boolean) extends PureVal(v)
case class StringVal(v : String) extends PureVal(v)
case class ClassVal(name:String) extends PureVal(name)
case object TopVal extends PureVal(null)

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
sealed case class PureVar(id:Int) extends PureExpr {
//  val id : Int = State.getId()
  override def getVars(s : Set[PureVar]) : Set[PureVar] = s + this

  override def substitute(toSub : PureExpr, subFor : PureVar) : PureExpr = if (subFor == this) toSub else this

  override def hashCode : Int = id*100271
  override def equals(other : Any) : Boolean = other match {
    case p : PureVar => this.id == p.id
    case _ => false
  }
  override def toString : String = "p-" + id
}
object PureVar{
  implicit val rw:RW[PureVar] = macroRW
}
