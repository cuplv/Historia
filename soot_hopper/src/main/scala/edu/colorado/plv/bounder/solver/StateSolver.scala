package edu.colorado.plv.bounder.solver

import com.microsoft.z3.Solver
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{BitTypeSet, TAddr, TMessage, TNullVal, TopTypeSet, TypeSet, WitnessExplanation}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecSpace}
import edu.colorado.plv.bounder.lifestate.LifeState._
import edu.colorado.plv.bounder.symbolicexecutor.state.{HeapPtEdge, _}
import org.slf4j.LoggerFactory
import upickle.default.{read, write}

import scala.collection.immutable

trait Assumptions

class UnknownSMTResult(msg : String) extends Exception(msg)
trait SolverCtx[T]{
  def mkAssert(t:T):Unit
}

/** SMT solver parameterized by its AST or expression type */
trait StateSolver[T, C <: SolverCtx[T]] {
  private val logger = LoggerFactory.getLogger(classOf[StateSolver[T, C]])

  // checking
  def getSolverCtx: C

  def checkSAT()(implicit zctx: C): Boolean

  def push()(implicit zctx: C): Unit

  def pop()(implicit zctx: C): Unit

  def reset()(implicit zctx: C): Unit

  /**
   * Write debugging info, delete if cont finishes without failure
   * Used to debug native crashes in solver
   *
   * @param cont call solver code in continuation, return result
   * @param zctx solver context and state
   */
  protected def dumpDbg[V](cont: () => V)(implicit zctx: C): V


  // quantifiers
  /**
   * forall int condition is true
   *
   * @param cond condition inside the forall statement
   */
  @deprecated //TODO: remove int for performance/decidability
  protected def mkForallInt(min: T, max: T, cond: T => T)(implicit zctx: C): T

  protected def mkForallIndex(min: T, max: T, cond: T => T)(implicit zctx: C): T

  protected def mkForallIndex(cond: T => T)(implicit zctx: C): T

  protected def mkForallAddr(name: String, cond: T => T)(implicit zctx: C): T

  protected def mkForallAddr(name: Map[String, Option[T]], cond: Map[String, T] => T, solverNames: Set[T] = Set())(implicit zctx: C): T

  protected def mkExistsAddr(name: String, cond: T => T)(implicit zctx: C): T

  protected def mkExistsAddr(name: Map[String,Option[T]], cond: Map[String, T] => T, solverNames: Set[T] = Set())(implicit zctx: C): T

  @deprecated
  protected def mkExistsInt(min: T, max: T, cond: T => T)(implicit zctx: C): T

  protected def mkExistsIndex(min: T, max: T, cond: T => T)(implicit zctx: C): T

  protected def mkLTEIndex(ind1: T, ind2: T)(implicit zctx: C): T

  protected def mkLTIndex(ind1: T, ind2: T)(implicit zctx: C): T

  protected def mkAddOneIndex(ind: T)(implicit zctx: C): (T, T)

  protected def mkZeroIndex()(implicit zctx: C): T

  @deprecated
  protected def mkMaxInd(ind: T)(implicit zctx: C): Unit

  // comparison operations
  protected def mkEq(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkNe(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkLt(lhs: T, rhs: T)(implicit zctx: C): T

  // logical and arithmetic operations
  protected def mkImplies(t: T, t1: T)(implicit zctx: C): T

  protected def mkNot(o: T)(implicit zctx: C): T

  @deprecated
  protected def mkAdd(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkSub(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkAnd(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkAnd(t: List[T])(implicit zctx: C): T

  protected def mkOr(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkOr(t: Iterable[T])(implicit zctx: C): T

  // creation of variables, constants, assertions
  protected def mkIntVal(i: Int)(implicit zctx: C): T

  protected def mkBoolVal(b: Boolean)(implicit zctx: C): T

  @deprecated
  protected def mkIntVar(s: String)(implicit zCtx: C): T

  protected def mkLenVar(s: String)(implicit zCtx: C): T

  protected def mkAddrVar(pv: PureVar)(implicit zCtx: C): T

  protected def mkFreshIntVar(s: String)(implicit zCtx: C): T

  protected def mkModelVar(s: String, predUniqueID: String)(implicit zCtx: C): T // model vars are scoped to trace abstraction

  protected def fieldEquals(fieldFun: T, t1: T, t2: T)(implicit zCtx: C): T

  protected def solverSimplify(t: T,
                               state: State,
                               messageTranslator: MessageTranslator, logDbg: Boolean = false)(implicit zctx: C): Option[T]

  protected def mkTypeConstraints(types: Set[Int])(implicit zctx: C): (T, Map[Int, T])

  protected def mkLocalDomain(locals: Set[(String, Int)])(implicit zctx: C): (T, Map[(String, Int), T])

  protected def mkConstConstraintsMap(pvs: Set[PureVal])(implicit zctx: C): (T, Map[PureVal, T])

  protected def mkTypeConstraintForAddrExpr(typeFun: T, typeToSolverConst: Map[Int, T],
                                            addr: T, tc: Set[Int])(implicit zctx: C): T

  protected def createTypeFun()(implicit zctx: C): T

  protected def mkUT(name: String, types: List[String])(implicit zctx: C): Map[String, T]

  protected def mkTraceFn(uid: String)(implicit zctx: C): T

  protected def mkFreshTraceFn(uid: String)(implicit zctx: C): T

  protected def mkLocalFn(uid: String)(implicit zctx: C): T

  protected def mkLocalConstraint(localIdent: T, equalTo: T, uid: String)(implicit zctx: C): T

  protected def mkDynFieldFn(uid: String, fieldName: String)(implicit zctx: C): T

  protected def mkDynFieldConstraint(base: T, fieldName: String, equalTo: T, uid: String)(implicit zctx: C): T

  protected def mkStaticFieldConstraint(clazz: String, fieldName: String, equalTo: T, uid: String)(implicit zctx: C): T

  // function msg -> iname
  protected def mkINameFn()(implicit zctx: C): T

  // function for argument i -> msg -> addr
  protected def mkArgFun()(implicit zctx: C): T

  /**
   * Attempt to limit Uint and msg to fix z3 timeout
   *
   * @param n
   * @param zCtx
   * @return
   */
  protected def mkMaxMsgUint(n: Int)(implicit zCtx: C): T

  //  // function to test if addr is null
  //  // Uses uninterpreted function isNullFn : addr -> bool
  //  protected def mkIsNull(addr: T)(implicit zctx: C): T
  //
  //  protected def mkIntValueConstraint(addr:T)(implicit zctx: C): T
  //
  protected def mkConstValueConstraint(addr: T)(implicit zctx: C): T

  // Get enum value for I based on index
  protected def mkIName(enum: T, enumNum: Int)(implicit zctx: C): T

  // function from index to message (message is at index in trace)
  protected def mkTraceConstraint(traceFun: T, index: T)(implicit zctx: C): T

  // function msg -> funname
  protected def mkNameConstraint(nameFun: T, msg: T)(implicit zctx: C): T

  // function argumentindex -> msg -> argvalue
  protected def mkArgConstraint(argFun: T, argIndex: Int, msg: T)(implicit zctx: C): T

  protected def mkAllArgs(msg: T, pred: T => T)(implicit zctx: C): T

  protected def mkExistsArg(argFun: T, msg: T, pred: T => T)(implicit zctx: C): T

  protected def mkAddrConst(i: Int)(implicit zctx: C): T

  def printDbgModel(messageTranslator: MessageTranslator, traceabst: Set[AbstractTrace],
                    lenUID: String)(implicit zctx: C): Unit
  def explainWitness(messageTranslator:MessageTranslator,
                     pvMap: Map[PureVar, Option[T]])(implicit zCtx:C): WitnessExplanation
  def compareConstValueOf(rhs: T, op: CmpOp, pureVal: PureVal, constMap: Map[PureVal, T])(implicit zctx: C): T = {
    (pureVal, op) match {
      case (TopVal, _) => mkBoolVal(b = true)
      case (ClassVal(_), _) => mkBoolVal(b = true) //TODO: add class vals if necessary for precision
      case (v: PureVal, Equals) =>
        if(!constMap.contains(v)) //TODO: Remove
          ???
        mkEq(constMap(v), mkConstValueConstraint(rhs))
      case (v: PureVal, NotEquals) => mkNot(mkEq(constMap(v), mkConstValueConstraint(rhs)))
      case (_: PureVal, _) => mkBoolVal(b = true)
      case v =>
        println(v)
        ???
    }
  }

  def toAST(p: PureConstraint, constMap: Map[PureVal, T], pvMap: Map[PureVar, T])(implicit zctx: C): T = p match {
    // TODO: field constraints based on containing object constraints
    case PureConstraint(v: PureVal, op, rhs) => compareConstValueOf(toAST(rhs, pvMap), op, v, constMap)
    case PureConstraint(lhs, op, v: PureVal) => compareConstValueOf(toAST(lhs, pvMap), op, v, constMap)
    case PureConstraint(lhs, op, rhs) =>
      toAST(toAST(lhs, pvMap), op, toAST(rhs, pvMap))
    case _ => ???
  }

  def toAST(p: PureExpr, pvMap: Map[PureVar, T])(implicit zctx: C): T = p match {
    case p: PureVar => pvMap(p)
    case _ => throw new IllegalStateException("Values should be handled at a higher level")
  }

  def toAST(lhs: T, op: CmpOp, rhs: T)(implicit zctx: C): T = op match {
    case Equals => mkEq(lhs, rhs)
    case NotEquals =>
      mkNe(lhs, rhs)
    case _ =>
      ???
  }

  def getArgAt(index: T, argNum: Int, traceFn: T)(implicit zCtx: C): T = {
    val msgExpr = mkTraceConstraint(traceFn, index)
    mkArgConstraint(mkArgFun(), argNum, msgExpr)
  }

  /**
   * Formula representing truth of "m is at position index in traceFn"
   *
   * @param index             index of the message (ArithExpr)
   * @param m                 observed message
   * @param messageTranslator mapping from observed messages to z3 representation
   * @param traceFn           : Int->Msg
   * @return
   */
  private def assertIAt(index: T, m: I,
                        messageTranslator: MessageTranslator,
                        traceFn: T, // Int -> Msg
                        negated: Boolean = false,
                        lsTypeMap: Map[String, TypeSet],
                        typeToSolverConst: Map[Int, T],
                        modelVarMap: String => T)(implicit zctx: C): T = {
    val msgExpr = mkTraceConstraint(traceFn, index)
    val nameFun = messageTranslator.nameFun
    val nameConstraint = mkEq(mkNameConstraint(nameFun, msgExpr), messageTranslator.enumFromI(m))
    val argConstraints = m.lsVars.zipWithIndex.flatMap {
      case (LSAnyVal(), _) => None //TODO: primitive value cases
      case (msgVar, ind) =>
        //        val modelVar = modelVarMap(msgVar)
        val modelExpr = encodeModelVarOrConst(msgVar, modelVarMap)
        val argAt = mkArgConstraint(mkArgFun(), ind, msgExpr)
        val typeConstraint = lsTypeMap.get(msgVar) match {
          case Some(BitTypeSet(s)) =>
            mkTypeConstraintForAddrExpr(createTypeFun(), typeToSolverConst, argAt, s.toSet)
          case _ => mkBoolVal(b = true)
        }
        Some(mkAnd(
          mkEq(argAt, modelExpr),
          typeConstraint
        ))
    }

    // w[i] = cb foo(x,y)
    // If we are asserting that a message is not at a location, the arg function cannot be negated
    // We only negate the name function
    if (negated) {
      val nameConstraints = mkNot(nameConstraint)
      mkOr(nameConstraints, mkOr(argConstraints.map(mkNot)))
    } else {
      mkAnd(nameConstraint, mkAnd(argConstraints))
    }
  }

  private def encodeModelVarOrConst(lsExpr: String, modelVarMap: String => T)(implicit zctx: C): T = lsExpr match {
    case LifeState.LSVar(v) => modelVarMap(v)
    case LifeState.LSConst(const) =>
      toAST(const, ???)
    case LifeState.LSAnyVal() =>
      throw new IllegalStateException("AnyVal shouldn't reach here")
  }

  /**
   * Value is at least one argument of message
   *
   * @param msg     target message
   * @param v       value at one position
   * @param negated true - value contained in message, false - value not contained in message
   * @param zCtx    - solver context
   * @return
   */
  @Deprecated
  def mkValContainedInMsg(msg: T, v: T, negated: Boolean)(implicit zCtx: C): T = {
    val argF = mkArgFun()
    if (negated) {
      mkAllArgs(msg, arg => mkNe(arg, v))
      ???
    } else {
      mkExistsArg(argF, msg, arg => mkEq(arg, v))
      ???
    }
  }

  private def encodePred(combinedPred: LifeState.LSPred, traceFn: T, len: T,
                         messageTranslator: MessageTranslator,
                         modelVarMap: String => T,
                         typeToSolverConst: Map[Int, T],
                         typeMap: Map[String, TypeSet],
                         constMap:Map[PureVal, T],
                         negate: Boolean = false)(implicit zctx: C): T = {
    val res = combinedPred match {
      case Forall(h::t, p) =>
        mkForallAddr(h, (v:T) => {
          val newModelVarMap:String => T = s => if(s == h) v else modelVarMap(s)
          encodePred(Forall(t, p), traceFn, len, messageTranslator, newModelVarMap, typeToSolverConst, typeMap,
            constMap, negate)
        })
      case Exists(h::t, p) =>
        mkExistsAddr(h, (v:T) => {
          val newModelVarMap:String => T = s => if(s == h) v else modelVarMap(s)
          encodePred(Exists(t, p), traceFn, len, messageTranslator, newModelVarMap, typeToSolverConst, typeMap,
            constMap, negate)
        })
      case Forall(Nil, p) =>
        encodePred(p, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap, negate)
      case Exists(Nil, p) =>
        encodePred(p, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap, negate)
      case LSImplies(l1,l2) if !negate => mkImplies(
        encodePred(l1, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap),
        encodePred(l2, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap)
      )
      case LSImplies(l1,l2) if negate =>
        // ¬(a=>b) =equiv ¬(¬a\/b) =equiv a/\¬b
        val encL1 = encodePred(l1, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap,
          negate = false)
        val encL2 = encodePred(l2, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap,
          negate = true)
        mkAnd(encL1,encL2)
      case LSConstraint(LSVar(v1), Equals,LSVar(v2)) if !negate =>
        mkEq(modelVarMap(v1), modelVarMap(v2))
      case LSConstraint(LSVar(v1), op, LSConst(c)) =>
        compareConstValueOf(modelVarMap(v1), op, c, constMap)
      case LSConstraint(c@LSConst(_), Equals, LSVar(v1)) =>
        encodePred(LSConstraint(v1,Equals,c), traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap,
          constMap)
      case LSConstraint(v1,Equals,v2) if negate =>
        mkNot(encodePred(LSConstraint(v1,Equals,v2), traceFn, len, messageTranslator, modelVarMap,
          typeToSolverConst, typeMap, constMap))
      case LSConstraint(v1,NotEquals,v2) if negate =>
        encodePred(LSConstraint(v1,Equals,v2), traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap,
          constMap)
      case LSConstraint(v1, NotEquals, v2) if !negate =>
        encodePred(LSConstraint(v1,Equals,v2), traceFn, len, messageTranslator, modelVarMap, typeToSolverConst,
          typeMap,constMap, true)
      case And(l1, l2) if !negate => mkAnd(encodePred(l1, traceFn, len, messageTranslator,
        modelVarMap, typeToSolverConst, typeMap, constMap),
        encodePred(l2, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap))
      case And(l1, l2) if negate => mkOr(
        encodePred(l1, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst,
          typeMap,constMap, negate = true),
        encodePred(l2, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap,
          negate = true)
      )
      case Or(l1, l2) if !negate => mkOr(encodePred(l1, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst,
        typeMap, constMap),
        encodePred(l2, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap))
      case Or(l1, l2) if negate => mkAnd(encodePred(l1, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst,
        typeMap, constMap, negate = true),
        encodePred(l2, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap,constMap,
          negate = true))
      case Not(l) =>
        encodePred(l, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap, !negate)
      case m: I if !negate =>
        mkExistsIndex(mkZeroIndex, len,
          i => assertIAt(i, m, messageTranslator, traceFn, negated = false, typeMap, typeToSolverConst, modelVarMap))
      //case NotI(m) if negate =>
      //  encodePred(m, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, !negate)
      //case NotI(m) =>
      //  mkForallInt(mkIntVal(-1), len,
      //    i => assertIAt(i,m,messageTranslator, traceFn, negated = true, typeMap, typeToSolverConst, modelVarMap))
      case m: I if negate =>
        mkForallIndex(mkZeroIndex(), len, i => assertIAt(i, m, messageTranslator, traceFn, negated = true, typeMap,
          typeToSolverConst, modelVarMap))
      case NI(m1, m2) if !negate =>
        // exists i such that omega[i] = m1 and forall j > i omega[j] != m2
        mkExistsIndex(mkZeroIndex, len, i => {
          mkAnd(List(
            assertIAt(i, m1, messageTranslator, traceFn, negated = false, typeMap, typeToSolverConst, modelVarMap),
            mkForallIndex(j => mkImplies(mkAnd(mkLTIndex(i, j), mkLTIndex(j, len)),
              assertIAt(j, m2, messageTranslator, traceFn, negated = true, typeMap,
                typeToSolverConst, modelVarMap)))
          ))
        })
      case NI(m1, m2) if negate =>
        // not NI(m1,m2) def= (not I(m1)) or NI(m2,m1)
        // encode with no negation
        encodePred(Or(Not(m1), NI(m2, m1)), traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap,
          constMap)
      case FreshRef(v) if !negate =>
        val msgAt: T => T = index => mkTraceConstraint(traceFn, index)
        mkExistsIndex(mkZeroIndex, len, ind => mkValContainedInMsg(msgAt(ind), modelVarMap(v), negated = false))
      case FreshRef(v) if negate =>
        val msgAt: T => T = index => mkTraceConstraint(traceFn, index)
        mkForallIndex(mkZeroIndex, len, ind => mkValContainedInMsg(msgAt(ind), modelVarMap(v), negated = true))
      case LSFalse =>
        mkBoolVal(negate)
      case LSTrue =>
        mkBoolVal(!negate)
    }
    res
  }


  private def allITraceAbs(traceAbstractionSet: Set[AbstractTrace]): Set[I] =
    traceAbstractionSet.flatMap(a => allI(a, includeArrow = true))


  private def allI(abs: AbstractTrace, includeArrow: Boolean): Set[I] = {
    val pred = abs.a.getOrElse(LSTrue)
    if (includeArrow)
      (SpecSpace.allI(pred) ++ abs.rightOfArrow).flatMap {
        case i: I => Some(i)
        case _ => None
      }
    else {
      SpecSpace.allI(pred)
    }
  }

  //TODO: remove "suffix" part of this class
  private case class TraceAndSuffixEnc(len: T,
                                       definedPvMap: Map[PureVar, T],
                                       noQuantifyPv: Set[PureVar] = Set(),
                                       quantifiedPv: Set[T] = Set(),
                                       suffix: Option[T] = None, trace: Option[T] = None) {

    def getOrQuantifyPv(pv: PureVar)(implicit zCtx: C): (T, TraceAndSuffixEnc) = {
      if (definedPvMap.contains(pv)) {
        (definedPvMap(pv), this)
      } else {
        val pvVar: T = mkAddrVar(pv)
        (pvVar, this.copy(definedPvMap = definedPvMap + (pv -> pvVar), quantifiedPv = quantifiedPv + pvVar))
      }
    }

    /**
     *
     * @param traceConstraint list of constraints from applicable specs at trace point
     * @param negate Construct negation of formula
     * @param zctx solver context
     * @return trace and suffix encoding object
     */
    def mkTrace(traceConstraint:List[T], negate:Boolean)(implicit zctx: C):TraceAndSuffixEnc = {
      assert(!negate) //TODO: remove negate
      if(traceConstraint.isEmpty)
        return this
      // If we have two overlapping specs e.g.
      //  I(bar(x)) <= x = Foo() /\ x != null
      //  ¬I(bar(x)) <= x = Foo() /\ x == null
      // And a message x=Foo() then we have:
      // [x!=null => I(bar(x))] && [x=null => ¬I(bar(x))]

      val op:List[T]=>T = if(negate) mkOr else mkAnd
//      val combTraceConst:List[T]=>T = if(negate) mkAnd else mkOr

      if(trace.isDefined)
        this.copy(trace = Some(op(List(trace.get, op(traceConstraint) ))))
      else
        this.copy(trace = Some(op(traceConstraint)))
    }
  }

  private def instArrowPhi(target:LSSingle,specSpace: SpecSpace):LSPred= target match {
    case i:I =>
      val applicableSpecs = specSpace.specsByI(i)
      val swappedPreds = applicableSpecs.map{s =>
        s.instantiate(i, specSpace)
      }
      if(swappedPreds.isEmpty) LSTrue
      else if(swappedPreds.size == 1) swappedPreds.head
      else swappedPreds.reduce(And)
    case FreshRef(_) => LSTrue
    case CLInit(_) => LSTrue
  }
  private def filterAny(s:Seq[(String,String)]):Seq[(String,String)] = s.filter{
    case (LSAnyVal(),_) => false
    case (_,LSAnyVal()) => false
    case _ => true
  }
  private def eq(i1:I,i2:I):LSPred =
    if(i1.signatures != i2.signatures || i1.mt != i2.mt)
      LSFalse
    else {
      val pairs = filterAny(i1.lsVars zip i2.lsVars)
      pairs.map(v => LSConstraint(v._1, Equals,v._2)).reduce(And)
    }

  private def neq(i1:I, i2:I):LSPred = {
    if(i1.signatures != i2.signatures || i1.mt != i2.mt)
      LSTrue
    else {
      val pairs = filterAny(i1.lsVars zip i2.lsVars)
      pairs.map(v => LSConstraint(v._1,NotEquals,v._2)).reduce(Or)
    }
  }
  private def updArrowPhi(i:I, lsPred:LSPred):LSPred = lsPred match {
    case Forall(v,p) => Forall(v,updArrowPhi(i:I, p:LSPred))
    case Exists(v,p) => Exists(v,updArrowPhi(i:I, p:LSPred))
    case l:LSConstraint => l
    case And(l1, l2) => And(updArrowPhi(i,l1), updArrowPhi(i,l2))
    case Or(l1, l2) => Or(updArrowPhi(i,l1), updArrowPhi(i,l2))
    case LifeState.LSTrue => LifeState.LSTrue
    case LifeState.LSFalse => LifeState.LSFalse
    case LSImplies(l1,l2) => LSImplies(updArrowPhi(i,l1), updArrowPhi(i,l2))
    case FreshRef(v) =>
      throw new IllegalStateException("RefV cannot be updated (encoding handled elsewhere)")
    case Not(i1:I) =>
      if(i1.mt == i.mt && i1.signatures == i.signatures)
        And(neq(i1,i), lsPred)
      else lsPred
    case ni@NI(i1,i2) =>
      And(Or(eq(i1,i), And(ni, neq(i1,i))), neq(i,i2))
    case i1:I =>
      if(i1.mt == i.mt && i1.signatures == i.signatures)
        Or(eq(i1,i), lsPred)
      else lsPred
    case Not(_) =>
      throw new IllegalArgumentException("Negation only supported on I")
  }
  private def updArrowPhi(rhs:LSSingle, lSPred: LSPred):LSPred = rhs match {
    case FreshRef(_) =>
      // Creation of reference (occurs earlier than instantiation)
      lSPred
    case i:I => updArrowPhi(i,lSPred)
    case CLInit(sig) => lSPred
  }

  private def encodeSpec(spec:LSSpec, traceFn:T, traceLen:T,
                         messageTranslator: MessageTranslator)(implicit zCtx: C):T = {
    //TODO:====
    mkForallIndex{i =>
      val modelVarMap:Map[String,T] = ???
      val lsTypeMap:Map[String,TypeSet] = ???
      val typeToSolverConst:Map[Int,T] = ???

      val indexMatches = assertIAt(i, spec.target, messageTranslator, traceFn, false, lsTypeMap,
        typeToSolverConst, modelVarMap)
      ???
    }
  }
  private def encodeSpec(specSpace:SpecSpace, traceFn:T, traceLen:T,
                         messageTranslator: MessageTranslator)(implicit zCtx:C):T = {

    ???
  }

  protected def encodeRef(v:T, traceFn:T, traceLen:T)(implicit zCtx:C):T
  /**
   * Encode .|>m1|>m2...
   *
   * @return
   */
  private def encodeTraceAbs(abs: AbstractTrace,
                                 messageTranslator: MessageTranslator,
                                 traceFn: T,
                                 traceLen: T,
                                 typeMap: Map[PureVar, TypeSet],
                                 typeToSolverConst: Map[Int, T],
                                 constMap: Map[PureVal, T],
                                 specSpace: SpecSpace,
                                 negate: Boolean = false, debug: Boolean = false)(implicit zCtx: C): TraceAndSuffixEnc = {
    assert(!negate) //TODO: remove negate or make this function handle it
    val rhs: Seq[LSSingle] = abs.rightOfArrow
    val rulePreds: Set[LSPred] = rhs.foldRight(Set[LSPred]()){ (v, acc) =>
      val updated = acc.map(lsPred => updArrowPhi(v,lsPred))
      val instantiated = instArrowPhi(v, specSpace)
      updated + instantiated
    }.filter(p => p != LSTrue)

    val op = if(negate) Or else And

    //Encode that each preceeding |> constraint cannot be equal to an allocation
    def encodeRefV(rhs: Seq[LSSingle], previous:Set[String] = Set()):Option[(LSPred, Set[FreshRef])] = rhs match {
      case (ref@FreshRef(v))::t =>
        val currentConstr: Set[LSConstraint] = previous.map{ other =>
          if(negate)
            LSConstraint(other, Equals, v)
          else
            LSConstraint(other, NotEquals, v)
        }
        // TODO: constrain all args prior to not be equal to ref ======

        val c = currentConstr.reduceOption(op)
        val n = encodeRefV(t,previous)
        n.getOrElse((LSTrue, Set[FreshRef]())) match {
          case (lsPred, refs) =>
            Some((And(c.getOrElse(LSTrue),lsPred), refs + ref))
        }
      case Nil => None
      case h::t => encodeRefV(t, previous ++ h.lsVar )
    }
    val refVPred: Option[(LSPred, Set[FreshRef])] = encodeRefV(rhs)
    val preds = refVPred.map(_._1) ++ rulePreds

    val lsVars = preds.flatMap(p => p.lsVar) ++ abs.rightOfArrow.flatMap(_.lsVar)
    val (modelVarMap:Map[String,T], traceAndSuffixEnc:TraceAndSuffixEnc) =
      lsVars.foldLeft(Map[String,T](),TraceAndSuffixEnc(traceLen,Map())){
        case ((accM, accTS),fv) =>
          if(abs.modelVars.contains(fv)) {
            val (newTS, v) = accTS.getOrQuantifyPv(abs.modelVars(fv).asInstanceOf[PureVar])
            (accM + (fv -> newTS), v)
          }else {
            //TODO: find some other well formed check, variables quantified in the spec reach here as well as generated.
//            assert(fv.contains("LS_GENERATED__"), "All non-generated fv must be bound to pv")
            val v = mkModelVar(fv,"")
            (accM + (fv -> v), accTS.copy(quantifiedPv = accTS.quantifiedPv + v))
          }
      }
    //TODO: should this be factored out? I think the idea was to constraint the types in the trace.
//    val modelTypeMap = modelVarMap.keySet.map{
//      case k if abs.modelVars.contains(k) =>
//        val pv = abs.modelVars(k)
//        k->typeMap.getOrElse(pv.asInstanceOf[PureVar], TopTypeSet)
//      case k => k -> TopTypeSet
//    }.toMap
    val modelTypeMap = Map[String,TypeSet]()
    val encoded = preds.foldLeft(traceAndSuffixEnc){(acc,p) =>
      val encodedPred = encodePred(p, traceFn, traceLen, messageTranslator, modelVarMap, typeToSolverConst,
        modelTypeMap, constMap, negate)
      acc.mkTrace(List(encodedPred), negate)
    }
    val refs = refVPred.map(_._2).getOrElse(Set()).toList.map{
      case FreshRef(v) =>
        encodeRef(modelVarMap(v),traceFn, traceLen)
    }
    encoded.mkTrace(refs,false)
  }

  protected def mkDistinct(pvList: Iterable[PureVar],pvMap:Map[PureVar,T])(implicit zctx: C): T

  protected def mkDistinctT(tList: Iterable[T])(implicit zctx: C): T

  protected def encodeTypeConsteraints: StateTypeSolving

  protected def persist: ClassHierarchyConstraints

  private implicit val ch = persist

  def toAST(ll:Map[(String,Int), PureVar],pvMap:Map[PureVar,T],stateUID:String,
            messageTranslator: MessageTranslator,
            negate:Boolean)(implicit zctx:C):T = {
    val localConstraints: List[T] = ll.map { case (local, pureVar) =>
      mkLocalConstraint(messageTranslator.localDomain(local), toAST(pureVar,pvMap), stateUID)
    }.toList
    if(negate) {
      mkOr(localConstraints.map(mkNot))
    }else{
      mkAnd(localConstraints)
    }
  }
  def toAST(heap: Map[HeapPtEdge, PureExpr],stateUID:String, pvMap:Map[PureVar,T],
            negate:Boolean)(implicit zctx: C): T = {
    // In addition to heap function, we assert that heap domain elements are distinct.
    // e.g. a^.f -> b^ * c^.f->d^ means a^ != c^
    // alternatively a^.f ->b^ * c^.g->d^ does not mean a^!=c^
    val fields = heap.groupBy {
      case (FieldPtEdge(_, fieldName), _) => fieldName
      case (StaticPtEdge(_, _), _) => "@static"
      case (ArrayPtEdge(_, _), _) => "@array"
    }
    val heapAst = fields.foldLeft(mkBoolVal(true)) { (acc, v) =>
      val pvList = v._2.flatMap {
        case (FieldPtEdge(pv, _), _) => Some(pv)
        case (StaticPtEdge(_, _), _) => None
        case (ArrayPtEdge(pv, _), _) => None //TODO: array encoding
      }
      mkAnd(acc, mkDistinct(pvList,pvMap))
    }

    //represent heap function
    val heapFunConst = heap.flatMap{
      case (FieldPtEdge(base,name),tgt:PureVar) =>
        val out = Some(mkDynFieldConstraint(pvMap(base), name, pvMap(tgt), stateUID))
        out
      case (StaticPtEdge(clazz,name),tgt:PureVar)  =>
        Some(mkStaticFieldConstraint(clazz,name, pvMap(tgt),stateUID))
      case (ArrayPtEdge(_,_),_) => None
    }.toList

    if(negate){
      mkOr(mkNot(heapAst), mkOr(heapFunConst.map(mkNot)))
    }else {
      mkAnd(heapAst, mkAnd(heapFunConst))
    }
  }

  def getPureValSet(pf:Set[PureConstraint]):Set[PureVal] = {
    pf.flatMap{
      case PureConstraint(lhs:PureVal, _, rhs:PureVal) => Set(lhs,rhs)
      case PureConstraint(_, _, rhs:PureVal) => Set(rhs)
      case PureConstraint(lhs:PureVal, _, _) => Set(lhs)
      case _ => Set()
    }
  }

  def mkPvName(pv:PureVar): String = s"pv-${pv.id}"

  /**
   * "[[_R_]]" from semantics
   *
   * @param state R ::= <O,M,P> where O is suffix of trace that may reach assertion
   *                M is separation logic memory
   *                P is pure vars
   *                call stack explicitly represented too (but may be elided from paper?)
   * @param messageTranslator mapping from I name to solver uninterpreted sort
   * @param maxWitness optional maximum trace length, if defined, debugging info is printed
   * @param negate trace, heap etc match or don't match state (used for subsumption)
   * @param zctx solver context
   * @return encoded formula for solver
   */
  def toASTState(state: State,
                       messageTranslator: MessageTranslator,
                       maxWitness: Option[Int] = None,
                       specSpace: SpecSpace,
                       negate:Boolean, debug:Boolean = false)(implicit zctx: C): T =
    toASTStateWithPv(state,messageTranslator, maxWitness, specSpace, negate, debug, false)._1

  def toASTStateWithPv(state: State,
                      messageTranslator: MessageTranslator,
                      maxWitness: Option[Int] = None,
                      specSpace: SpecSpace,
                      negate:Boolean,
                      debug:Boolean = false,
                      skolemizedPV:Boolean)(implicit zctx: C): (T, Map[PureVar,Option[T]]) = {

    if(debug){
      println(s"encoding state: ${state}")
    }

    // pure formula are for asserting that two abstract addresses alias each other or not
    //  as well as asserting upper and lower bounds on concrete types associated with addresses
    state.pureFormula.foreach {
      case PureConstraint(_, Subtype, _) => throw new IllegalArgumentException()
      case _ => true
    }

    val stateUniqueID = "" //TODO: should remove?
    val len = mkLenVar(s"len_$stateUniqueID") // there exists a finite size of the trace for this state
    val traceFun = mkTraceFn(stateUniqueID)
    val traceAbs = state.traceAbstraction
    val traceEnc: TraceAndSuffixEnc = encodeTraceAbs(traceAbs, messageTranslator, traceFn = traceFun, traceLen = len,
      negate = negate, typeMap = state.typeConstraints, typeToSolverConst = messageTranslator.getTypeToSolverConst,
      specSpace = specSpace, constMap = messageTranslator.getConstMap(), debug = debug)
//    val encodedSuffix = traceEnc.suffix.getOrElse(mkBoolVal(b = true))

    def withPVMap(pvMapIn:Map[PureVar, T]):T =  {

      val pvMap = pvMapIn ++ traceEnc.definedPvMap
      // typeFun is a function from addresses to concrete types in the program
      val typeFun = createTypeFun()

      // *** Pure constraints ***
      val pureAst = state.pureFormula.foldLeft(mkBoolVal(!negate))((acc, v) =>
        if(negate){
          mkOr(acc, mkNot(toAST(v,messageTranslator.getConstMap(),pvMap)))
        }else {
          mkAnd(acc, toAST(v, messageTranslator.getConstMap(),pvMap))
        }
      )

      val op:List[T]=>T = if(negate) mkOr else mkAnd

      // *** Type constraints
      val encodedTypeConstraints = {
        val typeConstraints = state.typeConstraints.map { case (k, v) => k -> v.getValues }
        op(typeConstraints.flatMap {
          case (pv, Some(ts)) =>
            val tc = mkTypeConstraintForAddrExpr(typeFun, messageTranslator.getTypeToSolverConst, toAST(pv,pvMap), ts)
            if(negate){
              Some(mkNot(tc))
            }else {
              Some(tc)
            }
          case _ => None
        }.toList)
      }

      // Encode locals
      val ll: Map[(String, Int), PureVar] = levelLocalPv(state)
      val localAST = toAST(ll, pvMap, stateUniqueID,messageTranslator, negate)

      // Encode heap
      val heapAst = toAST(state.heapConstraints,stateUniqueID, pvMap, negate)

      //TODO:Unclear if this adds any precision

      // Encode Ref (pv in heap or memory can't equal value created in the future)
      // pure values created in the future
      val refs = state.sf.traceAbstraction.rightOfArrow.flatMap{
        case FreshRef(v) => Some(state.sf.traceAbstraction.modelVars(v))
        case _ => None
      }
      // pure values referenced by separation logic
      val memPV: Set[PureVar] = ll.values.toSet ++ state.sf.heapConstraints.flatMap{
        case (StaticPtEdge(_,_),pv:PureVar) => Set(pv)
        case (FieldPtEdge(pv1,_),pv2:PureVar) => Set(pv1,pv2)
        case (ArrayPtEdge(_,_),_) =>
          ???
      }
      val refNeq = mkAnd(refs.flatMap{
        case r:PureVar =>
          Some(mkAnd(memPV.toList.map(l => mkNe(pvMap(r),pvMap(l)))))
        case _ => None
      })
      // val refNeq = mkBoolVal(true)

      assert(state.traceAbstraction.a.isEmpty, "TODO: remove a from trace abs")
      val out = op(List(refNeq, pureAst, localAST, heapAst, encodedTypeConstraints) ++ traceEnc.trace)
      maxWitness.foldLeft(out) { (acc, v) =>
        val (iv, isInc) = mkIndex(v)
        mkAnd(List(isInc, mkLTIndex(len, iv), acc))
      }
    }


    val statePV = state.pureVars() -- traceEnc.noQuantifyPv
    val statePVWithExtra = statePV
    val pureVarsBack: Map[String,PureVar] = statePVWithExtra.map(pv => (mkPvName(pv) -> pv)).toMap
    val pureVars: Map[String,Option[T]] = statePVWithExtra.map{pv =>
      mkPvName(pv) -> traceEnc.definedPvMap.get(pv)}.toMap

    val back = (v:Map[String,T]) => withPVMap(v.map{ case (k,v) => (pureVarsBack(k) -> v) })
    val res = if(skolemizedPV){
      back(pureVars.map{
        case (k,Some(v)) => (k,v)
        case _ => throw new IllegalArgumentException()
      })
    }else if(negate) {
      mkForallAddr(pureVars, back,traceEnc.quantifiedPv)
    }else{
      mkExistsAddr(pureVars, back,traceEnc.quantifiedPv)
    }
    (res,pureVars.map{
      case (k,v) => (pureVarsBack(k),v)
    })
  }

  case class MessageTranslator(states: List[State], specSpace: SpecSpace)(implicit zCtx: C) {
    // Trace messages
    private val alli = allITraceAbs(states.map(_.traceAbstraction).toSet) ++ specSpace.allI
    private val inameToI: Map[String, Set[I]] = alli.groupBy(_.identitySignature)
    private val inamelist = "OTHEROTHEROTHER" :: inameToI.keySet.toList
    private val identitySignaturesToSolver = mkUT("inames", inamelist)
    val solverToIdentitySignature:List[(T,String)] = identitySignaturesToSolver.map{
      case (k,v) => (v,k)
    }.toList

    // Constants
    private val pureValSet = states.foldLeft(Set[PureVal]()){
      case (acc,v) => acc.union(getPureValSet(v.pureFormula))
    }
    private val (uniqueConst, constMap) = mkConstConstraintsMap(pureValSet)
    def getConstMap():Map[PureVal,T] = constMap
    zCtx.mkAssert(uniqueConst)

    // Types
    private val allTypeValues = states.foldLeft(Set[Int]()){
      case (acc,s) => acc.union(allTypes(s))
    }

    private val (typesUnique, typeToSolverConst: Map[Int, T]) = mkTypeConstraints(allTypeValues)
    zCtx.mkAssert(typesUnique)
    def getTypeToSolverConst:Map[Int,T] = typeToSolverConst


    // Locals
    private val allLocal: Set[(String, Int)] = states.flatMap{ state =>
      val localAtStackDepth: Map[(String, Int), PureVar] = levelLocalPv(state)
      val out = localAtStackDepth.keySet
      out
    }.toSet
    val (localDistinct, localDomain) = mkLocalDomain(allLocal)
    zCtx.mkAssert(localDistinct)

    def enumFromI(m: I): T = {
      try {
        identitySignaturesToSolver(m.identitySignature)
      }catch {
        case k:NoSuchElementException =>
          throw k
      }
    } //mkIName(enum, iNameIntMap(m.identitySignature))

    def nameFun: T = mkINameFn()

    def iForMsg(m: TMessage): Option[I] = {
      val possibleI = alli.filter(ci => ci.contains(ci.mt,m.fwkSig.get))
      assert(possibleI.size < 2)
      possibleI.headOption
    }

    def iForZ3Name(z3Name: String): Set[I] = {
      inameToI.getOrElse(z3Name, Set())
    }
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
    val tracePVs = state.traceAbstraction.modelVars.collect{case (_, pv: PureVar) => pv}
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
          case (Some(acc), pc@PureConstraint(v1@PureVar(id1), Equals, v2@PureVar(id2))) if id1 < id2 =>
            if (existsNegation(pc, acc)) {
              None
            } else {
//              val res = mergePV(acc.copy(pureFormula = acc.pureFormula - pc), v2, v1)
              val res = mergePV(acc.removePureConstraint(pc),v2,v1)
              res
            }
          case (Some(acc), pc@PureConstraint(v1@PureVar(id1), Equals, v2@PureVar(id2))) if id1 > id2 =>
            if (existsNegation(pc, acc)) {
              None
            } else {
//              val res = mergePV(acc.copy(pureFormula = acc.pureFormula - pc), v1, v2)
              val res = mergePV(acc.removePureConstraint(pc), v1,v2)
              res
            }
          case (Some(acc), pc@PureConstraint(PureVar(id1), Equals, PureVar(id2))) if id1 == id2 =>
//            Some(acc.copy(pureFormula = acc.pureFormula - pc))
            Some(acc.removePureConstraint(pc))
          case (acc, _) =>
            acc
        }
      }
    }

    if(swappedForSmallerPvOpt.isEmpty)
      return None
    val swappedForSmallerPv = swappedForSmallerPvOpt.get
    val allPv = swappedForSmallerPv.pureVars()
    val out = if (allPv.nonEmpty) {
      val maxPvValue = allPv.map { case PureVar(id) => id }.max
      swappedForSmallerPv.copy(nextAddr = maxPvValue + 1)
    } else
      swappedForSmallerPv
    Some(out)
  }

  def simplify(state: State,specSpace: SpecSpace, maxWitness: Option[Int] = None): Option[State] = {
    implicit val zCtx = getSolverCtx
    if (state.isSimplified) Some(state) else {
      // Drop useless constraints
      val state2 = state.copy(sf = state.sf.copy(pureFormula = state.pureFormula.filter {
        case PureConstraint(v1, Equals, v2) if v1 == v2 => false
        case _ => true
      }))

      // note: I think the following is wrong, empty points to set occurs when value must be null
      //      // If no type possible for a pure var, state is not feasible
      //      val pvMap2: Map[PureVar, TypeSet] = state.typeConstraints
      //      if (pvMap2.exists{ a => a._2.isEmpty }) {
      //        return None
      //      }

      val nullsFromPt = state2.typeConstraints.filter(a => a._2.isEmpty)
      val stateWithNulls = nullsFromPt.foldLeft(state2){
        case (state,(v,_)) => state.addPureConstraint(PureConstraint(v, Equals, NullVal))
      }
      val messageTranslator = MessageTranslator(List(stateWithNulls),specSpace)

      // Only encode types in Z3 for subsumption check due to slow-ness

      val ast =
          toASTState(stateWithNulls, messageTranslator, maxWitness,
            negate = false, specSpace = specSpace, debug = maxWitness.isDefined)

      if (maxWitness.isDefined) {
        println(s"State ${System.identityHashCode(state2)} encoding: ")
        println(ast.toString)
      }
      val simpleAst = solverSimplify(ast, stateWithNulls, messageTranslator, maxWitness.isDefined)

      reset()
      if(simpleAst.isEmpty)
        None
      else {
        val reducedState = reduceStatePureVars(stateWithNulls.setSimplified()).map(gcPureVars)
        reducedState.map(_.setSimplified())
      }
    }
  }

  // TODO: call stack is currently just a list of stack frames, this needs to be updated when top is added
  def stackCanSubsume(cs1: List[CallStackFrame], cs2: List[CallStackFrame]): Boolean = (cs1, cs2) match {
    case (CallStackFrame(ml1, _, locals1) :: t1, CallStackFrame(ml2, _, locals2) :: t2) if ml1 == ml2 =>
      locals1.forall { case (k, v) => locals2.get(k).contains(v) } &&
        stackCanSubsume(t1, t2)
    case (Nil, Nil) => true
    case _ => false
  }

  /**
   *
   *
   * @param s1 subsuming state
   * @param s2 contained state
   * @return
   */
  def canSubsume(s1: State, s2: State, specSpace: SpecSpace, maxLen: Option[Int] = None): Boolean ={
    // Check if stack sizes or locations are different
    if (s1.callStack.size != s2.callStack.size)
      return false

    val stackLocsMatch = (s1.callStack zip s2.callStack).forall {
      case (fr1, fr2) => fr1.exitLoc == fr2.exitLoc
    }
    if (!stackLocsMatch)
      return false

    // s2 must have equal or more CLInit invocations as s1
    def clInitSet(s:State):Set[CLInit] = {
      s.traceAbstraction.rightOfArrow.flatMap{
        case v:CLInit => Some(v)
        case _ => None
      }.toSet
    }
    val s1CLinit = clInitSet(s1)
    val s2CLinit = clInitSet(s2)
    if(s1CLinit.exists(s1i => !s2CLinit.contains(s1i)))
      return false

    // s2 must contain all locals that s1 contains
    val s2locals: Set[(String, Int)] = levelLocalPv(s2).map{case (local,_) => local}.toSet
    val s1locals: Set[(String, Int)] = levelLocalPv(s1).map{case (local,_) => local}.toSet
    if(!s1locals.forall(l => s2locals.contains(l))){
      return false
    }

    // s2 must contian all heap cells that s2 contains
    val dummyPv = PureVar(-10)
    def repHeapCells(cell: (HeapPtEdge, PureExpr)):HeapPtEdge = cell match{
        case (FieldPtEdge(pv,fn),_) => FieldPtEdge(dummyPv, fn)
        case (StaticPtEdge(clazz,fn), _) => StaticPtEdge(clazz,fn)
    }
    val s2heapCells: Map[HeapPtEdge, Map[HeapPtEdge, PureExpr]] = s2.heapConstraints.groupBy(repHeapCells)
    val s1heapCells = s1.heapConstraints.groupBy(repHeapCells)

    // For each materialized heap cell in s1, s2 must have a matching heap cell or subsumption not possible
    val s2HasMoreOfEach = s1heapCells.forall{s1Cell =>
      s2heapCells.get(s1Cell._1) match {
        case Some(s2Cells) =>
          s1Cell._2.size <= s2Cells.size
        case None => true
      }
    }
    if(!s2HasMoreOfEach){
      return false
    }

    canSubsumeZ3(s1,s2,specSpace, maxLen)
  }

  def allTypes(state:State)(implicit zctx:C):Set[Int] = {
    val pvMap = state.typeConstraints
    val usedTypes = pvMap.flatMap { case (_, tc) => tc.getValues.getOrElse(Set()) }.toSet
    mkTypeConstraints(usedTypes)
    usedTypes
  }

  def canSubsumeZ3(s1:State, s2:State,specSpace:SpecSpace, maxLen:Option[Int]):Boolean = {
    try {
      implicit val zCtx: C = getSolverCtx
      val allTypesS1S2 = allTypes(s1).union(allTypes(s2))

//      val (typesUnique, typeToSolverConst: Map[Int, T]) = mkTypeConstraints(allTypesS1S2)
//      zCtx.mkAssert(typesUnique)
      val messageTranslator: MessageTranslator = MessageTranslator(List(s1, s2), specSpace)

//      val pureValSet = getPureValSet(s1.pureFormula).union(getPureValSet(s2.pureFormula))
//      val (uniqueConst, constMap) = mkConstConstraintsMap(pureValSet)
//      zCtx.mkAssert(uniqueConst)

      //TODO: does this work instead of complicated negate thing?
      val s1Enc = mkNot(toASTState(s1, messageTranslator, maxLen,
        negate = false,
        specSpace = specSpace, debug = maxLen.isDefined))
      zCtx.mkAssert(s1Enc)
      val s2Enc = toASTState(s2, messageTranslator, maxLen,
        negate = false,
        specSpace = specSpace, debug = maxLen.isDefined)
      zCtx.mkAssert(s2Enc)
      val foundCounter = try {
        checkSAT()
      }catch {
        case e:IllegalStateException =>
          println("subsumption timeout:")
          println(s"  s1: ${s1}")
          println(s"  s2: ${s2}")
          throw e
      }
      if (foundCounter && maxLen.isDefined) {
        printDbgModel(messageTranslator, Set(s1.traceAbstraction,s2.traceAbstraction), "")
      }
      reset()
      !foundCounter
    }catch{
      case e:IllegalStateException if e.getLocalizedMessage.contains("timeout issue") =>
        // Note: this didn't seem to help things so currently disabled
        // sound to say state is not subsumed if we don't know
        // false
        e.printStackTrace()
        throw e
    }
  }

  /**
   * name locals relative to their stack position for encoding
   * @param s state
   * @return map from local and level to pointed to purevar
   */
  def levelLocalPv(s:State):Map[(String,Int), PureVar] = {
    s.callStack.zipWithIndex.flatMap{
      case (CallStackFrame(_,_,locals), level) =>
        locals.collect{case (StackVar(name),pValue:PureVar) => ((name,level),pValue)}
    }.toMap
  }
  /**
   * Consider rearrangments of pure vars that could result in subsumption
   *
   * @param s1 subsuming state
   * @param s2 contained state
   * @return
   */
  def canSubsumeSlow(s1: State, s2: State, maxLen: Option[Int] = None): Boolean = {

    // Check if more fields are defined in the subsuming state (more fields means can't possibly subsume)
    def fieldNameCount(s: State): Map[String, Int] = {
      val fieldSeq: immutable.Iterable[String] = s.heapConstraints.collect {
        case (FieldPtEdge(_, name), _) => name
      }
      fieldSeq.groupBy(l => l).map(t => (t._1, t._2.size))
    }

    val s1FieldCount: Map[String, Int] = fieldNameCount(s1)
    val s2FieldCount: Map[String, Int] = fieldNameCount(s2)
    val s1FieldSet = s1FieldCount.keySet
    val s2FieldSet = s2FieldCount.keySet
    if (s1FieldSet.size > s2FieldSet.size)
      return false

    if (s1FieldSet.exists(fld => s1FieldCount(fld) > s2FieldCount.getOrElse(fld, -1)))
      return false



    //TODO: below is brute force approach to see if considering pure var rearrangments fixes the issue
    val pv1: Set[PureVar] = s1.pureVars()
    val pv2: Set[PureVar] = s2.pureVars()
    val allPv = pv1.union(pv2).toList
    // map s2 to something where all pvs are strictly larger
    val maxID = if (allPv.nonEmpty) allPv.maxBy(_.id) else PureVar(5)


    // Swap all pureVars to pureVars above the max found in either state
    // This way swapping doesn't interfere with itself
    val (s2Above, pvToTemp) = pv2.foldLeft((s2.copy(nextAddr = maxID.id + 1), Set[PureVar]())) {
      case ((st, nl), pv) =>
        val (freshPv, st2) = st.nextPv()
        (st2.swapPv(pv, freshPv), nl + freshPv)
    }

    // swap shared locals

    val s1LocalMap = levelLocalPv(s1)
    val s2LocalMap = levelLocalPv(s2Above)
    val overlap = s1LocalMap.keySet.intersect(s2LocalMap.keySet)

    // Create mapping that must exist if subsumption is to occur, none if not feasible
    val s2LocalSwapMapOpt = overlap.foldLeft(Some(Map()):Option[Map[PureVar,PureVar]]){
      case (None,_) => None
      case (Some(acc),v) => {
        val s1Val = s1LocalMap(v)
        val s2Val = s2LocalMap(v)
        if(acc.contains(s1Val) && (acc(s1Val) != s2Val)){
          // Cannot subsume if two locals in subsuming state map to the same pure var and the subsumee maps to different
          // e.g.
          // s1: foo -> a * bar -> b * baz -> b
          // s2: foo -> c * bar -> b * baz -> a
          // s1 cannot subsume s2 since the heap `foo -> @1, bar -> @2, baz -> @3` is in s2 but not s1
          None
        }else{
          Some(acc + (s1Val -> s2Val))
        }
      }
    }

    if(s2LocalSwapMapOpt.isEmpty)
      return false

    val s2LocalSwapped = s2LocalSwapMapOpt.get.foldLeft(s2Above){
      case (acc,(newPv,oldPv)) => acc.swapPv(oldPv, newPv)
    }
    val removeFromPermS1 = overlap.map(k => s1LocalMap(k))
//    val allPvNoLocals = allPv.filter(v => !removeFromPerm.contains(v))
    val removeFromPermS2 = overlap.map(k => s2LocalMap(k))



    //TODO: extremely slow permutations there is probably a better way
    val startTime = System.currentTimeMillis()
    //filter out pure var pairings early if they can't be subsumed type wise
    def canMap(pv1:PureVar, pv2:PureVar):Boolean = {
      // Check if pv mapping is possible from types
      val tc1 = s1.typeConstraints.get(pv1)
      val tc2 = s2Above.typeConstraints.get(pv2)
      if(tc2.isEmpty)
        return true
      val typeCanSubs = tc1.forall(_.contains(tc2.get))

      def firstConstConstraint(pv : PureVar, s:State):Option[PureVal] = {
        s.pureFormula.collectFirst{
          case PureConstraint(lhs, Equals, pval:PureVal) if lhs == pv => pval
        }
      }
      val cc1 = firstConstConstraint(pv1, s1)
      val cc2 = firstConstConstraint(pv2, s2Above)
      val constCanSub = (cc1,cc2) match{
        case (None,None) => true
        case (None,Some(_)) => true
        case (Some(TopVal), _) => true
        case (Some(v1), Some(v2)) => v1 == v2
        case (Some(_), None) => false
      }

      typeCanSubs && constCanSub
    }

    //all possible renamings of variables
    val perm = BounderUtil.allMap(pv1 -- removeFromPermS1,pvToTemp -- removeFromPermS2,canMap)
    val noRenamingIfEmpty = if(perm.isEmpty) Map()::Nil else perm
//    val perm = allPvNoLocals.permutations.grouped(40)
    //TODO: add par back in?
    val out: Boolean = noRenamingIfEmpty.exists{perm =>
      val s2Swapped = perm.foldLeft(s2LocalSwapped) {
        case (s, (newPv, oldPv)) => s.swapPv(oldPv, newPv)
      }

//      val out1 = canSubsumeNoCombinations(s1, s2Swapped, maxLen)
      //TODO: probably should remove canSubsumeSlow method ===
      val out1 = ???
      out1
    }
    val elapsedTime = System.currentTimeMillis() - startTime
    if(elapsedTime > 1000) {
      println(s"Subsumption time: $elapsedTime pvCount: ${allPv.size} Subsumption result: $out")
      println(s"  state1: $s1")
      println(s"  state2: $s2")
    }

    out
  }


  def encodeTrace(traceFN: T, trace: List[TMessage],
                  messageTranslator: MessageTranslator, valToT: Map[Int, T])(implicit zCtx: C): T = {
    val assertEachMsg: List[T] = trace.zipWithIndex.flatMap {
      case (m, ind) =>
        val (iv, isInd) = mkIndex(ind)
        zCtx.mkAssert(isInd)
        val msgExpr = mkTraceConstraint(traceFN, iv)
        val i = messageTranslator.iForMsg(m)
        val argConstraints: List[T] = m.args.zipWithIndex.map {
          case (TAddr(addr), ind) =>
            val lhs = mkArgConstraint(mkArgFun(), ind, msgExpr)
            mkEq(lhs, valToT(addr))
          case (TNullVal, _) => ???
        }
        i.map(ii => {
          mkAnd(assertIAt(iv, ii, messageTranslator, traceFN, negated = false,
            lsTypeMap = Map(), typeToSolverConst = Map(), s => mkModelVar(s, "")),
            mkAnd(argConstraints)
          )
        })
    }
    assertEachMsg.foldLeft(mkBoolVal(b = true))((a, b) => mkAnd(a, b))
  }

  def witnessed(state: State, specSpace: SpecSpace, debug:Boolean = false): Option[WitnessExplanation] = {
    implicit val zCtx = getSolverCtx
    if (state.heapConstraints.nonEmpty)
      return None
    if (state.callStack.nonEmpty)
      return None
    traceInAbstraction(state,specSpace, Nil, debug)
  }

  def traceInAbstraction(state: State,specSpace: SpecSpace,
                         trace: List[TMessage],negate:Boolean = false,
                         debug: Boolean = false)(implicit zCtx: C): Option[WitnessExplanation] = {
    try {
      val messageTranslator = MessageTranslator(List(state), specSpace)
      val pvMap: Map[PureVar, Option[T]] = encodeTraceContained(state, trace, messageTranslator = messageTranslator, specSpace = specSpace,
        negate = negate)
      val sat = checkSAT()
      if (sat && debug) {
        println(s"model:\n ${zCtx.asInstanceOf[Z3SolverCtx].solver.toString}")
        printDbgModel(messageTranslator, Set(state.traceAbstraction), "")
      }
      if (sat) {
        Some(explainWitness(messageTranslator, pvMap))
      } else {
        None
      }
    }finally{
      reset()
    }
  }

  def mkIndex(num:Int)(implicit zctx: C):(T,T) = {
    (0 until num).foldLeft((mkZeroIndex, mkBoolVal(b = true))){case (acc,_) =>
      val (ivIsInc,iv) = mkAddOneIndex(acc._1)
      (iv,mkAnd(acc._2, ivIsInc))
    }
  }
  private def encodeTraceContained(state: State, trace: List[TMessage], specSpace: SpecSpace,
                                   messageTranslator: MessageTranslator,
                                   negate:Boolean = false)(implicit zCtx: C): Map[PureVar, Option[T]] = {
    val traceFn = mkTraceFn("")

    val usedTypes = allTypes(state)
    val (typesAreUnique, typeMap) = mkTypeConstraints(usedTypes)
    zCtx.mkAssert(typesAreUnique)

    val len = mkLenVar(s"len_")
//    val traceLimit = trace.indices.foldLeft(mkZeroIndex){case (acc,_) => mkAddOneIndex(acc)}
    val (traceLimit, isInc) = mkIndex(trace.size)
    zCtx.mkAssert(isInc)
    zCtx.mkAssert(mkEq(len, traceLimit))

    // Maximum of 10 addresses in trace contained.  This method is typically used for empty traces with no addresses.
    // Only testing has non empty traces passed to this method
    val distinctAddr: Map[Int, T] = (0 until 10).map(v => (v, mkAddrConst(v))).toMap
    val assertDistinct = mkDistinctT(distinctAddr.keySet.map(distinctAddr(_)))
    zCtx.mkAssert(assertDistinct)
    val (encodedState,pvMap) = toASTStateWithPv(state, messageTranslator, None,
      negate=false, specSpace = specSpace,skolemizedPV = true)
    val encodedTrace = encodeTrace(traceFn, trace, messageTranslator, distinctAddr)
    if(negate){
      zCtx.mkAssert(mkNot(encodedState))
      zCtx.mkAssert(mkNot(encodedTrace))
    }else {
      zCtx.mkAssert(encodedState)
      zCtx.mkAssert(encodedTrace)
    }

    pvMap
  }

}