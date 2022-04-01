package edu.colorado.plv.bounder.solver

import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{BitTypeSet, EmptyTypeSet, MessageType, PrimTypeSet, TAddr, TMessage, TNullVal, TopTypeSet, TypeSet, WitnessExplanation}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecSpace}
import edu.colorado.plv.bounder.lifestate.LifeState._
import edu.colorado.plv.bounder.solver.StateSolver.{rhsToPred, simplifyPred}
import edu.colorado.plv.bounder.symbolicexecutor.state.{HeapPtEdge, _}
import org.slf4j.{Logger, LoggerFactory}
import upickle.default.{read, write}

import scala.collection.{immutable, mutable}

trait Assumptions

class UnknownSMTResult(msg : String) extends Exception(msg)
trait SolverCtx[T]{
  def mkAssert(t:T):Unit
  def acquire(randomSeed:Option[Int] = None):Unit
  def release():Unit
}

object StateSolver{
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
    case I(_,mSig, _) if mSig.matchesClass(sig) => LSFalse
    case i:I => i
    case NI(I(_,mSig, _),_) if mSig.matchesClass(sig) => LSFalse
    case ni:NI => ni
    case CLInit(sig2) if sig == sig2 => LSFalse
    case f:FreshRef => f
  }
  private def instArrowPhi(target:LSSingle,specSpace: SpecSpace, includeDis:Boolean):LSPred= target match {
    case i:I =>
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
}
/** SMT solver parameterized by its AST or expression type */
trait StateSolver[T, C <: SolverCtx[T]] {

  def setSeed(v:Int)(implicit zCtx: C):Unit
  // checking
  def getSolverCtx: C
  def getLogger:Logger

  /**
   * Check satisfiability of fomrula in solver
   * @throws IllegalStateException if formula is undecidable or times out
   * @param useCmd if true, call z3 using bash
   * @param timeout if usecmd is true, set timeout
   * @param zCtx solver context
   * @return satisfiability of formula
   */
  def checkSAT(useCmd:Boolean, timeout:Option[Int] = None)(implicit zCtx: C): Boolean

  def push()(implicit zCtx: C): Unit

  def pop()(implicit zCtx: C): Unit

//  def reset()(implicit zCtx: C): Unit

  /**
   * Write debugging info, delete if cont finishes without failure
   * Used to debug native crashes in solver
   *
   * @param cont call solver code in continuation, return result
   */
  protected def dumpDbg[V](cont: () => V)(implicit zCtx: C): V


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

  protected def mkForallAddr(name: Map[String, Option[T]], cond: Map[String, T] => T,
                             solverNames: Set[T] = Set())(implicit zCtx: C): T

  protected def mkExistsT(t:List[T], cond:T)(implicit zCtx: C):T
  protected def mkExistsAddr(name: String, cond: T => T)(implicit zctx: C): T

  protected def mkExistsAddr(name: Map[String,Option[T]], cond: Map[String, T] => T,
                             solverNames: Set[T] = Set())(implicit zCtx: C): T
  protected def mkPv(pv:PureVar)(implicit zCtx:C):T

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

//  @deprecated
//  protected def mkAdd(lhs: T, rhs: T)(implicit zctx: C): T

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
   * @param n maximum number of uninterpreted integers
   * @param zCtx solver context
   * @return boolean asserting fixed Uint count
   */
  protected def mkMaxMsgUint(n: Int)(implicit zCtx: C): T

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
  def compareConstValueOf(rhs: T, op: CmpOp, pureVal: PureVal, constMap: Map[PureVal, T])(implicit zctx: C): T =
    (pureVal, op) match {
      case (TopVal, _) => mkBoolVal(b = true)
      case (ClassVal(_), _) => mkBoolVal(b = true) //TODO: add class vals if necessary for precision
      case (v: PureVal, Equals) =>
        if(!constMap.contains(v))
          throw new IllegalStateException(s"Missing constant $v")
        mkEq(constMap(v), mkConstValueConstraint(rhs))
      case (v: PureVal, NotEquals) =>
        mkNot(mkEq(constMap(v), mkConstValueConstraint(rhs)))
      case (_: PureVal, _) =>
        mkBoolVal(b = true)
      case v =>
        println(v)
        ???
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
      case (LifeState.LSVar(msgVar), ind) =>
        //        val modelVar = modelVarMap(msgVar)
        val modelExpr = modelVarMap(msgVar)
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
      case (LifeState.LSConst(const), ind) =>
        val argAt = mkArgConstraint(mkArgFun(), ind, msgExpr)
        Some(compareConstValueOf(argAt, Equals, const, messageTranslator.getConstMap()))
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
      ???
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
                         constMap:Map[PureVal, T])(implicit zctx: C): T = {
    val res = combinedPred match {
      case Forall(h::t, p) =>
        mkForallAddr(h, (v:T) => {
          val newModelVarMap:String => T = s => if(s == h) v else modelVarMap(s)
          encodePred(Forall(t, p), traceFn, len, messageTranslator, newModelVarMap, typeToSolverConst, typeMap,
            constMap)
        })
      case Exists(h::t, p) =>
        mkExistsAddr(h, (v:T) => {
          val newModelVarMap:String => T = s => if(s == h) v else modelVarMap(s)
          encodePred(Exists(t, p), traceFn, len, messageTranslator, newModelVarMap, typeToSolverConst, typeMap,
            constMap)
        })
      case Forall(Nil, p) =>
        encodePred(p, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap)
      case Exists(Nil, p) =>
        encodePred(p, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap)
      case LSImplies(l1,l2) => mkImplies(
        encodePred(l1, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap),
        encodePred(l2, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap)
      )
      case LSConstraint(LSVar(v1), Equals,LSVar(v2)) =>
        mkEq(modelVarMap(v1), modelVarMap(v2))
      case LSConstraint(LSVar(v1), NotEquals, LSVar(v2)) =>
        mkNot(mkEq(modelVarMap(v1), modelVarMap(v2)))
      case LSConstraint(LSVar(v1), op, LSConst(c)) =>
        compareConstValueOf(modelVarMap(v1), op, c, constMap)
      case LSConstraint(c@LSConst(_), Equals, LSVar(v1)) =>
        encodePred(LSConstraint(v1,Equals,c), traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap,
          constMap)
      case LSConstraint(c@LSConst(_), NotEquals, LSVar(v1)) =>
        encodePred(LSConstraint(v1,NotEquals,c), traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap,
          constMap)
      case And(l1, l2) => mkAnd(encodePred(l1, traceFn, len, messageTranslator,
        modelVarMap, typeToSolverConst, typeMap, constMap),
        encodePred(l2, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap))
      case Or(l1, l2) => mkOr(encodePred(l1, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst,
        typeMap, constMap),
        encodePred(l2, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap))
      case Not(l) =>
        mkNot(encodePred(l, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap))
      case m: I =>
        mkExistsIndex(mkZeroIndex, len,
          i => assertIAt(i, m, messageTranslator, traceFn, negated = false, typeMap, typeToSolverConst, modelVarMap))
      //case NotI(m) if negate =>
      //  encodePred(m, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, !negate)
      //case NotI(m) =>
      //  mkForallInt(mkIntVal(-1), len,
      //    i => assertIAt(i,m,messageTranslator, traceFn, negated = true, typeMap, typeToSolverConst, modelVarMap))
      case NI(m1, m2) =>
        // exists i such that omega[i] = m1 and forall j > i omega[j] != m2
        mkExistsIndex(mkZeroIndex, len, i => {
          mkAnd(List(
            assertIAt(i, m1, messageTranslator, traceFn, negated = false, typeMap, typeToSolverConst, modelVarMap),
            mkForallIndex(j => mkImplies(mkAnd(mkLTIndex(i, j), mkLTIndex(j, len)),
              assertIAt(j, m2, messageTranslator, traceFn, negated = true, typeMap,
                typeToSolverConst, modelVarMap)))
          ))
        })
      case FreshRef(v) =>
        val msgAt: T => T = index => mkTraceConstraint(traceFn, index)
        mkExistsIndex(mkZeroIndex, len, ind => mkValContainedInMsg(msgAt(ind), modelVarMap(v), negated = false))
//      case FreshRef(v) if negate =>
//        val msgAt: T => T = index => mkTraceConstraint(traceFn, index)
//        mkForallIndex(mkZeroIndex, len, ind => mkValContainedInMsg(msgAt(ind), modelVarMap(v), negated = true))
      case LSFalse =>
        mkBoolVal(false)
      case LSTrue =>
        mkBoolVal(true)
    }
    res
  }


  private def allITraceAbs(traceAbstractionSet: Set[AbstractTrace]): Set[I] =
    traceAbstractionSet.flatMap(a => allI(a))


  private def allI(abs: AbstractTrace): Set[I] = {
    abs.rightOfArrow.flatMap {
      case i: I => Some(i)
      case _ => None
    }.toSet
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
     * @param zctx solver context
     * @return trace and suffix encoding object
     */
    def mkTrace(traceConstraint:List[T])(implicit zctx: C):TraceAndSuffixEnc = {
      if(traceConstraint.isEmpty)
        return this
      // If we have two overlapping specs e.g.
      //  I(bar(x)) <= x = Foo() /\ x != null
      //  ¬I(bar(x)) <= x = Foo() /\ x == null
      // And a message x=Foo() then we have:
      // [x!=null => I(bar(x))] && [x=null => ¬I(bar(x))]

      if(trace.isDefined)
        this.copy(trace = Some(mkAnd(List(trace.get, mkAnd(traceConstraint) ))))
      else
        this.copy(trace = Some(mkAnd(traceConstraint)))
    }
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
                             specSpace: SpecSpace,
                             shouldEncodeRef:Boolean = true,
                             definedPvMap:Map[PureVar, T] = Map(),
                             debug: Boolean = false)(implicit zCtx: C): TraceAndSuffixEnc = {
    val typeToSolverConst = messageTranslator.getTypeToSolverConst
    val constMap = messageTranslator.getConstMap()
    val rhs: Seq[LSSingle] = abs.rightOfArrow

    // Instantiate and update specifications for each ▷m̂
    // only include the disallow if it is the last one in the chain
    val rulePreds: Set[LSPred] = rhsToPred(rhs, specSpace).map(simplifyPred)

    //Encode that each preceeding |> constraint cannot be equal to an allocation
    def encodeRefV(rhs: Seq[LSSingle], previous:Set[String] = Set()):Option[(LSPred, Set[FreshRef])] = rhs match {
      case (ref@FreshRef(v))::t =>
        val currentConstr: Set[LSConstraint] = previous.map{ other =>
            LSConstraint(other, NotEquals, v)
        }
        // TODO: constrain all args prior to not be equal to ref ======

        val c = currentConstr.reduceOption(And)
        val n = encodeRefV(t,previous)
        n.getOrElse((LSTrue, Set[FreshRef]())) match {
          case (lsPred, refs) =>
            Some((And(c.getOrElse(LSTrue),lsPred), refs + ref))
        }
      case Nil => None
      case h::t => encodeRefV(t, previous ++ h.lsVar )
    }
    val refVPred: Option[(LSPred, Set[FreshRef])] = if(shouldEncodeRef) encodeRefV(rhs) else None
    val preds = refVPred.map(_._1) ++ rulePreds

    val lsVars = preds.flatMap(p => p.lsVar) ++ abs.rightOfArrow.flatMap(_.lsVar)
    val (modelVarMap:Map[String,T], traceAndSuffixEnc:TraceAndSuffixEnc) =
      lsVars.foldLeft(Map[String,T](),TraceAndSuffixEnc(traceLen,definedPvMap)){
        case ((accM, accTS),fv) =>
          if(abs.modelVars.contains(fv)) {
            val (newTS, v) = accTS.getOrQuantifyPv(abs.modelVars(fv).asInstanceOf[PureVar])
            (accM + (fv -> newTS), v)
          }else {
            val v = mkModelVar(fv,"")
            (accM + (fv -> v), accTS.copy(quantifiedPv = accTS.quantifiedPv + v))
          }
      }
    val modelTypeMap = Map[String,TypeSet]()
    val encoded = preds.foldLeft(traceAndSuffixEnc){(acc,p) =>
      val encodedPred = encodePred(p, traceFn, traceLen, messageTranslator, modelVarMap, typeToSolverConst,
        modelTypeMap, constMap)
      acc.mkTrace(List(encodedPred))
    }
    val refs = refVPred.map(_._2).getOrElse(Set()).toList.map{
      case FreshRef(v) =>
        encodeRef(modelVarMap(v),traceFn, traceLen)
    }
    encoded.mkTrace(refs)
  }

  protected def mkDistinct(pvList: Iterable[PureVar], pvMap:Map[PureVar,T])(implicit zctx: C): T

  protected def mkDistinctT(tList: Iterable[T])(implicit zctx: C): T

//  protected def encodeTypeConsteraints: StateTypeSolving

  protected def persist: ClassHierarchyConstraints

  private implicit val ch = persist

  def toAST(ll:Map[(String,Int), PureVar],pvMap:Map[PureVar,T],stateUID:String,
            messageTranslator: MessageTranslator)(implicit zctx:C):T = {
    val negate = false
    val localConstraints: List[T] = ll.map { case (local, pureVar) =>
      mkLocalConstraint(messageTranslator.localDomain(local), toAST(pureVar,pvMap), stateUID)
    }.toList
    if(negate) {
      mkOr(localConstraints.map(mkNot))
    }else{
      mkAnd(localConstraints)
    }
  }
  def toAST(heap: Map[HeapPtEdge, PureExpr],stateUID:String, pvMap:Map[PureVar,T])(implicit zctx: C): T = {
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
    mkAnd(heapAst, mkAnd(heapFunConst))
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
   * @param zctx solver context
   * @return encoded formula for solver
   */
  def toASTState(state: State,
                       messageTranslator: MessageTranslator,
                       maxWitness: Option[Int] = None,
                       specSpace: SpecSpace,
                       debug:Boolean = false)(implicit zctx: C): T =
    toASTStateWithPv(state,messageTranslator, maxWitness, specSpace, debug, false)._1

  def toASTStateWithPv(state: State,
                      messageTranslator: MessageTranslator,
                      maxWitness: Option[Int] = None,
                      specSpace: SpecSpace,
                      debug:Boolean = false,
                      skolemizedPV:Boolean)(implicit zctx: C): (T, Map[PureVar,Option[T]]) = {

    if(debug){
      println(s"encoding state: ${state}")
    }


    val stateUniqueID = "" //TODO: should remove?
    val len = mkLenVar(s"len_$stateUniqueID") // there exists a finite size of the trace for this state
    val traceFun = mkTraceFn(stateUniqueID)
    val traceAbs = state.traceAbstraction
    val traceEnc: TraceAndSuffixEnc = encodeTraceAbs(traceAbs, messageTranslator, traceFn = traceFun, traceLen = len,
       specSpace = specSpace, debug = debug)
//    val encodedSuffix = traceEnc.suffix.getOrElse(mkBoolVal(b = true))

    def withPVMap(pvMapIn:Map[PureVar, T]):T =  {

      val pvMap = pvMapIn ++ traceEnc.definedPvMap
      // typeFun is a function from addresses to concrete types in the program
      val typeFun = createTypeFun()

      // *** Pure constraints ***
      val pureAst = state.pureFormula.foldLeft(mkBoolVal(true))((acc, v) =>
          mkAnd(acc, toAST(v, messageTranslator.getConstMap(),pvMap))
      )

      // *** Type constraints
      val tc = state.typeConstraints
      val encodedTypeConstraints = encodeTypeConstraints(tc, typeFun, messageTranslator, pvMap)

      // Encode locals
      val ll: Map[(String, Int), PureVar] = levelLocalPv(state)
      val localAST = toAST(ll, pvMap, stateUniqueID,messageTranslator)

      // Encode heap
      val heapAst = toAST(state.heapConstraints,stateUniqueID, pvMap)

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

      val out = mkAnd(List(refNeq, pureAst, localAST, heapAst, encodedTypeConstraints) ++ traceEnc.trace)
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
    }else {
      mkExistsAddr(pureVars, back,traceEnc.quantifiedPv)
    }
    (res,pureVars.map{
      case (k,v) => (pureVarsBack(k),v)
    })
  }

  private def encodeTypeConstraints(tc: Map[PureVar, TypeSet], typeFun:T,messageTranslator: MessageTranslator,
                                    pvMap:Map[PureVar,T] )(implicit zCtx:C): T = {

    val typeConstraints = tc.map { case (k, v) => k -> v.getValues }
    mkAnd(typeConstraints.flatMap {
      case (pv, Some(ts)) =>
        val tc = mkTypeConstraintForAddrExpr(typeFun, messageTranslator.getTypeToSolverConst, toAST(pv, pvMap), ts)
        Some(tc)
      case _ => None
    }.toList)

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
    } + NullVal + BoolVal(true) + BoolVal(false) + IntVal(0) + IntVal(1)
    private val (uniqueConst, constMap1) = mkConstConstraintsMap(pureValSet)
    val constMap = constMap1 +
      (BoolVal(true)-> constMap1(IntVal(1))) + (BoolVal(false) -> constMap1(IntVal(0)))
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
    val startTime = System.nanoTime()
    var result = "unfinished"
    try {
      zCtx.acquire()

      if (state.isSimplified){
        result = "sat"
        Some(state)
      }else {
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
        val stateWithNulls = nullsFromPt.foldLeft(state2) {
          case (state, (v, _)) => state.addPureConstraint(PureConstraint(v, Equals, NullVal))
        }
        val messageTranslator = MessageTranslator(List(stateWithNulls), specSpace)

        // Only encode types in Z3 for subsumption check due to slow-ness

        val ast =
          toASTState(stateWithNulls, messageTranslator, maxWitness,
             specSpace = specSpace, debug = maxWitness.isDefined)

        if (maxWitness.isDefined) {
          println(s"State ${System.identityHashCode(state2)} encoding: ")
          println(ast.toString)
        }
        zCtx.mkAssert(ast)
        val sat = checkSAT(false)
        //      val simpleAst = solverSimplify(ast, stateWithNulls, messageTranslator, maxWitness.isDefined)

        //      if(simpleAst.isEmpty)
        if (!sat) {
          result = "unsat"
          None
        } else {
          result = "sat"
          val reducedState = reduceStatePureVars(stateWithNulls.setSimplified()).map(gcPureVars)
          reducedState.map(_.setSimplified())
        }
      }
    }finally{
      zCtx.release()
      getLogger.warn(s"feasibility result: ${result} time(ms): ${(System.nanoTime() - startTime) / 1000.0}")
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

  private def canSwap(pv1:PureVar, pv2:PureVar, t1:Map[PureVar, TypeSet], t2:Map[PureVar, TypeSet]):Boolean = {
    val ts1 = t1.getOrElse(pv1, TopTypeSet)
    val ts2 = t2.getOrElse(pv2, TopTypeSet)
    ts1.contains(ts2)
  }
  /**
   * h2 => h1
   */
  private def canSubsumeUnifyHeap(h1:Map[HeapPtEdge, PureExpr], h2:Map[HeapPtEdge, PureExpr],
                          ts1:Map[PureVar, TypeSet], ts2:Map[PureVar,TypeSet],
                          h1Swap:Map[PureVar,PureVar]):List[Map[PureVar,PureVar]] = {
    if(h1.isEmpty)
      List(h1Swap)
    else {
      val subs = h1.head match {
        case (FieldPtEdge(p1, fieldName1), t1: PureVar) =>
          h2.toList.flatMap {
            case (e2@FieldPtEdge(p2, fieldName2), t2: PureVar) if fieldName1 == fieldName2 =>
              if ((!h1Swap.contains(p1) || h1Swap(p1) == p2)  // check if values either not swapped or swapped with same
                && (!h1Swap.contains(t1) || h1Swap(t1) == t2)
                && canSwap(p1, p2, ts1, ts2) && canSwap(t1, t2, ts1, ts2))
                Some(h1Swap ++ Map(p1 -> p2, t1 -> t2), e2)
              else None //TODO: a.f -> b * c.f->b ├ a.f->b * c.f->c
            case _ => None
          }
        case (StaticPtEdge(clazz1, fieldName1), t1: PureVar) =>
          h2.toList.flatMap {
            case (e2@StaticPtEdge(clazz2, fieldName2), t2: PureVar) if clazz1 == clazz2 && fieldName1 == fieldName2 =>
              if ((!h1Swap.contains(t1) || h1Swap(t1) == t2)&&canSwap(t1, t2, ts1, ts2))
                Some(h1Swap ++ Map(t1 -> t2), e2)
              else
                None
            case _ => None
          }
      }
      if(subs.isEmpty) {
        Nil
      } else{
        val out: List[Map[PureVar, PureVar]] = subs.flatMap{
          case (varMap, edge) =>
            val nextH1 = h1.tail
            val nextH2 = h2 - edge
            canSubsumeUnifyHeap(nextH1,nextH2, ts1, ts2, varMap)
        }
        out
      }

    }
  }
  private def canSubsumeUnifyLocals(l1:Map[(String,Int), PureVar], l2:Map[(String,Int),PureVar],
                                    ts1:Map[PureVar, TypeSet], ts2:Map[PureVar,TypeSet]): Option[Map[PureVar,PureVar]] = {
    Some(l1.map{
      case (k,v) if l2.contains(k) && canSwap(v, l2(k), ts1, ts2) => v -> l2(k)
      case _ => return None
    })
  }
  private def canSubsumeUnifyFreshRef(r1:Set[PureVar], r2:Set[PureVar],
                                      ts1:Map[PureVar, TypeSet], ts2:Map[PureVar,TypeSet],
                                      r1Swap:Map[PureVar, PureVar]):List[Map[PureVar,PureVar]] = {
    if(r1.isEmpty){
      // s2 => true
      return List(r1Swap)
    }
    val c1 = r1.head
    val possibleSwaps = if (r1Swap.contains(c1)) {
        if (!r2.contains(r1Swap(c1)))
          return Nil
        else
          Set(r1Swap(c1))
    } else {
        r2.filter{c2 => canSwap(c1,c2,ts1,ts2)}
    }
    if(possibleSwaps.isEmpty)
      return Nil

    possibleSwaps.toList.flatMap{c2 =>
      canSubsumeUnifyFreshRef(r1.tail, r2 - c2, ts1, ts2, r1Swap + (c1 -> c2))}
  }

  // p2 => p1
  private def canSubsumeUnifyPred(p1:LSPred, p2:LSPred):Option[(Map[String,String], Set[LSConstraint])] = (p1, p2) match {
    case (I(mt1,sig1,lsVars1), I(mt2, sig2, lsVars2))
      if(mt1 == mt2 && sig1.identifier == sig2.identifier && lsVars1.size == lsVars2.size) =>
      Some(((lsVars1 zip lsVars2).toMap, Set[LSConstraint]()))
    case (NI(_,_), _:I) =>
      None
    case (I(mt1,sig1,lsVars1), NI(I(mt2, sig2, lsVars2),_))
      if(mt1 == mt2 && sig1.identifier == sig2.identifier && lsVars1.size == lsVars2.size) =>
      ???
    case _ =>
      ???
  }
  private def validateLSSwap(swapMap:Map[String,String], lm1:Map[String,PureExpr], lm2:Map[String,PureExpr],
    ts1:Map[PureVar, TypeSet], ts2:Map[PureVar,TypeSet],
    r1Swap:Map[PureVar,PureVar]):Boolean = {
    swapMap.forall{
      case (k,v) =>
        ???
    }
  }
  //p2 => p1
  private def canSubsumeUnifyPreds(p1:Set[LSPred], p2:Set[LSPred],lm1:Map[String,PureExpr], lm2:Map[String,PureExpr],
                                  ts1:Map[PureVar, TypeSet], ts2:Map[PureVar,TypeSet],
                                  r1Swap:Map[PureVar,PureVar]):List[(Map[PureVar,PureVar], Set[PureConstraint])] = {
    if(p1.isEmpty)
      return List((r1Swap, Set[PureConstraint]()))
    val c1 = p1.head
    p2.toList.flatMap{c2 =>
      canSubsumeUnifyPred(c1, c2) match {
        case Some((newSwap, newPC)) if validateLSSwap(newSwap, lm1, lm2, ts1, ts2, r1Swap) =>
          println(newSwap)
          println(newPC)
          ???
        case Some((_, _)) =>
          None // Types or previous swap don't allow this assignment
        case None =>
          None
      }
    }
  }
  private def canSubsumeUnifyPure(ps1:Set[PureConstraint], ps2:Set[PureConstraint],
                                  r1Swap:Map[PureVar,PureVar]):Boolean = {
    def swapExpr(p:PureExpr):Option[PureExpr] = p match {
      case pureVal: PureVal => Some(pureVal)
      case v:PureVar if r1Swap.contains(v) => Some(r1Swap(v))
      case _ => None
    }
    val ps1Swapped = ps1.flatMap{
      case PureConstraint(lhs, op, rhs) =>
        val lhs2 = swapExpr(lhs)
        val rhs2 = swapExpr(rhs)
        if(lhs2.isDefined && rhs2.isDefined){
          Some(PureConstraint(lhs2.get,op,rhs2.get))
        }else None
    }
    ps1Swapped.forall(p => ps2.contains(p))
  }

  /**
   * check if s2 => s1
   * @return true if unification successful
   */
  def canSubsumeUnify(s1:State, s2:State, specSpace:SpecSpace): Boolean = {
    assert(s1.traceAbstraction == s2.traceAbstraction, "unify does not handle trace")
    val t1: Map[PureVar, TypeSet] = s1.sf.typeConstraints
    val t2 = s2.sf.typeConstraints
    val l1 = levelLocalPv(s1)
    val l2 = levelLocalPv(s2)
    val mapL = canSubsumeUnifyLocals(l1, l2, t1,t2)
    if(mapL.isEmpty)
      return false
    val h1: Map[HeapPtEdge, PureExpr] = s1.sf.heapConstraints
    val h2: Map[HeapPtEdge, PureExpr] = s2.sf.heapConstraints
    val mapsH: List[Map[PureVar, PureVar]] = canSubsumeUnifyHeap(h1,h2,t1,t2, mapL.get)

    val mapsR: Set[Map[PureVar, PureVar]] = mapsH.flatMap { mapH =>
      // Sets of pure vars that must be created in the future
      def freshRefSet(state: State): Set[PureVar] = {
        val tr = state.traceAbstraction
        tr.rightOfArrow.flatMap {
          case FreshRef(v) => Some(tr.modelVars(v).asInstanceOf[PureVar])
          case _ => None
        }.toSet
      }

      // Match up freshRefs.  s2 should have all freshRefs that s1 has
      val s1FreshRef = freshRefSet(s1)
      val s2FreshRef = freshRefSet(s2)
      // s2 should have been refuted before now if a heap cell contains a value that must be created in the future
      canSubsumeUnifyFreshRef(s1FreshRef, s2FreshRef, t1,t2, mapH)
    }.toSet //.filter(mapR => canSubsumeUnifyPure(s1.pureFormula, s2.pureFormula, mapR))

    // note: we assume traces are equal here so we ignore trace abstraction
    mapsR.exists{mapT =>
             canSubsumeUnifyPure(s1.sf.pureFormula, s2.sf.pureFormula,mapT)
    }

    // TODO: commented out code is faster non-z3 method, trying z3 for final subs before putting in time
    //    val pred1 = rhsToPred(s1.sf.traceAbstraction.rightOfArrow, specSpace).map(simplifyPred)
    //    val pred2: Set[LSPred] = rhsToPred(s2.sf.traceAbstraction.rightOfArrow, specSpace).map(simplifyPred)
    //    val lm1 = s1.sf.traceAbstraction.modelVars
    //    val lm2 = s2.sf.traceAbstraction.modelVars
    //    val mapsT: List[(Map[PureVar,PureVar], Set[PureConstraint])] = mapsR.flatMap{mapT =>
    //      canSubsumeUnifyPreds(pred1,pred2,lm1,lm2,t1,t2,mapT)
    //    }
    //    mapsT.exists{
    //      case (mapT, extraPure) =>
    //        canSubsumeUnifyPure(s1.sf.pureFormula ++ extraPure, s2.sf.pureFormula,mapT)
    //    }

    // TODO: below is attempt at dispatching trace query to Z3, didn't seem to be faster
    // Create version of s2 with all fresh pv so swapping doesn't conflict

//    if(false) {
//      val pv1: Set[PureVar] = s1.pureVars()
//      val pv2: Set[PureVar] = s2.pureVars()
//      val allPv = pv1.union(pv2).toList
//      // map s2 to something where all pvs are strictly larger
//      val maxID = if (allPv.nonEmpty) allPv.maxBy(_.id) else PureVar(5)
//
//
//      implicit val zCtx: C = getSolverCtx
//      // Swap all pureVars to pureVars above the max found in either state
//      // This way swapping doesn't interfere with itself
//      val (s1Above, pvToTemp) = pv1.foldLeft((s1.copy(nextAddr = maxID.id + 1), Map[PureVar, PureVar]())) {
//        case ((st, nl), pv) =>
//          val (freshPv, st2) = st.nextPv()
//          (st2.swapPv(pv, freshPv), nl + (pv -> freshPv))
//      }
//
//      // Check if one of the mappings allows subsumption
//      mapsR.exists { mapR =>
//        // determine if one of the mappings in mapsR allows subsumption over trace abstraction
//
//        val s1Swapped = mapR.foldLeft(s1Above) {
//          case (st, (oldPv, newPv)) => st.swapPv(pvToTemp(oldPv), newPv)
//        }
//
//        zCtx.acquire()
//        try {
//          val messageTranslator = MessageTranslator(List(s1Swapped, s2), specSpace)
//          val traceFun = mkTraceFn("")
//          val len = mkLenVar(s"len_") // there exists a finite size of the trace for this state
//          val pvMap = (s1Swapped.pureVars() ++ s2.pureVars()).map { pv => (pv -> mkPv(pv)) }.toMap
//          val typeFun: T = createTypeFun()
//
//          // State 1
//          //   trace
//          val tr1 = encodeTraceAbs(s1Swapped.traceAbstraction,
//            messageTranslator, traceFn = traceFun, traceLen = len, specSpace = specSpace, shouldEncodeRef = false,
//            definedPvMap = pvMap)
//
//          //   pure formula
//          val p1AST: Set[T] = s1Swapped.pureFormula.map { v =>
//            toAST(v, messageTranslator.getConstMap(), pvMap)
//          }
//
//          //   type enc
//          val p1TypeEnc: T = encodeTypeConstraints(s1Swapped.typeConstraints, typeFun, messageTranslator, pvMap)
//          //        val quantifyS1: List[T] = (s1Swapped.pureVars() -- mapR.values).map(pvMap).toList
//          val quantifyS1 = s1Swapped.pureVars().map(pvMap).toList
//
//          //   separation logic disjoint domain
//          val distinctCells1 = mkAnd(s1Swapped.heapConstraints.groupBy {
//            case (FieldPtEdge(_, fld), _) => Some(fld)
//            case _ => None
//          }.flatMap {
//            case (Some(fld), edges) =>
//              val srcS = edges.flatMap {
//                case (FieldPtEdge(src, fld2), _) if fld == fld2 => Some(src)
//                case _ => throw new IllegalStateException()
//              }
//              Some(mkDistinct(srcS, pvMap))
//            case (None, _) => None
//          }.toList)
//
//          val formula1: T = mkAnd(List(p1TypeEnc, distinctCells1) ++ tr1.trace ++ p1AST)
//          val s1Enc = mkExistsT(quantifyS1, formula1)
//
//          zCtx.mkAssert(mkNot(s1Enc))
//
//          // State 2
//          val tr2 = encodeTraceAbs(s2.traceAbstraction,
//            messageTranslator, traceFn = traceFun, traceLen = len, specSpace = specSpace, shouldEncodeRef = false,
//            definedPvMap = pvMap)
//
//          val p2AST = s2.pureFormula.map { v =>
//            toAST(v, messageTranslator.getConstMap(), pvMap)
//          }
//
//          val p2TypeEnc = encodeTypeConstraints(s2.typeConstraints, typeFun, messageTranslator, pvMap)
//
//          //        val quantifyS2 = (s2.pureVars() -- mapR.values).map(pvMap).toList
//          val quantifyS2 = s2.pureVars().map(pvMap).toList // TODO: ==== debug
//
//          //   separation logic disjoint domain
//          val distinctCells2 = mkAnd(s2.heapConstraints.groupBy {
//            case (FieldPtEdge(_, fld), _) => Some(fld)
//            case _ => None
//          }.flatMap {
//            case (Some(fld), edges) =>
//              val srcS = edges.flatMap {
//                case (FieldPtEdge(src, fld2), _) if fld == fld2 => Some(src)
//                case _ => throw new IllegalStateException()
//              }
//              Some(mkDistinct(srcS, pvMap))
//            case (None, _) => None
//          }.toList)
//
//          val formula2 = mkAnd(List(p2TypeEnc, distinctCells2) ++ tr2.trace ++ p2AST)
//          val s2Enc = mkExistsT(quantifyS2, formula2)
//          zCtx.mkAssert(s2Enc)
//
//          val foundCounter =
//            checkSAT(useCmd = false)
//          //try {
//          //        }catch {
//          //          case e:IllegalStateException => {
//          //            val s1Ser = write(s1)
//          //            val s2Ser = write(s2)
//          //            val ctime = System.currentTimeMillis()
//          //            val f1 = File(s"s1_unify_timeout_${ctime}.json")
//          //            val f2 = File(s"s2_unify_timeotu_${ctime}.json")
//          //            f1.write(s1Ser)
//          //            f2.write(s2Ser)
//          //            println("decision timeout, assuming no subsumption")
//          //            e.printStackTrace()
//          //            true // negated later so true says don't subsume here
//          //          }
//          //        }
//          // TODO:==== weird difference between z3 and unify
//          //printDbgModel(messageTranslator, Set(s1Swapped.traceAbstraction,s2.traceAbstraction), "")
//          !foundCounter
//
//        } finally {
//          zCtx.release()
//        }
//      }
//    }
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
      case i:I => Set(s"I_${i.identitySignature}")
      case NI(i1,i2) => Set(s"NI_${i1.identitySignature}__${i2.identitySignature}") ++ mustI(i1)
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
      case Not(i:I) => Set()
      case Not(p) => throw new IllegalStateException(s"expected normal form in pred: ${p}")
      case Or(l1, l2) => mayI(l1).union(mayI(l2))
      case LifeState.LSTrue => Set()
      case LifeState.LSFalse => Set()
      case i:I => Set(s"I_${i.identitySignature}")
      case NI(i1,i2) => Set(s"NI_${i1.identitySignature}__${i2.identitySignature}") ++ mayI(i1)
    }
    pred.flatMap(mayI)
  }

  /**
   *
   *
   * @param s1 subsuming state
   * @param s2 contained state
   *           checks s2 => s1
   * @return
   */
  def canSubsume(s1: State, s2: State, specSpace: SpecSpace, maxLen: Option[Int] = None,
                 timeout:Option[Int] = None): Boolean = {
    val mustIs = mustISet(s1,specSpace)
    val mayIs = mayISet(s2, specSpace)
    if (mustIs.exists(v => !mayIs.contains(v))) {
      return false
    }
//     val method = "Unify"//TODO: benchmark and see if this is actually faster: Idea run both and log times then hist
//     val method = "Debug"
    val method = "Z3"
    // val method = "FailOver"
    val startTime = System.nanoTime()
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

    //// Compute the set of required positive "I"s.  Cannot subsume if not subset
    //val s1Pred = StateSolver.rhsToPred(s1.sf.traceAbstraction.rightOfArrow, specSpace)
    //val s1MustI = s1Pred.flatMap(mustISet)
    //val s2Pred = StateSolver.rhsToPred(s2.sf.traceAbstraction.rightOfArrow, specSpace)
    //val s2MustI = s2Pred.flatMap(mustISet)
    ////TODO: is there something we could do to quickly eliminate tracepred subsumption without calling z3?


    // TODO: test if requiring subsuming state is suffix of subsumee improves speed
    // TODO: this should be done by StateSet rather than here for better performance
    // Note: sound but possibly not precise
    // if(!suffixSame(s1.sf.traceAbstraction.rightOfArrow, s2.sf.traceAbstraction.rightOfArrow))
    //   return false
    val s1Simp = simplify(s1, specSpace)
    val s2Simp = simplify(s2, specSpace)
    if(s2Simp.isEmpty)
      return true


    //TODO: =========== try to use unification subs when trace abs is same
    // note: unification pure formula subs is busted
//    if(s1Simp.get.traceAbstraction == s2Simp.get.traceAbstraction){
//      val csu = canSubsumeUnify(s1,s2, specSpace)
//      if(true){
//        // dbg code
//        val zsu = canSubsumeZ3(s1Simp.get,s2Simp.get,specSpace, maxLen, timeout)
//        assert(zsu == csu)
//      }
//      return csu
//    }

    val res = if(method == "Z3")
      canSubsumeZ3(s1Simp.get,s2Simp.get,specSpace, maxLen, timeout)
    else if(method == "Unify")
      canSubsumeUnify(s1Simp.get,s2Simp.get,specSpace)
    else if(method == "FailOver"){
      try{canSubsumeUnify(s1Simp.get, s2Simp.get, specSpace)} catch{
        case _:IllegalStateException =>
          canSubsumeZ3(s1Simp.get, s2Simp.get, specSpace, maxLen, timeout)
      }
    } else if(method == "Debug") {
      val z3res = canSubsumeZ3(s1Simp.get, s2Simp.get, specSpace, maxLen, timeout)
      val unifyRes = canSubsumeUnify(s1Simp.get,s2Simp.get,specSpace)
      if(z3res != unifyRes) {
        val s1Ser = write(s1)
        val s2Ser = write(s2)
        val ctime = System.currentTimeMillis()
        val f1 = File(s"s1_diff_${ctime}.json")
        f1.write(s1Ser)
        val f2 = File(s"s2_diff_${ctime}.json")
        val s1Deser = read[State](s1Ser)
        val s2Deser = read[State](s2Ser)
        println(s1Deser)
        println(s2Deser)
        val z3res2 = canSubsumeZ3(s1Simp.get, s2Simp.get, specSpace,maxLen, timeout)
        val unifres2 = canSubsumeUnify(s1Simp.get, s2Simp.get, specSpace)
        //throw new IllegalStateException("different results")
      }
      z3res
    } else {
      println("""Expected method: "Unify" or "Z3" """)
      throw new IllegalArgumentException("""Expected method: "Unify" or "Z3" """)
    }
//    catch {
//      case e:IllegalStateException =>
//              throw e
////        println(s"Subsumption returning false due to timeout: ${e.getMessage}")
////        getLogger.warn(s"subsumption result:timeout time(ms): ${(System.nanoTime() - startTime)/1000.0}")
////        false
//    }

    getLogger.warn(s"subsumption result:${res} time(ms): ${(System.nanoTime() - startTime)/1000.0}")
    res
  }
  // s1 subsuming state
  // s2 state being subsumed
  // TODO: May want to handle alpha renaming, but see if this works first
  private def suffixSame(s1Suffix: List[LSSingle], s2Suffix:List[LSSingle]):Boolean = (s1Suffix, s2Suffix) match{
    case (I(mt1,sig1,v)::t1, I(mt2,sig2,_)::t2) if mt1 != mt2 || sig1 != sig2 => suffixSame(I(mt1,sig1,v)::t1, t2)
    case (I(mt1,sig1,_)::t1, I(mt2,sig2,_)::t2) if mt1 == mt2 && sig1 == sig2 => suffixSame(t1,t2)
    case (FreshRef(_)::t1, s2Suffix) => suffixSame(t1,s2Suffix)
    case (CLInit(_)::t1, s2Suffix) => suffixSame(t1,s2Suffix)
    case (s1Suffix, FreshRef(_)::t2) => suffixSame(s1Suffix,t2)
    case (s1Suffix, CLInit(_)::t2) => suffixSame(s1Suffix,t2)
    case (Nil,_) => true
    case (_::_, Nil) => false
  }
  private def suffix(state:State):List[String] = {
    state.sf.traceAbstraction.rightOfArrow.map {
      case c@CLInit(_) => c.toString
      case FreshRef(_) => "FreshRef"
      case I(mt, signatures, _) => s"I(${mt}, ${signatures.identifier})"
    }
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
    case I(mt, signatures, lsVars) => Set((mt,signatures))
    case NI(i1, i2) => mustISet(i1)
  }

  def allTypes(state:State)(implicit zctx:C):Set[Int] = {
    val pvMap = state.typeConstraints
    val usedTypes = pvMap.flatMap { case (_, tc) => tc.getValues.getOrElse(Set()) }.toSet
    mkTypeConstraints(usedTypes)
    usedTypes
  }

  //TODO: this method could probably be more efficient
  /**
   * Remove points to regions that are redundant with respect to z3 subsumption check
   * This is a hack to deal with the thousands of points to regions that are produced by spark.
   * e.g. a state with pt regions such as:
   *   p-1 : 100,101,102
   *   p-2 : 50, 51, 52
   *   p-3 : 102
   *  would become:
   *   p-1 : 100,102
   *   p-2 : 50
   *   p-3 : 102
   * @param s1 subsuming state
   * @param s2 state to be subsumed
   * @return (s1,s2) where points to sets contain 1 representative element but no more
   */
  def reducePtRegions(s1:State, s2:State): (State,State) = {
    def tc(id:Int,s:State) = {
      s.typeConstraints.map{
        case (k,v) => (id,k,v)
      }
    }
    val spt = tc(1,s1) ++ tc(2,s2)

    //Get set of all regions
    var allSet = mutable.BitSet()
    spt.foreach{
      case (_,_, PrimTypeSet(n)) =>
      case (_,_, EmptyTypeSet) =>
      case (_,_, TopTypeSet) =>
      case (_, _, set) => allSet.addAll(set.getValues.getOrElse(mutable.BitSet())) // addAll uses a |= b under the hood
    }
    allSet.toImmutable

    // Iterate over each pt region and collect sets of regions including a pt value
    val setSet = allSet.foldLeft(Set[List[(Int,PureVar, TypeSet)]]()){ case (set,pt) =>
      val typeSetsContainingValue: List[(Int, PureVar, TypeSet)] = spt.filter {
        case (_, _, set) => set.contains(pt)
      }.toList
      set + typeSetsContainingValue
    }.toList.zipWithIndex // create artificial value for each set of sets and add to each associated set
    //TODO: may be better to have a representative pt element here instead of index

    // construct modified s1 and s2

    val outS1 = s1.typeConstraints.flatMap{
      case (k,_:BitTypeSet) => Some((k,mutable.BitSet()))
      case (k,ts) => None
    }
    val outS2 = s2.typeConstraints.flatMap{
      case (k,_:BitTypeSet) => Some((k,mutable.BitSet()))
      case (k,ts) => None
    }
    setSet.foreach{
      case (updList, i) =>
        updList.foreach{
          case (oldSt, pv, _) =>
            val updSt = if(oldSt == 1) outS1 else if(oldSt == 2) outS2 else throw new IllegalStateException("nostate")
            if(updSt.contains(pv)) {
              updSt(pv) += i
            }
        }
    }
    def constructSt(s:State, map: Map[PureVar, mutable.BitSet]):State = {
      map.foldLeft(s){
        case (st, (pv,bts)) => st.addTypeConstraint(pv,BitTypeSet(bts))
      }
    }
    val res = (constructSt(s1, outS1), constructSt(s2,outS2))
    res
  }

  /**
   * use the z3 encoding to test subsumption
   * @param s1i subsuming state
   * @param s2i state testing if it can be subsumed
   * @param specSpace specifications under which subsumption may occur
   * @param maxLen set to Some([num]) for dbg mode, witness will be limited to [num] length
   * @param timeout z3 timeout in milliseconds
   * @param rngTry number of attempts with different prng seeds
   * @return true if s1i can subsume s2i otherwise false
   */
  def canSubsumeZ3(s1i:State, s2i:State,specSpace:SpecSpace, maxLen:Option[Int], timeout:Option[Int],
                   rngTry:Int = 0):Boolean = {
    val (s1,s2) = reducePtRegions(s1i,s2i) //TODO: does reducing pts regions help?
//    val (s1,s2) = (s1i,s2i)
    implicit val zCtx: C = getSolverCtx
    try {
      if(rngTry == 0)
        zCtx.acquire(None)
      else if(rngTry > 0){
        // on retry, seed RNG with try number for determinism
        val rngSeed = rngTry
        println(s"try again with new random seed: ${rngSeed}")
        zCtx.acquire(Some(rngSeed))
      }else{
        throw new IllegalStateException("Timeout, exceeded rng seed attempts")
      }
      val messageTranslator: MessageTranslator = MessageTranslator(List(s1, s2), specSpace)

      val s1Enc = mkNot(toASTState(s1, messageTranslator, maxLen,
        specSpace = specSpace, debug = maxLen.isDefined))
      zCtx.mkAssert(s1Enc)
      val s2Enc = toASTState(s2, messageTranslator, maxLen,
        specSpace = specSpace, debug = maxLen.isDefined)
      zCtx.mkAssert(s2Enc)
      val foundCounter =
        checkSAT(useCmd = false)

      if (foundCounter && maxLen.isDefined) {
        printDbgModel(messageTranslator, Set(s1.traceAbstraction,s2.traceAbstraction), "")
      }
      !foundCounter
    }catch{
      case e:IllegalArgumentException if e.getLocalizedMessage.contains("timeout") =>
        // Note: this didn't seem to help things so currently disabled
        // sound to say state is not subsumed if we don't know
        // false

        println("subsumption timeout:")
        println(s"timeout: ${timeout}")
        println(s"  s1: ${s1}")
        println(s"  s1 ɸ_lhs: " +
          s"${StateSolver.rhsToPred(s1.traceAbstraction.rightOfArrow,specSpace)
            .map(pred => pred.stringRep(v => s1.sf.traceAbstraction.modelVars.getOrElse(v,v)))
            .mkString("  &&  ")}")
        println(s"  s2: ${s2}")
        println(s"  s2 ɸ_lhs: " +
          s"${StateSolver.rhsToPred(s2.traceAbstraction.rightOfArrow,specSpace)
            .map(pred => pred.stringRep(v => s2.sf.traceAbstraction.modelVars.getOrElse(v,v)))
            .mkString("  &&  ")}")
        // uncomment to dump serialized timeout states
        // val s1f = File("s1_timeout.json")
        // val s2f = File("s2_timeout.json")
        val s1str = write(s1)
        val s2str = write(s2)
        println(s1str)
        println(s2str)
        // s1f.write(write(s1))
        // s2f.write(write(s2))
        // throw e

        // try 3 times with different random seeds
        if(rngTry < 2){
          zCtx.release()
          canSubsumeZ3(s1i,s2i,specSpace,maxLen,timeout, rngTry+1)
        }else {
          zCtx.release()
          println("Giving up and not subsuming.")
          false
        }
    } finally {
      zCtx.release()
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
                         trace: List[TMessage],
                         debug: Boolean = false)(implicit zCtx: C): Option[WitnessExplanation] = {
    try {
      zCtx.acquire()
      val messageTranslator = MessageTranslator(List(state), specSpace)
      val pvMap: Map[PureVar, Option[T]] = encodeTraceContained(state, trace, messageTranslator = messageTranslator, specSpace = specSpace)
      val sat = checkSAT(useCmd = false)
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
      zCtx.release()
    }
  }

  def mkIndex(num:Int)(implicit zctx: C):(T,T) = {
    (0 until num).foldLeft((mkZeroIndex, mkBoolVal(b = true))){case (acc,_) =>
      val (ivIsInc,iv) = mkAddOneIndex(acc._1)
      (iv,mkAnd(acc._2, ivIsInc))
    }
  }
  private def encodeTraceContained(state: State, trace: List[TMessage], specSpace: SpecSpace,
                                   messageTranslator: MessageTranslator)(implicit zCtx: C): Map[PureVar, Option[T]] = {
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
      specSpace = specSpace,skolemizedPV = true)
    val encodedTrace = encodeTrace(traceFn, trace, messageTranslator, distinctAddr)

    zCtx.mkAssert(encodedState)
    zCtx.mkAssert(encodedTrace)

    pvMap
  }

}