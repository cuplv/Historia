package edu.colorado.plv.bounder.solver

import com.microsoft.z3.AST
import edu.colorado.plv.bounder.ir.{TAddr, TMessage, TNullVal}
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState._
import edu.colorado.plv.bounder.symbolicexecutor.state.{HeapPtEdge, _}
import org.slf4j.LoggerFactory
import scalaz.Memo
import scala.collection.parallel.CollectionConverters._
import upickle.default._

import scala.collection.immutable

trait Assumptions

class UnknownSMTResult(msg : String) extends Exception(msg)
trait SolverCtx

/** SMT solver parameterized by its AST or expression type */
trait StateSolver[T, C <: SolverCtx] {
  private val logger = LoggerFactory.getLogger(classOf[StateSolver[T, C]])

  // checking
  def getSolverCtx: C

  def checkSAT()(implicit zctx: C): Boolean

  def push()(implicit zctx: C): Unit

  def pop()(implicit zctx: C): Unit


  // quantifiers
  /**
   * forall int condition is true
   *
   * @param cond
   */
  protected def mkForallInt(min: T, max: T, cond: T => T)(implicit zctx: C): T

  protected def mkForallAddr(name: String, cond: T => T)(implicit zctx: C): T

  protected def mkExistsAddr(name: String, cond: AST => AST)(implicit zctx: Z3SolverCtx): AST

  protected def mkExistsInt(min: T, max: T, cond: T => T)(implicit zctx: C): T

  // comparison operations
  protected def mkEq(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkNe(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkGt(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkLt(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkGe(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkLe(lhs: T, rhs: T)(implicit zctx: C): T

  // logical and arithmetic operations
  protected def mkImplies(t: T, t1: T)(implicit zctx: C): T

  protected def mkNot(o: T)(implicit zctx: C): T

  protected def mkAdd(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkSub(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkMul(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkDiv(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkRem(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkAnd(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkAnd(t: List[T])(implicit zctx: C): T

  protected def mkOr(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkOr(t: List[T])(implicit zctx: C): T

  protected def mkExactlyOneOf(l: List[T])(implicit zctx: C): T

  // creation of variables, constants, assertions
  protected def mkIntVal(i: Int)(implicit zctx: C): T

  protected def mkBoolVal(b: Boolean)(implicit zctx: C): T

  protected def mkIntVar(s: String)(implicit zctx: C): T

  protected def mkFreshIntVar(s: String)(implicit zctx: C): T

  protected def mkBoolVar(s: String)(implicit zctx: C): T

  protected def mkObjVar(s: PureVar)(implicit zctx: C): T //Symbolic variable
  protected def mkModelVar(s: String, predUniqueID: String)(implicit zctx: C): T // model vars are scoped to trace abstraction
  protected def mkAssert(t: T)(implicit zctx: C): Unit

  protected def mkFieldFun(n: String)(implicit zctx: C): T

  protected def fieldEquals(fieldFun: T, t1: T, t2: T)(implicit zctx: C): T

  protected def solverSimplify(t: T,
                               state: State,
                               messageTranslator: MessageTranslator, logDbg: Boolean = false)(implicit zctx: C): Option[T]

  protected def mkTypeConstraints(types: Set[String])(implicit zctx: C): (T, Map[String, T])

  protected def mkTypeConstraintForAddrExpr(typeFun: T, typeToSolverConst: Map[String, T],
                                            addr: T, tc: Set[String])(implicit zctx: C): T

  protected def createTypeFun()(implicit zctx: C): T

  // TODO: swap enum with uninterpreted type
  protected def mkEnum(name: String, types: List[String])(implicit zctx: C): T

  protected def getEnumElement(enum: T, i: Int)(implicit zctx: C): T

  // function traceIndex -> msg
  protected def mkTraceFn(uid: String)(implicit zctx: C): T

  protected def mkFreshTraceFn(uid: String)(implicit zctx: C): T

  // function msg -> iname
  protected def mkINameFn(enum: T)(implicit zctx: C): T

  // function for argument i -> msg -> addr
  protected def mkArgFun()(implicit zctx: C): T

  // function to test if addr is null
  // Uses uninterpreted function isNullFn : addr -> bool
  protected def mkIsNull(addr: T)(implicit zctx: C): T

  // Get enum value for I based on index
  protected def mkIName(enum: T, enumNum: Int)(implicit zctx: C): T

  // function from index to message (message is at index in trace)
  protected def mkTraceConstraint(traceFun: T, index: T)(implicit zctx: C): T

  // function msg -> funname
  protected def mkNameConstraint(nameFun: T, msg: T)(implicit zctx: C): T

  // function argumentindex -> msg -> argvalue
  protected def mkArgConstraint(argFun: T, argIndex: T, msg: T)(implicit zctx: C): T

  protected def mkAddrConst(i: Int)(implicit zctx: C): T

  def printDbgModel(messageTranslator: MessageTranslator, traceabst: Set[AbstractTrace],
                    lenUID: String)(implicit zctx: C): Unit

  def compareConstValueOf(rhs: T, op: CmpOp, pureVal: PureVal)(implicit zctx: C): T = {
    (pureVal, op) match {
      case (NullVal, Equals) => mkIsNull(rhs)
      case (NullVal, NotEquals) => mkNot(mkIsNull(rhs))
      case (v, Equals) if v == pureVal => mkBoolVal(true)
      case (ClassVal(_), _) => mkBoolVal(true) //TODO: add class vals if necessary for precision
      case (IntVal(_), _) => mkBoolVal(true)
      case v =>
        println(v)
        ???
    }
  }

  def toAST(p: PureConstraint)(implicit zctx: C): T = p match {
    // TODO: field constraints based on containing object constraints
    case PureConstraint(lhs: PureVar, TypeComp, rhs: TypeConstraint) =>
      throw new IllegalStateException("Pure constraints should be filtered out before here.")
    //      val typeSet = persist.typeSetForPureVar(lhs,state)
    //      mkTypeConstraint(typeFun, toAST(lhs), rhs)
    case PureConstraint(v: PureVal, op, rhs) => compareConstValueOf(toAST(rhs), op, v)
    case PureConstraint(lhs, op, v: PureVal) => compareConstValueOf(toAST(lhs), op, v)
    case PureConstraint(lhs, op, rhs) =>
      toAST(toAST(lhs), op, toAST(rhs))
    case _ => ???
  }

  def toAST(p: PureExpr)(implicit zctx: C): T = p match {
    case p: PureVar => mkObjVar(p)
    case _ => throw new IllegalStateException("Values should be handled at a higher level")
  }

  def toAST(lhs: T, op: CmpOp, rhs: T)(implicit zctx: C): T = op match {
    case Equals => mkEq(lhs, rhs)
    case NotEquals =>
      mkNe(lhs, rhs)
    case _ =>
      ???
  }

  /**
   * Formula representing truth of "m is at position index in traceFn"
   *
   * @param index   index of the message (ArithExpr)
   * @param m
   * @param messageTranslator
   * @param traceFn : Int->Msg
   * @return
   */
  private def assertIAt(index: T, m: I,
                        messageTranslator: MessageTranslator,
                        traceFn: T, // Int -> Msg
                        negated: Boolean = false,
                        modelVarMap: String => T)(implicit zctx: C): T = {
    val msgExpr = mkTraceConstraint(traceFn, index)
    val nameFun = messageTranslator.nameFun
    val nameConstraint = mkEq(mkNameConstraint(nameFun, msgExpr), messageTranslator.enumFromI(m))
    val argConstraints = m.lsVars.zipWithIndex.flatMap {
      case (LSAnyVal(), _) => None //TODO: primitive value cases
      case (msgVar, ind) =>
        //        val modelVar = modelVarMap(msgVar)
        val modelExpr = encodeModelVarOrConst(msgVar, modelVarMap)
        Some(mkEq(mkArgConstraint(mkArgFun(), mkIntVal(ind), msgExpr), modelExpr))
    }

    // w[i] = cb foo(x,y)
    // If we are asserting that a message is not at a location, the arg function cannot be negated due to skolemization
    // We only negate the name function
    if (negated)
      mkOr(mkNot(nameConstraint), mkOr(argConstraints.map(mkNot)))
    else
      mkAnd(nameConstraint, mkAnd(argConstraints))
  }

  private def encodeModelVarOrConst(lsExpr: String, modelVarMap: String => T)(implicit zctx: C): T = lsExpr match {
    case LifeState.LSVar(v) => modelVarMap(v)
    case LifeState.LSConst(const) => toAST(const)
    case LifeState.LSAnyVal() =>
      throw new IllegalStateException("AnyVal shouldn't reach here")
  }

  private def encodePred(combinedPred: LifeState.LSPred, traceFn: T, len: T,
                         messageTranslator: MessageTranslator
                         , modelVarMap: Map[String, T], negate: Boolean = false)(implicit zctx: C): T = combinedPred match {
    case And(l1, l2) if !negate => mkAnd(encodePred(l1, traceFn, len, messageTranslator, modelVarMap),
      encodePred(l2, traceFn, len, messageTranslator, modelVarMap))
    case And(l1, l2) if negate => mkOr(
      encodePred(l1, traceFn, len, messageTranslator, modelVarMap, negate = true),
      encodePred(l2, traceFn, len, messageTranslator, modelVarMap, negate = true)
    )
    case Or(l1, l2) if !negate => mkOr(encodePred(l1, traceFn, len, messageTranslator, modelVarMap),
      encodePred(l2, traceFn, len, messageTranslator, modelVarMap))
    case Or(l1, l2) if negate => mkAnd(encodePred(l1, traceFn, len, messageTranslator, modelVarMap, negate = true),
      encodePred(l2, traceFn, len, messageTranslator, modelVarMap, negate = true))
    //    case Not(m:I) if !negate =>
    //      mkForallInt(mkIntVal(-1),len, i => assertIAt(i,m,messageTranslator,traceFn,absUID,true))
    case Not(l) =>
      encodePred(l, traceFn, len, messageTranslator, modelVarMap, !negate)
    case m@I(_, _, _) if !negate =>
      mkExistsInt(mkIntVal(-1), len,
        i => assertIAt(i, m, messageTranslator, traceFn, negated = false, modelVarMap))
    case m: I if negate =>
      mkForallInt(mkIntVal(-1), len, i => assertIAt(i, m, messageTranslator, traceFn, negated = true, modelVarMap))
    case NI(m1, m2) if !negate =>
      // exists i such that omega[i] = m1 and forall j > i omega[j] != m2
      mkExistsInt(mkIntVal(-1), len, i => mkAnd(List(
        assertIAt(i, m1, messageTranslator, traceFn, negated = false, modelVarMap),
        mkForallInt(i, len, j => assertIAt(j, m2, messageTranslator, traceFn, negated = true, modelVarMap))
      )))
    case NI(m1, m2) if negate =>
      // not NI(m1,m2) def= (not I(m1)) or NI(m2,m1)
      // encode with no negation
      encodePred(Or(Not(m1), NI(m2, m1)), traceFn, len, messageTranslator, modelVarMap)
    case LSFalse =>
      mkBoolVal(negate)
    case LSTrue =>
      mkBoolVal(!negate)
  }


  private def allITraceAbs(traceAbstractionSet: Set[AbstractTrace], includeArrow: Boolean = false): Set[I] =
    traceAbstractionSet.flatMap(a => allI(a, includeArrow))

  private def allI(pred: LSPred): Set[I] = pred match {
    case i@I(_, _, _) => Set(i)
    case NI(i1, i2) => Set(i1, i2)
    case And(l1, l2) => allI(l1).union(allI(l2))
    case Or(l1, l2) => allI(l1).union(allI(l2))
    case Not(l) => allI(l)
    case LSTrue => Set()
    case LSFalse => Set()
  }

  private def allI(abs: AbstractTrace, includeArrow: Boolean): Set[I] = abs match {
    case AbstractTrace(pred, i2, mapping) =>
      if (includeArrow)
        allI(pred) ++ i2
      else
        allI(pred)
  }

  /**
   *
   * @param abs               abstraction of trace to encode for the solver
   * @param messageTranslator mapping from I preds to enum elements
   * @param traceFn           solver function from indices to trace messages
   * @param traceLen          total length of trace including arrow constraints
   * @param absUID            optional unique id for model variables to scope properly,
   *                          if none is provided, identity hash code of abs is used
   * @param negate            encode the assertion that traceFn is not in abs,
   *                          note that "mkNot(encodeTraceAbs(..." does not work due to skolomization
   * @return encoded trace abstraction
   */
  def encodeTraceAbs(abs: AbstractTrace, messageTranslator: MessageTranslator, traceFn: T, traceLen: T,
                     absUID: Option[String] = None, negate: Boolean = false)(implicit zctx: C): T = {
    val uniqueAbsId = absUID.getOrElse(System.identityHashCode(abs).toString)

    def ienc(sublen: T, f: LSPred, modelVarsConstraints: Map[String, PureExpr], traceFn: T,
             modelVars: Map[String, T], negate: Boolean): T = {
      val modelConstraints: List[T] = modelVarsConstraints.map {
        case (k, v: PureVar) => mkEq(mkModelVar(k, uniqueAbsId), mkObjVar(v))
        case _ => ???
      }.toList
      mkAnd(
        encodePred(f, traceFn, sublen, messageTranslator, modelVars, negate), mkAnd(modelConstraints))
    }

    // encoding is function of model variables to solver boolean expression T
    val modelVarsToEncoding: Map[String, T] => T = { modelVars =>
      val freshTraceFun = mkFreshTraceFn("arrowtf")
      val beforeIndEq =
        mkForallInt(mkIntVal(-1), traceLen, i =>
          mkEq(mkTraceConstraint(traceFn, i), mkTraceConstraint(freshTraceFun, i)))
      val (suffixConstraint, endlen) = abs.rightOfArrow.foldLeft((beforeIndEq, traceLen)) {
        case ((acc, ind), i) => (
          mkAnd(acc, assertIAt(ind, i, messageTranslator, freshTraceFun, negated = false, modelVars)),
          mkAdd(ind, mkIntVal(1))
        )
      }
      val absEnc = ienc(endlen, abs.a, abs.modelVars, freshTraceFun, modelVars, negate)
      mkAnd(absEnc, suffixConstraint)
    }

    val allLSVarsInPred = abs.a.lsVar ++ abs.rightOfArrow.flatMap(_.lsVar)
    if(negate)
      allLSVarsInPred.foldLeft(modelVarsToEncoding){
        case(acc,lsVar) => {
          (lsMap:Map[String,T]) => mkForallAddr(lsVar,tMV => acc(lsMap + (lsVar -> tMV)))
        }
      }(Map())
    else{
      val modelVarMap = allLSVarsInPred.map(varname => (varname,mkModelVar(varname,uniqueAbsId))).toMap
      modelVarsToEncoding(modelVarMap)
    }
  }

  protected def mkDistinct(pvList: Iterable[PureVar])(implicit zctx: C): T

  protected def mkDistinctT(tList: Iterable[T])(implicit zctx: C): T

  protected def encodeTypeConsteraints: StateTypeSolving

  protected def persist: ClassHierarchyConstraints

  private implicit val ch = persist

  def toAST(heap: Map[HeapPtEdge, PureExpr])(implicit zctx: C): T = {
    // The only constraint we get from the heap is that domain elements must be distinct
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
      mkAnd(acc, mkDistinct(pvList))
    }
    heapAst
  }

  def toAST(state: State, typeToSolverConst: Map[String, T],
            messageTranslator: MessageTranslator,
            maxWitness: Option[Int] = None)(implicit zctx: C): T = {
    state.pureVars()
    val pure = state.pureFormula
    // typeFun is a function from addresses to concrete types in the program
    val typeFun = createTypeFun()

    // pure formula are for asserting that two abstract addresses alias each other or not
    //  as well as asserting upper and lower bounds on concrete types associated with addresses
    val pureNoTypes = pure.filter {
      case PureConstraint(_, TypeComp, _) => false
      case _ => true
    }
    val pureAst = pureNoTypes.foldLeft(mkBoolVal(true))((acc, v) =>
      mkAnd(acc, toAST(v))
    )

    val typeConstraints = if (encodeTypeConsteraints == SolverTypeSolving) {
      //      // Encode type constraints in Z3
      val typeConstraints = state.typeConstraints.map { case (k, v) => k -> v.typeSet(ch) }
      //      val typeConstraints = persist.pureVarTypeMap(state)
      typeConstraints.keySet.filter(pv => state.pureFormula.exists {
        case PureConstraint(v1, TypeComp, _) => v1 == pv
        case _ => false
      })
      mkAnd(typeConstraints.map { case (pv, ts) => mkTypeConstraintForAddrExpr(typeFun, typeToSolverConst, toAST(pv), ts) }.toList)
    } else mkBoolVal(true)

    val heapAst = toAST(state.heapConstraints)

    // Identity hash code of trace abstraction used when encoding a state so that quantifiers are independent
    val stateUniqueID = System.identityHashCode(state).toString

    val tracefun = mkTraceFn(stateUniqueID)
    val len = mkIntVar(s"len_$stateUniqueID") // there exists a finite size of the trace for this state
    val trace = state.traceAbstraction.foldLeft(mkBoolVal(true)) {
      case (acc, v) => mkAnd(acc, encodeTraceAbs(v, messageTranslator,
        traceFn = tracefun, traceLen = len))
    }
    val out = mkAnd(mkAnd(mkAnd(pureAst, heapAst), trace), typeConstraints)
    maxWitness.foldLeft(out) { (acc, v) => mkAnd(mkLt(len, mkIntVal(v)), acc) }
  }

  case class MessageTranslator(states: List[State])(implicit zctx: C) {
    private val alli = allITraceAbs(states.flatMap(_.traceAbstraction).toSet, includeArrow = true)
    private val inameToI: Map[String, Set[I]] = alli.groupBy(_.identitySignature)
    private val inamelist = "OTHEROTHEROTHER" :: inameToI.keySet.toList
    private val iNameIntMap: Map[String, Int] = inamelist.zipWithIndex.toMap
    private val enum = mkEnum("inames", inamelist)

    def enumFromI(m: I): T = mkIName(enum, iNameIntMap(m.identitySignature))

    def getEnum: T = enum

    def nameFun: T = mkINameFn(enum)

    def iForMsg(m: TMessage): Option[I] = {
      val possibleI = alli.filter(ci =>
        ci.signatures.contains(m.fwkSig.get) && ci.mt == m.mType)
      assert(possibleI.size < 2)
      possibleI.headOption
    }

    def iForZ3Name(z3Name: String): Set[I] = {
      inameToI.getOrElse(z3Name, Set())
    }

  }

  def reduceStatePureVars(state: State): State = {
    assert(state.isSimplified, "reduceStatePureVars must be called on feasible state.")
    // TODO: test for trace enforcing that pure vars are equivalent
    val swappedForSmallerPv = state.pureFormula.foldLeft(state) {
      case (acc, pc@PureConstraint(v1@PureVar(id1), Equals, v2@PureVar(id2))) if id1 < id2 =>
        acc.copy(pureFormula = acc.pureFormula - pc).swapPv(v2, v1)
      case (acc, pc@PureConstraint(v1@PureVar(id1), Equals, v2@PureVar(id2))) if id1 > id2 =>
        acc.copy(pureFormula = acc.pureFormula - pc).swapPv(v1, v2)
      case (acc, pc@PureConstraint(PureVar(id1), Equals, PureVar(id2))) if id1 == id2 =>
        acc.copy(pureFormula = acc.pureFormula - pc)
      case (acc, _) => acc
    }
    val allPv = swappedForSmallerPv.pureVars()
    if (allPv.nonEmpty) {
      val maxPvValue = allPv.map { case PureVar(id) => id }.max
      swappedForSmallerPv.copy(nextAddr = maxPvValue + 1)
    } else
      swappedForSmallerPv
  }

  def simplify(state: State, maxWitness: Option[Int] = None): Option[State] = {
    implicit val zctx = getSolverCtx
    if (state.isSimplified) Some(state) else {
      // Drop useless constraints
      val state2 = state.copy(pureFormula = state.pureFormula.filter {
        case PureConstraint(v1, Equals, v2) if v1 == v2 => false
        case _ => true
      })
      // If no type possible for a pure var, state is not feasible
      val pvMap2: Map[PureVar, TypeSet] = state.typeConstraints
      if (pvMap2.exists(a => a._2.isEmpty(persist))) {
        return None
      }
      push()
      val messageTranslator = MessageTranslator(List(state2))

      //TODO: below should only be if z3 state solver is selected for types ======
//      val usedTypes = pvMap2.flatMap { case (_, tc) => tc.typeSet(ch) }.toSet

//      val (typesAreUniqe, typeMap) = mkTypeConstraints(usedTypes)
      val typesAreUniqe= mkBoolVal(true)
      val typeMap = Map[String,T]()
      val ast = mkAnd(typesAreUniqe, toAST(state2, typeMap, messageTranslator, maxWitness))

      if (maxWitness.isDefined) {
        println(s"State ${System.identityHashCode(state2)} encoding: ")
        println(ast.toString)
      }
      val simpleAst = solverSimplify(ast, state2, messageTranslator, maxWitness.isDefined)

      pop()
      // TODO: garbage collect constraint, if all purevar can't be reached from reg or stack var and state is satisfiable
      simpleAst.map(_ =>
        reduceStatePureVars(state2.setSimplified())
      )
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

  private def filterTypeConstraintsFromPf(pure: Set[PureConstraint]): Set[PureConstraint] = pure.filter {
    case PureConstraint(_, TypeComp, _) => false
    case _ => true
  }


  def canSubsume(s1: State, s2: State, maxLen: Option[Int] = None): Boolean = canSubsumeSlow(s1, s2, maxLen)

  /**
   * Consider rearrangments of pure vars that could result in subsumption
   *
   * @param s1 subsuming state
   * @param s2 contained state
   * @return
   */
  def canSubsumeSlow(s1: State, s2: State, maxLen: Option[Int] = None): Boolean = {
    // Check if stack sizes or locations are different
    if (s1.callStack.size != s2.callStack.size)
      return false

    val stackLocsMatch = (s1.callStack zip s2.callStack).forall {
      case (fr1, fr2) => fr1.methodLoc == fr2.methodLoc
    }
    if (!stackLocsMatch)
      return false

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
    val pv1 = s1.pureVars()
    val pv2 = s2.pureVars()
    val allPv = pv1.union(pv2).toList
    // map s2 to somethign where all pvs are strictly larger
    val maxID = if (allPv.nonEmpty) allPv.maxBy(_.id) else PureVar(5)

    // Swap all pureVars to pureVars above the max found in either state
    // This way swapping doesn't interfere with itself
    val (s2Above, pvToTemp) = allPv.foldLeft((s2.copy(nextAddr = maxID.id + 1), Map[PureVar, PureVar]())) {
      case ((st, nl), pv) =>
        val (freshPv, st2) = st.nextPv()
        (st2.swapPv(pv, freshPv), nl + (pv -> freshPv))
    }
    //    val normalCanSubsume = canSubsumeFast(s1,s2,maxLen)
    //TODO: extremely slow permutations there is probably a better way
    val perm = allPv.permutations.grouped(16)
    // TODO: add toList.par back in
    val out: Boolean = perm.exists{group => group.toList.exists { perm =>
      // Break early for combinations that don't match type constraints
//      val allCanMatch = (allPv zip perm).forall {
//        case (oldPv, newPv) =>
//          val optionals1TC = s1.typeConstraints.get(newPv)
//          val optionals2TC = s2.typeConstraints.get(oldPv)
//          (optionals1TC, optionals2TC) match {
//            case (Some(tc1), Some(tc2)) => tc1.contains(tc2)
//            case _ => true
//          }
//      }
//      if (allCanMatch) {

        val s2Swapped = (allPv zip perm).foldLeft(s2Above) {
          case (s, (oldPv, newPv)) => s.swapPv(pvToTemp(oldPv), newPv)
        }
        canSubsumeFast(s1, s2Swapped, maxLen)
//      } else false
    }
  }
    //    if (out != normalCanSubsume) {
    //      println()
    //    }
    out
  }

  def canSubsumeSolver(s1: State, s2: State, maxLen: Option[Int] = None): Boolean = {
    implicit var zctx = getSolverCtx

    // Currently, the stack is strictly the app call string
    // When adding more abstraction to the stack, this needs to be modified
    if (!stackCanSubsume(s1.callStack, s2.callStack)) {
      //      logger.info(s"Stack no subsume STATE1: $s1  STATE2: $s2")
      return false
    }

    // check if each pure var in the subsuming state represents a greater than or equal set of types
    push()


    val typeFun = createTypeFun()
    val allTypes = List(s1, s2).flatMap(_.typeConstraints.flatMap { case (_, v) => v.typeSet(ch) }).toSet
    val (uniqueType, typeMap) = mkTypeConstraints(allTypes)
    val state1Types = s1.typeConstraints.map { case (pv, v) =>
      mkTypeConstraintForAddrExpr(typeFun, typeMap, toAST(pv), v.typeSet(ch))
    }
    val state2Types = s2.typeConstraints.map { case (pv, v) =>
      mkTypeConstraintForAddrExpr(typeFun, typeMap, toAST(pv), v.typeSet(ch))
    }

    val notS1TypesEncoded = state1Types.foldLeft(mkBoolVal(false)) {
      (acc, v) => mkOr(acc, mkNot(v))
    }
    val s2TypesEncoded = state2Types.foldLeft(mkBoolVal(true)) {
      (acc, v) => mkAnd(acc, v)
    }

    val s1pf = filterTypeConstraintsFromPf(s1.pureFormula)
    val s2pf = filterTypeConstraintsFromPf(s2.pureFormula)

    // Pure formula that are not type constraints
    val negs1pure = s1pf.foldLeft(notS1TypesEncoded) {
      case (acc, constraint) => mkOr(mkNot(toAST(constraint)), acc)
    }

    val s2pure = s2pf.foldLeft(s2TypesEncoded) {
      case (acc, constraint) => mkAnd(toAST(constraint), acc)
    }

    // encode locals

    ???
    // encode heap constraints
    ???

    // encode trace abstraction
    val messageTranslator = MessageTranslator(List(s1, s2))
    val len = mkIntVar(s"len_")
    val traceFun = mkTraceFn("0")

    val phi = s2.traceAbstraction.foldLeft(s2pure) {
      case (acc, v) => mkAnd(acc, encodeTraceAbs(v, messageTranslator,
        traceFn = traceFun, len, absUID = Some("0")))
    }
    val negPhi = s1.traceAbstraction.foldLeft(negs1pure) {
      case (acc, v) => mkOr(acc, encodeTraceAbs(v, messageTranslator,
        traceFn = traceFun, len, absUID = Some("1"), negate = true))
    }

    val fp = mkAnd(
      negPhi,
      phi)
    // limit trace length for debug
    val f = maxLen match {
      case Some(v) =>
        // Print formula when debug mode enabled
        println(s"formula:\n $fp")
        mkAnd(mkLt(len, mkIntVal(v)), fp)
      case None => fp
    }
    // pureFormulaEnc._3 is assertion that all types are unique
    mkAssert(mkAnd(uniqueType, f))
    val ti = checkSAT()

    pop()

    !ti
  }

  /**
   * Check if formula s2 is entirely contained within s1.  Used to determine if subsumption is sound.
   *
   * @param s1 subsuming state
   * @param s2 contained state
   * @return false if there exists a trace in s2 that is not in s1 otherwise true
   */
  def canSubsumeFast(s1: State, s2: State, maxLen: Option[Int] = None): Boolean = {
    implicit var zctx = getSolverCtx

    // Currently, the stack is strictly the app call string
    // When adding more abstraction to the stack, this needs to be modified
    if (!stackCanSubsume(s1.callStack, s2.callStack)) {
      //      logger.info(s"Stack no subsume STATE1: $s1  STATE2: $s2")
      return false
    }
    if (!s1.heapConstraints.forall { case (k, v) => s2.heapConstraints.get(k).contains(v) }) {
      //      logger.info(s"Heap no subsume STATE1: $s1  STATE2: $s2")
      //      dbg(s1,s2)
      return false
    }
    // TODO: if tc says two things can't be equal then smt formula says they can't be equal

    // check if each pure var in the subsuming state represents a greater than or equal set of types
    if (encodeTypeConsteraints == SetInclusionTypeSolving) {
      val s1TypeMap = s1.typeConstraints
      val s2TypeMap = s2.typeConstraints
      val typesSubsume = s1TypeMap.forall { case (pv, ts) =>
        val opts2Val = s2TypeMap.get(pv)
        opts2Val.forall(ts.contains) //s1 type set contains s2 type set and pv must exist in s2
      }
      //        s1TypeMap.keySet.forall(pv => s2TypeMap.get(pv).exists(tset => s1TypeMap(pv).union(tset) == s1TypeMap(pv)))
      if (!typesSubsume) {
        return false
      }
    }

    push()

    val pureFormulaEnc = {

      // TODO: add type encoding here
      val (negTC1, tC2, uniqueType) = if (encodeTypeConsteraints == SolverTypeSolving) {
        val typeFun = createTypeFun()
        val allTypes = List(s1, s2).flatMap(_.typeConstraints.flatMap { case (_, v) => v.typeSet(ch) }).toSet
        val (uniqueType, typeMap) = mkTypeConstraints(allTypes)
        val state1Types = s1.typeConstraints.map { case (pv, v) =>
          mkTypeConstraintForAddrExpr(typeFun, typeMap, toAST(pv), v.typeSet(ch))
        }
        val state2Types = s2.typeConstraints.map { case (pv, v) =>
          mkTypeConstraintForAddrExpr(typeFun, typeMap, toAST(pv), v.typeSet(ch))
        }
        //        val state1Types = persist.pureVarTypeMap(s1).map{
        //          case (pv,ts) => mkTypeConstraint(typeFun, toAST(pv), ts)
        //        }
        //        val state2Types = persist.pureVarTypeMap(s2).map{
        //          case (pv,ts) => mkTypeConstraint(typeFun, toAST(pv), ts)
        //        }
        val notS1TypesEncoded = state1Types.foldLeft(mkBoolVal(false)) {
          (acc, v) => mkOr(acc, mkNot(v))
        }
        val s2TypesEncoded = state2Types.foldLeft(mkBoolVal(true)) {
          (acc, v) => mkAnd(acc, v)
        }
        (notS1TypesEncoded, s2TypesEncoded, uniqueType)
      } else (mkBoolVal(false), mkBoolVal(true), mkBoolVal(true))

      val s1pf = filterTypeConstraintsFromPf(s1.pureFormula)
      val s2pf = filterTypeConstraintsFromPf(s2.pureFormula)

      // Pure formula that are not type constraints
      val negs1pure = s1pf.foldLeft(negTC1) {
        case (acc, constraint) => mkOr(mkNot(toAST(constraint)), acc)
      }

      val s2pure = s2pf.foldLeft(tC2) {
        case (acc, constraint) => mkAnd(toAST(constraint), acc)
      }

      (negs1pure, s2pure, uniqueType)
    }

    val messageTranslator = MessageTranslator(List(s1, s2))
    val len = mkIntVar(s"len_")
    val traceFun = mkTraceFn("0")

    val phi = s2.traceAbstraction.foldLeft(pureFormulaEnc._2) {
      case (acc, v) => mkAnd(acc, encodeTraceAbs(v, messageTranslator,
        traceFn = traceFun, len, absUID = Some("0")))
    }
    val negPhi = s1.traceAbstraction.foldLeft(pureFormulaEnc._1) {
      case (acc, v) => mkOr(acc, encodeTraceAbs(v, messageTranslator,
        traceFn = traceFun, len, absUID = Some("1"), negate = true))
    }

    val fp = mkAnd(
      negPhi,
      phi)
    // limit trace length for debug
    val f = maxLen match {
      case Some(v) =>
        // Print formula when debug mode enabled
        println(s"formula:\n $fp")
        mkAnd(mkLt(len, mkIntVal(v)), fp)
      case None => fp
    }
    // pureFormulaEnc._3 is assertion that all types are unique
    mkAssert(mkAnd(pureFormulaEnc._3, f))
    val ti = checkSAT()
    if (ti && maxLen.isDefined) {
      println(s"===formula: $f")
      printDbgModel(messageTranslator, s1.traceAbstraction.union(s2.traceAbstraction), "")
    }
    pop()
    //    if(ti){
    //      logger.info(s"Pure or Trace no subsume STATE1: " +
    //        s"$s1  " +
    //        s"STATE2: $s2")
    //    }else{
    //      logger.info(s"Subsumed STATE1: " +
    //        s"${s1.toString.replace("\n"," ")}  " +
    //        s"STATE2: ${s2.toString.replace("\n"," ")}")
    //    }
    !ti
  }

  def encodeTrace(traceFN: T, trace: List[TMessage],
                  messageTranslator: MessageTranslator, valToT: Map[Int, T])(implicit zctx: C): T = {
    val assertEachMsg: List[T] = trace.zipWithIndex.flatMap {
      case (m, ind) =>
        val msgExpr = mkTraceConstraint(traceFN, mkIntVal(ind))
        val i = messageTranslator.iForMsg(m)
        val argConstraints: List[T] = m.args.zipWithIndex.map {
          case (TAddr(addr), ind) => mkEq(mkArgConstraint(mkArgFun(), mkIntVal(ind), msgExpr), valToT(addr))
          case (TNullVal, _) => ???
        }
        i.map(ii => {
          mkAnd(assertIAt(mkIntVal(ind), ii, messageTranslator, traceFN, negated = false, s => mkModelVar(s, "")),
            mkAnd(argConstraints)
          )
        })
    }
    assertEachMsg.foldLeft(mkBoolVal(true))((a, b) => mkAnd(a, b))
  }

  def witnessed(state: State): Boolean = {
    implicit val zctx = getSolverCtx
    if (state.heapConstraints.nonEmpty)
      return false
    if (state.callStack.nonEmpty)
      return false
    if (!traceInAbstraction(state, Nil))
      return false
    true
  }

  def traceInAbstraction(state: State, trace: List[TMessage], debug: Boolean = false)(implicit zctx: C): Boolean = {
    push()
    val messageTranslator = MessageTranslator(List(state))
    val assert = encodeTraceContained(state, trace, messageTranslator)
    mkAssert(assert)
    val sat = checkSAT()
    if (sat && debug) {
      println(s"model:\n $assert")
      printDbgModel(messageTranslator, state.traceAbstraction, "")
    }
    pop()
    sat
  }

  private def encodeTraceContained(state: State, trace: List[TMessage],
                                   messageTranslator: MessageTranslator)(implicit zctx: C): T = {
    val traceFn = mkTraceFn("")
    val len = mkIntVar(s"len_")
    val encodedAbs: Set[T] =
      state.traceAbstraction.map(encodeTraceAbs(_, messageTranslator, traceFn, len, Some("")))
    val pf = filterTypeConstraintsFromPf(state.pureFormula)
    val s2pure = pf.foldLeft(mkBoolVal(true)) {
      case (acc, constraint) => mkAnd(toAST(constraint), acc)
    }

    val distinctAddr: Map[Int, T] = (0 until 10).map(v => (v, mkAddrConst(v))).toMap
    val assertDistinct = mkDistinctT(distinctAddr.keySet.map(distinctAddr(_)))
    val encodedTrace = encodeTrace(traceFn, trace, messageTranslator, distinctAddr)
    mkAnd(mkEq(len, mkIntVal(trace.length)),
      mkAnd(encodedAbs.foldLeft(mkAnd(assertDistinct, s2pure))((a, b) => mkAnd(a, b)), encodedTrace)
    )
  }

}