package edu.colorado.plv.bounder.solver

import edu.colorado.plv.bounder.ir.TMessage
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState._
import edu.colorado.plv.bounder.symbolicexecutor.state._

trait Assumptions

class UnknownSMTResult(msg : String) extends Exception(msg)

/** SMT solver parameterized by its AST or expression type */
trait StateSolver[T] {
  // checking
  def checkSAT(): Boolean

  def checkSATWithAssumptions(assumes: List[String]): Boolean

  def getUNSATCore: String

  def push(): Unit

  def pop(): Unit

  // cleanup
  def dispose(): Unit

  // conversion from pure constraints to AST type of solver (T)

  // quantifiers
  /**
   * forall int condition is true
   *
   * @param cond
   */
  protected def mkForallInt(min: T, max: T, cond: T => T): T

  protected def mkExistsInt(min: T, max: T, cond: T => T): T

  // comparison operations
  protected def mkEq(lhs: T, rhs: T): T

  protected def mkNe(lhs: T, rhs: T): T

  protected def mkGt(lhs: T, rhs: T): T

  protected def mkLt(lhs: T, rhs: T): T

  protected def mkGe(lhs: T, rhs: T): T

  protected def mkLe(lhs: T, rhs: T): T

  // logical and arithmetic operations
  protected def mkImplies(t: T, t1: T): T

  protected def mkNot(o: T): T

  protected def mkAdd(lhs: T, rhs: T): T

  protected def mkSub(lhs: T, rhs: T): T

  protected def mkMul(lhs: T, rhs: T): T

  protected def mkDiv(lhs: T, rhs: T): T

  protected def mkRem(lhs: T, rhs: T): T

  protected def mkAnd(lhs: T, rhs: T): T

  protected def mkAnd(t: List[T]): T

  protected def mkOr(lhs: T, rhs: T): T

  protected def mkOr(t : List[T]):T

  protected def mkExactlyOneOf(l: List[T]): T

  // creation of variables, constants, assertions
  protected def mkIntVal(i: Int): T

  protected def mkBoolVal(b: Boolean): T

  protected def mkIntVar(s: String): T

  protected def mkFreshIntVar(s: String): T

  protected def mkBoolVar(s: String): T

  protected def mkObjVar(s: PureVar): T //Symbolic variable
  protected def mkModelVar(s: String, predUniqueID: String): T // model vars are scoped to trace abstraction
  protected def mkAssert(t: T): Unit

  protected def mkFieldFun(n: String): T

  protected def fieldEquals(fieldFun: T, t1: T, t2: T): T

  protected def freshSolverIfNeeded()
  protected def solverSimplify(t: T, state: State, messageTranslator:MessageTranslator, logDbg: Boolean = false): Option[T]

  protected def mkTypeConstraint(typeFun: T, addr: T, tc: TypeConstraint): T

  protected def createTypeFun(): T

  protected def mkEnum(name: String, types: List[String]): T

  protected def getEnumElement(enum: T, i: Int): T

  // function traceIndex -> msg
  protected def mkTraceFn(uid: String): T

  protected def mkFreshTraceFn(uid: String): T

  // function msg -> iname
  protected def mkINameFn(enum: T): T

  // function for argument i -> msg -> addr
  protected def mkArgFun(): T

  // function to test if addr is null
  // Uses uninterpreted function isNullFn : addr -> bool
  protected def mkIsNull(addr:T): T

  // Get enum value for I based on index
  protected def mkIName(enum: T, enumNum: Int): T

  // function from index to message (message is at index in trace)
  protected def mkTraceConstraint(traceFun: T, index: T): T

  // function msg -> funname
  protected def mkNameConstraint(nameFun: T, msg: T): T

  // function argumentindex -> msg -> argvalue
  protected def mkArgConstraint(argFun: T, argIndex: T, msg: T): T

  def printDbgModel(messageTranslator: MessageTranslator, traceabst: Set[AbstractTrace], lenUID: String): Unit

  def nullConst(v: PureExpr, op : CmpOp):T = {
    val tfun = createTypeFun()
    op match {
      case Equals => mkIsNull(toAST(v))
      case NotEquals => mkNot(mkIsNull(toAST(v)))
    }
  }

  def toAST(p: PureConstraint, typeFun: T): T = p match {
    // TODO: field constraints based on containing object constraints
    case PureConstraint(lhs: PureVar, TypeComp, rhs: TypeConstraint) =>
      mkTypeConstraint(typeFun, toAST(lhs), rhs)
    case PureConstraint(lhs, op, NullVal) => nullConst(lhs,op)
    case PureConstraint(NullVal, op, rhs) => nullConst(rhs,op)
    case PureConstraint(lhs, op, rhs) =>
      toAST(toAST(lhs), op, toAST(rhs))
    case _ => ???
  }

  def toAST(p: PureExpr): T = p match {
    case p: PureVar => mkObjVar(p)
    case NullVal => mkIntVal(0)
    case ClassType(t) => ??? //handled at a higher level
    case _ =>
      ???
  }

  def toAST(lhs: T, op: CmpOp, rhs: T): T = op match {
    case Equals => mkEq(lhs, rhs)
    case NotEquals =>
      mkNe(lhs, rhs)
    case _ =>
      ???
  }

  /**
   * Formula representing truth of "m is at position index in traceFn"
   * @param index index of the message (ArithExpr)
   * @param m
   * @param messageTranslator
   * @param traceFn : Int->Msg
   * @param absUID unique identifier for this scoped abstraction to separate model vars
   * @return
   */
  private def assertIAt(index: T, m: I,
                        messageTranslator: MessageTranslator,
                        traceFn: T, absUID: String,
                        negated:Boolean = false): T = {
    val msgExpr = mkTraceConstraint(traceFn, index)
    val nameFun = messageTranslator.nameFun
    val nameConstraint = mkEq(mkNameConstraint(nameFun, msgExpr), messageTranslator.enumFromI(m))
    val argConstraints = m.lsVars.zipWithIndex.flatMap {
      case (msgvar, ind) if msgvar != "_" =>
        Some(mkEq(mkArgConstraint(mkArgFun(), mkIntVal(ind), msgExpr), mkModelVar(msgvar, absUID)))
      case _ => None
    }

    // If we are asserting that a message is not at a location, the arg function cannot be negated due to skolemization
    // We only negate the name function
    if(negated)
      mkOr(mkNot(nameConstraint),mkOr(argConstraints.map(mkNot)))
    else
      mkAnd(nameConstraint, mkAnd(argConstraints))
  }

  private def encodePred(combinedPred: LifeState.LSPred, traceFn: T, len: T,
                         messageTranslator: MessageTranslator
                         , absUID: String, negate:Boolean = false): T = combinedPred match {
    case And(l1, l2) if !negate => mkAnd(encodePred(l1, traceFn, len, messageTranslator, absUID),
      encodePred(l2, traceFn, len, messageTranslator, absUID))
    case And(l1,l2) if negate => mkOr(
      encodePred(l1, traceFn,len,messageTranslator,absUID, negate = true),
      encodePred(l2, traceFn,len,messageTranslator,absUID, negate = true)
    )
    case Or(l1, l2) if !negate => mkOr(encodePred(l1, traceFn, len, messageTranslator, absUID),
      encodePred(l2, traceFn, len, messageTranslator, absUID))
    case Or(l1, l2) if negate => mkAnd(encodePred(l1, traceFn, len, messageTranslator, absUID, negate=true),
      encodePred(l2, traceFn, len, messageTranslator, absUID, negate=true))
//    case Not(m:I) if !negate =>
//      mkForallInt(mkIntVal(-1),len, i => assertIAt(i,m,messageTranslator,traceFn,absUID,true))
    case Not(l) =>
      encodePred(l, traceFn, len, messageTranslator, absUID, !negate)
    case m@I(_, _, _) if !negate=>
      mkExistsInt(mkIntVal(-1), len,
        i => assertIAt(i, m, messageTranslator, traceFn, absUID))
    case m:I if negate =>
      mkForallInt(mkIntVal(-1),len, i=>assertIAt(i,m,messageTranslator,traceFn,absUID,negated = true))
    case NI(m1, m2) if !negate =>
      // exists i such that omega[i] = m1 and forall j > i omega[j] != m2
      mkExistsInt(mkIntVal(-1), len, i => mkAnd(List(
        assertIAt(i, m1, messageTranslator, traceFn, absUID),
        mkForallInt(i, len, j => assertIAt(j, m2, messageTranslator, traceFn, absUID, negated = true))
      )))
    case NI(m1,m2) if negate =>
      // not NI(m1,m2) def= (not I(m1)) or NI(m2,m1)
      // encode with no negation
      encodePred(Or(Not(m1),NI(m2,m1)), traceFn, len, messageTranslator, absUID)
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
   * @param abs         abstraction of trace to encode for the solver
   * @param messageTranslator mapping from I preds to enum elements
   * @param traceFn     solver function from indices to trace messages
   * @param traceLen    total length of trace including arrow constraints
   * @param absUID      optional unique id for model variables to scope properly,
   *                    if none is provided, identity hash code of abs is used
   * @param negate      encode the assertion that traceFn is not in abs,
   *                    note that "mkNot(encodeTraceAbs(..." does not work due to skolomization
   * @return encoded trace abstraction
   */
  def encodeTraceAbs(abs: AbstractTrace, messageTranslator: MessageTranslator, traceFn: T, traceLen: T,
                     absUID: Option[String] = None, negate:Boolean = false): T = {
    val uniqueAbsId = absUID.getOrElse(System.identityHashCode(abs).toString)

    def iencarrow(len: T, abs: AbstractTrace, traceFn: T): T = abs match {
      case AbstractTrace(abs, ipreds, modelVars) =>
        val freshTraceFun = mkFreshTraceFn("arrowtf")
        val beforeIndEq =
          mkForallInt(mkIntVal(-1), len, i =>
            mkEq(mkTraceConstraint(traceFn, i), mkTraceConstraint(freshTraceFun, i)))
        val (suffixConstraint, endlen) = ipreds.foldLeft((beforeIndEq, len)) {
          case ((acc, ind), i) => (
            mkAnd(acc, assertIAt(ind, i, messageTranslator, freshTraceFun, uniqueAbsId)),
            mkAdd(ind, mkIntVal(1))
          )
        }
        val absEnc = ienc(endlen, abs,modelVars, freshTraceFun, negate)
        if(negate){
          mkAnd(absEnc, suffixConstraint)
        }else {
          mkAnd(absEnc, suffixConstraint)
        }
    }

    def ienc(sublen: T, f: LSPred, modelVars: Map[String,PureExpr], traceFn: T, negate:Boolean): T = {
      val modelConstraints:List[T] = modelVars.map{
        case (k,v:PureVar) => mkEq(mkModelVar(k, uniqueAbsId), mkObjVar(v))
        case _ => ???
      }.toList
//      val mc = if(negate) mkOr(modelConstraints.map(mkNot)) else mkAnd(modelConstraints)
      mkAnd(
        encodePred(f, traceFn, sublen, messageTranslator, uniqueAbsId, negate), mkAnd(modelConstraints))
    }

    iencarrow(traceLen, abs, traceFn)
  }

  protected def mkDistinct(pvList: Iterable[PureVar]): T
  protected def encodeTypeConsteraints:Boolean
  protected def persist: PersistantConstraints

  def toAST(heap: Map[HeapPtEdge, PureExpr]): T={
    // The only constraint we get from the heap is that domain elements must be distinct
    // e.g. a^.f -> b^ * c^.f->d^ means a^ != c^
    // alternatively a^.f ->b^ * c^.g->d^ does not mean a^!=c^
    val fields = heap.groupBy({ case (FieldPtEdge(_, fieldName), _) => fieldName })
    val heapAst = fields.foldLeft(mkBoolVal(true)) { (acc, v) =>
      val pvList = v._2.map { case (FieldPtEdge(pv, _), _) => pv }
      mkAnd(acc, mkDistinct(pvList))
    }
    heapAst
  }
  def toAST(state: State, messageTranslator: MessageTranslator, maxWitness: Option[Int] = None): T = {
    val pure = state.pureFormula
    // TODO: handle static fields
    // typeFun is a function from addresses to concrete types in the program
    val typeFun = createTypeFun()

    // pure formula are for asserting that two abstract addresses alias each other or not
    //  as well as asserting upper and lower bounds on concrete types associated with addresses
    val pure2 = if(encodeTypeConsteraints)pure else pure.filter{
      case PureConstraint(_,TypeComp, _) => false
      case _ => true
    }
    val pureAst = pure2.foldLeft(mkBoolVal(true))((acc, v) =>
      mkAnd(acc, toAST(v, typeFun))
    )

    val heapAst = toAST(state.heapConstraints)

    // Identity hash code of trace abstraction used when encoding a state so that quantifiers are independent
    val stateUniqueID = System.identityHashCode(state).toString

    val tracefun = mkTraceFn(stateUniqueID)
    val len = mkIntVar(s"len_$stateUniqueID") // there exists a finite size of the trace for this state
    val trace = state.traceAbstraction.foldLeft(mkBoolVal(true)) {
      case (acc, v) => mkAnd(acc, encodeTraceAbs(v, messageTranslator,
        traceFn = tracefun, traceLen = len))
    }
    val out = mkAnd(mkAnd(pureAst, heapAst), trace)
    maxWitness.foldLeft(out) { (acc, v) => mkAnd(mkLt(len, mkIntVal(v)), acc) }
  }

  case class MessageTranslator(states: List[State]){
    private val alli = allITraceAbs(states.flatMap(_.traceAbstraction).toSet, includeArrow = true)
    private val inamelist = "OTHEROTHEROTHER" :: alli.groupBy(_.identitySignature).keySet.toList
    private val iNameIntMap: Map[String, Int] = inamelist.zipWithIndex.toMap
    private val enum = mkEnum("inames", inamelist)

    def enumFromI(m:I):T = mkIName(enum, iNameIntMap(m.identitySignature))
    def getEnum:T = enum
    def nameFun:T = mkINameFn(enum)
    def iForMsg(m:TMessage):Option[I] = {
      val possibleI = alli.filter(ci =>
        ci.signatures.contains(m.fwkSig.get) && ci.mt== m.mType)
      assert(possibleI.size < 2)
      possibleI.headOption
    }
  }

  def typeSetForPureVar(v:PureVar, state:State):Set[String] = {
    state.pureFormula.foldLeft(persist.getSubtypesOf("java.lang.Object")) {
      case (acc, PureConstraint(p2, TypeComp, SubclassOf(c))) if v == p2 => acc.intersect(persist.getSubtypesOf(c))
      case (acc, PureConstraint(p2, TypeComp, ClassType(c))) if v == p2 => acc.intersect(Set(c))
      case (acc, PureConstraint(p2, TypeComp, SuperclassOf(c))) if v == p2 => acc.intersect(persist.getSupertypesOf(c))
      case (acc, _) => acc
    }
  }
  def pureVarTypeMap(state:State):Map[PureVar, Set[String]] = {
    val pvMap: Map[PureVar, Set[String]] = state.pureVars().map(p => (p,typeSetForPureVar(p,state))).toMap
    val pvMap2 = state.pureFormula.foldLeft(pvMap){
      case(acc, PureConstraint(p1:PureVar, Equals, p2:PureVar)) => {
        val newPvClasses = acc(p1).intersect(acc(p2))
        acc + (p1->newPvClasses) + (p2 -> newPvClasses)
      }
      case (acc,_) => acc
    }
    pvMap2
  }

  def simplify(state: State, maxWitness: Option[Int] = None): Option[State] = {
    if(state.isSimplified) Some(state) else {
      val state2 = state.copy(pureFormula = state.pureFormula.filter{
        case PureConstraint(v, TypeComp, SubclassOf("java.lang.Object")) => false
        case _ => true
      })
      if (!encodeTypeConsteraints) {
        val pvMap2 = pureVarTypeMap(state)
        if(pvMap2.exists(a => a._2.isEmpty)){
          return None
        }
      }
      push()
      val messageTranslator = MessageTranslator(List(state2))

      val ast = toAST(state2, messageTranslator, maxWitness)

      if (maxWitness.isDefined) {
        println(s"State ${System.identityHashCode(state2)} encoding: ")
        println(ast.toString)
      }
      val simpleAst = solverSimplify(ast, state2, messageTranslator, maxWitness.isDefined)

      pop()
      // TODO: garbage collect, if purevar can't be reached from reg or stack var, discard
      simpleAst.map(_ =>
        state2.setSimplified()
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

  /**
   * Check if formula s2 is entirely contained within s1.  Used to determine if subsumption is sound.
   *
   * @param s1 subsuming state
   * @param s2 contained state
   * @return false if there exists a trace in s2 that is not in s1 otherwise true
   */
  def canSubsume(s1: State, s2: State, maxLen: Option[Int] = None): Boolean = {
    // Currently, the stack is strictly the app call string
    // When adding more abstraction to the stack, this needs to be modified
    if(!stackCanSubsume(s1.callStack, s2.callStack))
      return false
    if(!s1.heapConstraints.forall { case (k, v) => s2.heapConstraints.get(k).contains(v) })
      return false
    // TODO: encode inequality of heap cells in smt formula?

    if(!encodeTypeConsteraints){
      val s1TypeMap = pureVarTypeMap(s1)
      val s2TypeMap = pureVarTypeMap(s2)
      val typesSubsume =
        s1TypeMap.keySet.forall(pv => s2TypeMap.get(pv).exists(tset => s1TypeMap(pv).union(tset) == s1TypeMap(pv)))
      if(!typesSubsume){
        return false
      }
    }

    push()

    val pureFormulaEnc = if(encodeTypeConsteraints) {
      val typeFun = createTypeFun()
      val negs1pure = s1.pureFormula.foldLeft(mkBoolVal(false)) {
        case (acc, constraint) => mkOr(mkNot(toAST(constraint, typeFun)), acc)
      }

      val s2pure = s2.pureFormula.foldLeft(mkBoolVal(true)) {
        case (acc, constraint) => mkAnd(toAST(constraint, typeFun), acc)
      }
      mkAnd(negs1pure, s2pure)
    }else mkBoolVal(false)

    val messageTranslator = MessageTranslator(List(s1,s2))
    val len = mkIntVar(s"len_")
    val traceFun = mkTraceFn("0")

    val phi = s2.traceAbstraction.foldLeft(mkBoolVal(true)) {
      case (acc, v) => mkAnd(acc, encodeTraceAbs(v, messageTranslator,
        traceFn = traceFun, len, absUID = Some("0")))
    }
    val negPhi = s1.traceAbstraction.foldLeft(mkBoolVal(false)) {
      case (acc, v) => mkOr(acc, encodeTraceAbs(v, messageTranslator,
        traceFn = traceFun, len, absUID = Some("1"),negate = true))
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
    mkAssert(mkOr(f,pureFormulaEnc))
    val ti = checkSAT()
    if (ti && maxLen.isDefined) {
      println(s"===formula: $f")
      printDbgModel(messageTranslator, s1.traceAbstraction.union(s2.traceAbstraction), "")
    }
    pop()
    !ti
  }

  def encodeTrace(traceFN:T, trace: List[TMessage], messageTranslator: MessageTranslator):T = {
    val assertEachMsg: List[T] = trace.zipWithIndex.flatMap {
      case(m,ind) =>
        val i = messageTranslator.iForMsg(m)
        i.map(assertIAt(mkIntVal(ind), _, messageTranslator, traceFN, ""))
    }
    assertEachMsg.foldLeft(mkBoolVal(true))( (a,b) => mkAnd(a,b))
  }
  def witnessed(state:State):Boolean = {
    if (state.heapConstraints.nonEmpty)
      return false
    if (state.callStack.nonEmpty)
      return false
    if (!traceInAbstraction(state, Nil))
      return false
    true
  }

  def traceInAbstraction(state:State, trace: List[TMessage]): Boolean ={
    push()
    val assert = encodeTraceContained(state, trace)
    mkAssert(assert)
    val sat = checkSAT()
    pop()
    sat
  }

  private def encodeTraceContained(state: State, trace: List[TMessage]):T = {
    val messageTranslator = MessageTranslator(List(state))
    val traceFn = mkTraceFn("")
    val len = mkIntVar(s"len_")
    val encodedAbs: Set[T] =
      state.traceAbstraction.map(encodeTraceAbs(_, messageTranslator, traceFn, len, Some("")))
    val encodedTrace = encodeTrace(traceFn, trace, messageTranslator)
    mkAnd(mkEq(len, mkIntVal(trace.length)),
      mkAnd(encodedAbs.foldLeft(mkBoolVal(true))((a, b) => mkAnd(a, b)), encodedTrace)
    )
  }
}