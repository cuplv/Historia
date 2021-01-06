package edu.colorado.plv.bounder.solver

import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSAbsBind, LSFalse, LSPred, LSTrue, NI, Not, Or}
import edu.colorado.plv.bounder.symbolicexecutor.state._

trait Assumptions

class UnknownSMTResult(msg : String) extends Exception(msg)

/** SMT solver parameterized by its AST or expression type */
trait StateSolver[T] {
  // checking
  def checkSAT() : Boolean
  def checkSATWithAssumptions(assumes : List[String]) : Boolean

  def getUNSATCore : String
  def push() : Unit
  def pop() : Unit

  // cleanup
  def dispose() : Unit
  // conversion from pure constraints to AST type of solver (T)

  // quantifiers
  /**
   * forall int condition is true
   * @param cond
   */
  protected def mkForallInt(min:T, max:T, cond:T=>T):T
  protected def mkExistsInt(min:T, max:T, cond:T=>T):T
  // comparison operations
  protected def mkEq(lhs : T, rhs : T) : T
  protected def mkNe(lhs : T, rhs : T) : T
  protected def mkGt(lhs : T, rhs : T) : T
  protected def mkLt(lhs : T, rhs : T) : T
  protected def mkGe(lhs : T, rhs : T) : T
  protected def mkLe(lhs : T, rhs : T) : T

  // logical and arithmetic operations
  protected def mkImplies(t: T, t1: T):T
  protected def mkNot(o : T) : T
  protected def mkAdd(lhs : T, rhs : T) : T
  protected def mkSub(lhs : T, rhs : T) : T
  protected def mkMul(lhs : T, rhs : T) : T
  protected def mkDiv(lhs : T, rhs : T) : T
  protected def mkRem(lhs : T, rhs : T) : T
  protected def mkAnd(lhs:T, rhs:T):T
  protected def mkAnd(t : List[T]) : T
  protected def mkOr(lhs : T, rhs : T) : T
  protected def mkExactlyOneOf(l:List[T]) : T

  // creation of variables, constants, assertions
  protected def mkIntVal(i : Int) : T
  protected def mkBoolVal(b : Boolean) : T
  protected def mkIntVar(s : String) : T
  protected def mkFreshIntVar(s:String):T
  protected def mkBoolVar(s : String) : T
  protected def mkObjVar(s:PureVar) : T //Symbolic variable
  protected def mkModelVar(s:String, predUniqueID:String):T // model vars are scoped to trace abstraction
  protected def mkAssert(t : T) : Unit
  protected def mkFieldFun(n: String): T
  protected def fieldEquals(fieldFun: T, t1 : T, t2: T):T
  protected def solverSimplify(t: T, state:State, msgname:T, logDbg:Boolean = false): Option[T]
  protected def mkTypeConstraint(typeFun: T, addr: T, tc: TypeConstraint):T
  protected def createTypeFun():T
  protected def mkEnum(name:String, types:List[String]):T
  protected def getEnumElement(enum:T, i:Int):T
  // function traceIndex -> msg
  protected def mkTraceFn(uid:String):T
  protected def mkFreshTraceFn(uid:String):T
  // function msg -> iname
  protected def mkINameFn(enum:T):T
  // function for argument i -> msg -> value
  protected def mkArgFun():T
  // Get enum value for I based on index
  protected def mkIName(enum:T, enumNum:Int):T
  // function from index to message (message is at index in trace)
  protected def mkTraceConstraint(traceFun:T, index:T):T
  // function msg -> funname
  protected def mkNameConstraint(nameFun:T, msg:T):T
  // function argumentindex -> msg -> argvalue
  protected def mkArgConstraint(argFun:T, argIndex:T, msg:T):T
  def printDbgModel(msgname: T, traceabst: Set[TraceAbstractionArrow], lenUID: String):Unit

  def toAST(p : PureConstraint, typeFun: T) : T = p match {
      // TODO: field constraints based on containing object constraints
    case PureConstraint(lhs: PureVar, TypeComp, rhs:TypeConstraint) =>
      mkTypeConstraint(typeFun, toAST(lhs), rhs)
    case PureConstraint(lhs, op, rhs) =>
      toAST(toAST(lhs), op, toAST(rhs))
    case _ => ???
  }
  def toAST(p : PureExpr) : T = p match {
    case p:PureVar => mkObjVar(p)
    case NullVal => mkIntVal(0)
    case ClassType(t) => ??? //handled at a higher level
    case _ =>
      ???
  }
  def toAST(lhs : T, op : CmpOp, rhs : T) : T = op match {
    case Equals => mkEq(lhs,rhs)
    case NotEquals => mkNe(lhs, rhs)
    case _ =>
      ???
  }
  private def assertIAt(index:T, m:I, ienume:T, enumMap: Map[String,Int], traceFn:T, absUID:String):T = {
//    val traceFun = mkTraceFn(traceUID)
    val msgExpr = mkTraceConstraint(traceFn, index)
    val nameFun = mkINameFn(ienume)
    mkAnd(mkEq(mkNameConstraint(nameFun,msgExpr), mkIName(ienume,enumMap(m.identitySignature))),
      mkAnd(m.lsVars.zipWithIndex.map{case (msgvar, ind) =>
        mkEq(mkArgConstraint(mkArgFun(), mkIntVal(ind), msgExpr),mkModelVar(msgvar, absUID) )}))
  }
  def encodePred(combinedPred: LifeState.LSPred, traceFn:T, len:T,
                 ienume:T, enumMap:Map[String,Int], absUID:String): T = combinedPred match {
    case And(l1, l2) => mkAnd(encodePred(l1, traceFn,len, ienume, enumMap,absUID),
      encodePred(l2, traceFn,len,ienume, enumMap,absUID))
    case LSAbsBind(k, v: PureVar) => mkEq(mkModelVar(k, absUID), mkObjVar(v))
    case Or(l1, l2) => mkOr(encodePred(l1, traceFn,len,ienume,enumMap,absUID),
      encodePred(l2, traceFn,len,ienume, enumMap,absUID))
    case Not(l) => mkNot(encodePred(l, traceFn,len, ienume, enumMap,absUID))
    case m@I(_,_, _) =>
      mkExistsInt(mkIntVal(-1),len,
      i => mkAnd(List(
        assertIAt(i, m, ienume, enumMap, traceFn, absUID)
      )))
    case NI(m1,m2) =>
      // exists i such that omega[i] = m1 and forall j > i omega[j] != m2
      mkExistsInt(mkIntVal(-1), len, i => mkAnd(List(
        assertIAt(i, m1, ienume, enumMap, traceFn, absUID),
        mkForallInt(i,len, j => mkNot(assertIAt(j, m2, ienume, enumMap, traceFn, absUID)))
      )))
  }


  def allITraceAbs(traceAbstractionSet: Set[TraceAbstractionArrow], includeArrow:Boolean=false):Set[I] =
    traceAbstractionSet.flatMap(a => allI(a,includeArrow))
  def allI(pred:LSPred):Set[I] = pred match{
    case i@I(_,_,_) => Set(i)
    case NI(i1,i2) => Set(i1,i2)
    case And(l1,l2) => allI(l1).union(allI(l2))
    case Or(l1,l2) => allI(l1).union(allI(l2))
    case Not(l) => allI(l)
    case LSTrue => Set()
    case LSFalse => Set()
    case LSAbsBind(_,_) => Set()
  }
  def allI(abs:AbstractTrace):Set[I] = abs match{
    case AbsFormula(pred) => allI(pred)
    case AbsAnd(p1,p2) => allI(p1).union(allI(p2))
    case AbsEq(_,_) => Set()
  }
  def allI(abs:TraceAbstractionArrow, includeArrow:Boolean):Set[I] = abs match{
    case AbsArrow(pred, i2) =>
      if(includeArrow)
        allI(pred) ++ i2
      else
        allI(pred)
  }

  /**
   *
   * @param abs abstraction of trace to encode for the solver
   * @param enum solver enumeration type for message names
   * @param iNameIntMap Mapping from message names to integers in the enum (this includes cb/cbret etc)
   * @param traceFn solver function from indices to trace messages
   * @param traceLen total length of trace including arrow constraints
   * @param absUID optional unique id for model variables to scope properly,
   *               if none is provided, identity hash code of abs is used
   * @return encoded trace abstraction
   */
  def encodeTraceAbs(abs:TraceAbstractionArrow, enum:T, iNameIntMap:Map[String,Int], traceFn: T, traceLen:T,
                     absUID: Option[String] = None): T = {
    //TODO: replace tracelen and uniquetraceid with case class that can create new tracefn for each arrow
    // A unique id for variables scoped to the trace abstraction
    val uniqueAbsId = absUID.getOrElse(System.identityHashCode(abs).toString)

    def iencarrow(len:T, abs:TraceAbstractionArrow, traceFn:T):T = abs match{
      case AbsArrow(abs, ipreds) =>
        val freshTraceFun = mkFreshTraceFn("arrowtf")
        val beforeIndEq =
          mkForallInt(mkIntVal(-1), len, i =>
            mkEq(mkTraceConstraint(traceFn,i), mkTraceConstraint(freshTraceFun,i)))
        val (suffixConstraint,endlen) = ipreds.foldLeft((beforeIndEq,len)) {
          case ((acc,ind),i) => (
            mkAnd(acc, assertIAt(ind, i, enum, iNameIntMap, freshTraceFun, uniqueAbsId)),
            mkAdd(ind, mkIntVal(1))
          )
        }
        mkAnd(ienc(endlen, abs, freshTraceFun), suffixConstraint)
    }
    def ienc(sublen:T, abs: AbstractTrace, traceFn:T):T = abs match{
      case AbsFormula(f) =>
        encodePred(f, traceFn, sublen, enum,iNameIntMap, uniqueAbsId)
      case AbsAnd(f1,f2) => mkAnd(ienc(sublen,f1,traceFn), ienc(sublen,f2,traceFn))
//      case AbsArrow(abs, ipred) =>
//        // w |= \theta, \phi |> m^   iff   w;\theta(m^) |= \theta, \phi
//        // Use fresh trace function to avoid arrow constraint contradiction
//        // e.g. NI(a,b)|>a && NI(c,d)|>d should be true
//        val freshTraceFun = mkFreshTraceFn("arrowtf")
//        val lastElem = mkAdd(i,mkIntVal(1))
//        val newk = (nexti:T) =>
//          mkAnd(List(k(mkAdd(nexti, mkIntVal(1))),
//            assertIAt(nexti, ipred, enum, iNameIntMap, freshTraceFun, uniqueAbsId),
//            mkForallInt(mkIntVal(-1), nexti, j => mkEq(
//              mkTraceConstraint(freshTraceFun,j),
//              mkTraceConstraint(traceFn,j)))
//          ))
//        ienc(lastElem, abs, freshTraceFun, newk)
      case AbsEq(mv,pv) => mkEq(mkModelVar(mv,uniqueAbsId),mkObjVar(pv))
    }
    iencarrow(traceLen, abs,traceFn)
  }

  protected def mkDistinct(pvList: Iterable[PureVar]): T

  def toAST(state: State, enum:T, iNameIntMap:Map[String,Int], maxWitness:Option[Int] = None): T = {
    // TODO: make all variables in this encoding unique from other states so multiple states can be run at once
    val heap = state.heapConstraints
    val pure = state.pureFormula
    // TODO: handle static fields
    // typeFun is a function from addresses to concrete types in the program
    val typeFun = createTypeFun()

    // pure formula are for asserting that two abstract addresses alias each other or not
    //  as well as asserting upper and lower bounds on concrete types associated with addresses
    val pureAst = pure.foldLeft(mkBoolVal(true))((acc, v) =>
      mkAnd(acc, toAST(v, typeFun))
    )

    // The only constraint we get from the heap is that domain elements must be distinct
    // e.g. a^.f -> b^ * c^.f->d^ means a^ != c^
    // alternatively a^.f ->b^ * c^.g->d^ does not mean a^!=c^
    val fields = heap.groupBy({ case (FieldPtEdge(_, fieldName), _) => fieldName })
    val heapAst = fields.foldLeft(mkBoolVal(true)){(acc,v) =>
      val pvList = v._2.map{case (FieldPtEdge(pv, _), _) => pv}
      mkAnd(acc, mkDistinct(pvList))
    }

    // Identity hash code of trace abstraction used when encoding a state so that quantifiers are independent
    val stateUniqueID = System.identityHashCode(state).toString

    val tracefun = mkTraceFn(stateUniqueID)
    val len = mkIntVar(s"len_$stateUniqueID") // there exists a finite size of the trace for this state
    val trace = state.traceAbstraction.foldLeft(mkBoolVal(true)) {
      case (acc,v) => mkAnd(acc, encodeTraceAbs(v, enum, iNameIntMap,
        traceFn = tracefun,traceLen = len))
    }
    val out = mkAnd(mkAnd(pureAst, heapAst),trace)
    maxWitness.foldLeft(out){(acc,v) => mkAnd(mkLt(len, mkIntVal(v)), acc)}
  }

  def enumFromStates(states: List[State]):(T,Map[String,Int]) = {
    val alli = allITraceAbs(states.flatMap(_.traceAbstraction).toSet,includeArrow = true)
    val inamelist = "OTHEROTHEROTHER":: alli.groupBy(_.identitySignature).keySet.toList
    val iNameIntMap: Map[String, Int] = inamelist.zipWithIndex.toMap
    (mkEnum("inames",inamelist), iNameIntMap)
  }
  def simplify(state: State, maxWitness:Option[Int] = None): Option[State] = {
    push()
    val (ienum,iNameIntMap) = enumFromStates(List(state))
    val ast = toAST(state,ienum, iNameIntMap, maxWitness)

    if(maxWitness.isDefined) {
      println(s"State ${System.identityHashCode(state)} encoding: ")
      println(ast.toString)
    }
    val simpleAst = solverSimplify(ast,state,ienum, maxWitness.isDefined)

    pop()
    // TODO: garbage collect, if purevar can't be reached from reg or stack var, discard
    simpleAst.map(_ => state) //TODO: actually simplify?
  }

  // TODO: call stack is currently just a list of stack frames, this needs to be updated when top is added
  def stackCanSubsume(cs1: List[CallStackFrame], cs2: List[CallStackFrame]):Boolean = (cs1, cs2) match {
    case (CallStackFrame(ml1, _, locals1)::t1, CallStackFrame(ml2, _, locals2)::t2) if ml1 == ml2 =>
      locals1.forall{case (k,v) => locals2.get(k).contains(v)} &&
        stackCanSubsume(t1,t2)
    case (Nil,Nil) => true
    case _ => false
  }

  /**
   * Check if formula s1 is entirely contained within s2.  Used to determine if subsumption is sound.
   *
   * @param s1 contained state
   * @param s2 subsuming state
   * @return
   */
  def canSubsume(s1:State, s2:State, maxLen: Option[Int] = None):Boolean = {
    // Currently, the stack is strictly the app call string
    // When adding more abstraction to the stack, this needs to be modified
    // TODO: check if pure vars are canonacalized
    push()
    val si = stackCanSubsume(s1.callStack, s2.callStack)
    val hi = s1.heapConstraints.forall{case (k,v) => s2.heapConstraints.get(k).contains(v)}
    val pvi = s1.pureFormula.forall{
      case p@PureConstraint(_, Equals, _) =>
        s2.pureFormula.contains(p)
      case p@PureConstraint(_, NotEquals, _) => s2.pureFormula.contains(p)
      case _ => ??? //TODO: type comparison
    }
    val (iEnum,idMap) = enumFromStates(List(s1,s2))
    val len = mkIntVar(s"len_")
    val traceFun = mkTraceFn("0")
    val phi = (s:State) => (lenp1:T) => s.traceAbstraction.foldLeft(mkBoolVal(true)) {
      case (acc,v) => mkAnd(acc, encodeTraceAbs(v, iEnum, idMap,
        traceFn=traceFun ,lenp1, Some("0")))
    }
    val fp = mkExistsInt(mkIntVal(-1), len, l => mkNot(mkImplies(
      phi(s2)(l),
      phi(s1)(l))))
    // limit trace length for debug
    val f = maxLen match {
      case Some(v) =>
        // Print formula when debug mode enabled
        println(s"formula:\n $fp")
        mkAnd(mkLt(len, mkIntVal(v)), fp)
      case None => fp
    }
    mkAssert(f)
    val ti = checkSAT()
    if (ti) {
      println(s"===formula: $f")
      printDbgModel(iEnum, s1.traceAbstraction.union(s2.traceAbstraction), "")
    }
    pop()

    si && hi && pvi && (!ti)
  }

}