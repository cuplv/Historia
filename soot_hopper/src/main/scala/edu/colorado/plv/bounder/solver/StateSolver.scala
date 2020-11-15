package edu.colorado.hopper.solver

import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSAbsBind, LSAtom, LSFalse, LSPred, LSTrue, NI, Not, Or}
import edu.colorado.plv.bounder.symbolicexecutor.state._

import scala.reflect.ClassTag

trait Assumptions

class UnknownSMTResult(msg : String) extends Exception(msg)

/** SMT solver parameterized by its AST or expression type */
trait StateSolver[T] {
  // checking
  def checkSAT : Boolean
  def checkSATWithAssumptions(assumes : List[String]) : Boolean

  def getUNSATCore : String
  def push() : Unit
  def pop() : Unit

  // cleanup
  def dispose() : Unit
  // conversion from pure constraints to AST type of solver (T)
//  def mkAssert(p : PureConstraint) : Unit = mkAssert(toAST(p))
//  def mkAssertWithAssumption(assume : String, p : PureConstraint) : Unit = mkAssert(mkImplies(mkBoolVar(assume), toAST(p)))

  // quantifiers
  /**
   * forall int condition is true
   * @param cond
   */
  protected def mkForallInt(min:T, max:T, cond:T=>T):T
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
  protected def mkXor(l:List[T]) : T

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
  protected def solverSimplify(t: T, logDbg:Boolean): Option[T]
  protected def mkTypeConstraint(typeFun: T, addr: T, tc: TypeConstraint):T
  protected def createTypeFun():T
  protected def mkIFun(atom:I):T
  protected def mkINIConstraint(fun: T, index: T, modelVars: List[T]):T

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
  def encodePred(combinedPred: LifeState.LSPred, uniqueID:String, len:T): T = combinedPred match {
    case And(l1, l2) => mkAnd(encodePred(l1, uniqueID,len), encodePred(l2, uniqueID,len))
    case LSAbsBind(k, v: PureVar) => mkEq(mkModelVar(k, uniqueID), mkObjVar(v))
    case Or(l1, l2) => mkOr(encodePred(l1, uniqueID,len), encodePred(l2, uniqueID,len))
    case Not(l) => mkNot(encodePred(l, uniqueID,len))
    case i@I(_,_, lsVars) => {
      val ifun = mkIFun(i)
      // exists i such that omega[i] = i
      mkINIConstraint(ifun,mkFreshIntVar("fromi"), lsVars.map(mkModelVar(_, uniqueID)))
    }
    case NI(m1,m2) => {
      // exists i such that omega[i] = m1 and forall j > i omega[j] != m2
      val i = mkFreshIntVar("i")
      mkAnd(List(
        mkLt(mkIntVal(-1),i),
        mkLt(i,len),
        mkINIConstraint(mkIFun(m1),i, m1.lsVars.map(mkModelVar(_,uniqueID))),
        mkForallInt(i,len, j => mkNot(mkINIConstraint(mkIFun(m2),j,m2.lsVars.map(mkModelVar(_,uniqueID)))))
      ))
    }
  }


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
  def allI(abs:TraceAbstraction):Set[I] = abs match{
    case AbsFormula(pred) => allI(pred)
    case AbsArrow(pred, _) => allI(pred)
    case AbsAnd(p1,p2) => allI(p1).union(allI(p2))
    case AbsEq(_,_) => Set()
  }
  def encodeTraceAbs(abs:TraceAbstraction):T = {
//    val initial_i = mkIntVar(s"initial_i_ + ${System.identityHashCode(abs)}")
    val initial_i = mkFreshIntVar("i")
    // A unique id for this element of the trace abstraction, used to distinguish model vars and
    val uniqueID = System.identityHashCode(abs).toString
    val len = mkIntVar(s"len_${uniqueID}") // there exists a finite size of the trace
    val alli = allI(abs)

    def ienc(i:T, abs: TraceAbstraction):T = abs match{
      case AbsFormula(f) =>
        encodePred(f, uniqueID, len)
      case AbsAnd(f1,f2) => mkAnd(ienc(i,f1), ienc(i,f2))
      case AbsArrow(abs, ipred) => {
        val j = mkFreshIntVar("j")
        val ipredf = mkIFun(ipred)
        val messageAt = mkINIConstraint(ipredf, j, ipred.lsVars.map(mkModelVar(_,uniqueID)))
        val recurs = ienc(j,abs)
        // all indices between this and the next arrow do not affect the LSPred
        val disj = mkForallInt(j,i,k =>{
          val listofconst:List[T] = alli.foldLeft(List[T]()){ (acc, i) =>
            mkNot(mkINIConstraint(mkIFun(i),k,i.lsVars.map(mkModelVar(_,uniqueID))))::acc}
          mkAnd(listofconst)
        })
        mkAnd(mkLt(j,i),
          mkAnd(mkAnd(mkLt(mkIntVal(-1),j), mkLt(i,len)),
            mkAnd(mkAnd(messageAt,recurs),disj)))
      }
      case AbsEq(mv,pv) => mkEq(mkModelVar(mv,uniqueID),mkObjVar(pv))
    }

    // Each position has unique message
    val uniqueIndex = mkForallInt(mkIntVal(-1), len, ind => mkXor(alli.map(ipred =>{
      mkINIConstraint(mkIFun(ipred),ind, ipred.lsVars.map(mkModelVar(_,uniqueID)))
    }).toList))

    mkAnd(ienc(initial_i, abs), uniqueIndex)
  }

  def toAST(state: State): T = {
    // TODO: make all variables in this encoding unique from other states so multiple states can be run at once
    // TODO: add ls constraints to state
    // TODO: mapping from ? constraints to bools that can be retrieved from the model after solving
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

    // Non static fields are modeled by a function from int to int.
    // A function is created for each fieldname.
    // For a constraint a^.f -> b^, it is asserted that field_f(a^) == b^
    val fields = heap.groupBy({ case (FieldPtEdge(_, fieldName), _) => fieldName })
    val heapAst = fields.foldLeft(mkBoolVal(true)) {
      case (acc, (field, heapConstraints)) => {
        val fieldFun = mkFieldFun(s"field_${field}")
        heapConstraints.foldLeft(acc) {
          case (acc, (FieldPtEdge(p, _), tgt)) =>
            mkAnd(acc, fieldEquals(fieldFun, toAST(p), toAST(tgt)))
        }
      }
    }
    val trace = state.traceAbstraction.foldLeft(mkBoolVal(true)) {
      case (acc,v) => mkAnd(acc, encodeTraceAbs(v))
    }
    mkAnd(mkAnd(pureAst, heapAst),trace)
  }

  def simplify(state: State, logDbg:Boolean = false): Option[State] = {
    push()
    val ast = toAST(state)
    if(logDbg) {
      println(s"State ${System.identityHashCode(state)} encoding: ")
      println(ast.toString)
    }
    val simpleAst = solverSimplify(ast, logDbg)

    pop()
    // TODO: garbage collect, if purevar can't be reached from reg or stack var, discard
    simpleAst.map(_ => state) //TODO: actually simplify?
  }
}