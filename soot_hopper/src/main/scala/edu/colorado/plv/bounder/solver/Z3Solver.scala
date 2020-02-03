package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{AST, BoolExpr, Context, Expr, Status}
import edu.colorado.hopper.solver.Solver

class Z3Solver extends Solver[AST] {
  val ctx : Context = new Context
  val solver = {
    val solver = ctx.mkSolver
    val params = ctx.mkParams()
    params.add("timeout", 10000)
    solver.setParameters(params)
    solver
  }
  override def checkSAT: Boolean = interpretSolverOutput(solver.check)

  override def checkSATWithAssumptions(assumes: List[String]): Boolean = ???

  override def getUNSATCore: String = ???

  override def push(): Unit = solver.push()

  override def pop(): Unit = solver.pop()

  override def dispose(): Unit = ???

  override protected def mkEq(lhs: AST, rhs: AST): AST =
    ctx.mkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr])

  override protected def mkNe(lhs: AST, rhs: AST): AST = ???

  override protected def mkGt(lhs: AST, rhs: AST): AST = ???

  override protected def mkLt(lhs: AST, rhs: AST): AST = ???

  override protected def mkGe(lhs: AST, rhs: AST): AST = ???

  override protected def mkLe(lhs: AST, rhs: AST): AST = ???

  override protected def mkNot(o: AST): AST = ???

  override protected def mkImplies(lhs: AST, rhs: AST): AST = ???

  override protected def mkAdd(lhs: AST, rhs: AST): AST = ???

  override protected def mkSub(lhs: AST, rhs: AST): AST = ???

  override protected def mkMul(lhs: AST, rhs: AST): AST = ???

  override protected def mkDiv(lhs: AST, rhs: AST): AST = ???

  override protected def mkRem(lhs: AST, rhs: AST): AST = ???

  override protected def mkAnd(lhs: AST, rhs: AST): AST =
    ctx.mkAnd(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  override protected def mkOr(lhs: AST, rhs: AST): AST = ???

  override protected def mkXor(lhs: AST, rhs: AST): AST = ???

  override protected def mkIntVal(i: Int): AST = ctx.mkInt(i)

  override protected def mkBoolVal(b: Boolean): AST = ctx.mkBool(b)

  override protected def mkIntVar(s: String): AST = ???

  override protected def mkBoolVar(s: String): AST = ???

  override protected def mkAssert(t: AST): Unit = ???

  private def interpretSolverOutput(status : Status) : Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      // this usually happens because of timeouts
      throw new IllegalStateException("Z3 decidability or timeout issue--got Status.UNKNOWN")
  }

  override protected def mkObjVar(s: String): AST =
    ctx.mkBoolConst(s + "_object")

  override protected def solverSimplify(t: AST): Option[AST] = {
    solver.add(t.asInstanceOf[BoolExpr])
    val status: Status = solver.check()
    status match{
      case Status.SATISFIABLE => Some(t)
      case Status.UNKNOWN => Some(t)
      case Status.UNSATISFIABLE => None
    }
  }
}
