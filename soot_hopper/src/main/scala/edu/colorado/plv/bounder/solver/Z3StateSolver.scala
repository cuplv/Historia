package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{AST, ArithExpr, BoolExpr, BoolSort, Context, Expr, FuncDecl, IntSort, Model, Solver, Sort, Status}
import edu.colorado.hopper.solver.StateSolver
import edu.colorado.plv.bounder.lifestate.LifeState.{I, LSAtom, LSPred}
import edu.colorado.plv.bounder.symbolicexecutor.state.{PureVar, State, TraceAbstraction, TypeConstraint}

class Z3StateSolver(persistentConstraints: PersistantConstraints) extends StateSolver[AST] {
  val solver = persistentConstraints.getSolver
  val ctx = persistentConstraints.getCtx
  //val ctx : Context = new Context
  //val solver = {
  //  val solver = ctx.mkSolver
  //  val params = ctx.mkParams()
  //  params.add("timeout", 10000)
  //  solver.setParameters(params)
  //  solver
  //}
  override def checkSAT: Boolean = interpretSolverOutput(solver.check)

  override def checkSATWithAssumptions(assumes: List[String]): Boolean = ???

  override def getUNSATCore: String = ???

  override def push(): Unit = solver.push()

  override def pop(): Unit = solver.pop()

  override def dispose(): Unit = ???

  override protected def mkEq(lhs: AST, rhs: AST): AST =
    ctx.mkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr])

  override protected def mkNe(lhs: AST, rhs: AST): AST =
    ctx.mkNot(ctx.mkEq(lhs.asInstanceOf[Expr],rhs.asInstanceOf[Expr]))

  override protected def mkGt(lhs: AST, rhs: AST): AST = ???

  override protected def mkLt(lhs: AST, rhs: AST): AST =
    ctx.mkLt(lhs.asInstanceOf[ArithExpr],rhs.asInstanceOf[ArithExpr])

  override protected def mkGe(lhs: AST, rhs: AST): AST = ???

  override protected def mkLe(lhs: AST, rhs: AST): AST = ???

  override protected def mkNot(o: AST): AST = ctx.mkNot(o.asInstanceOf[BoolExpr])

  override protected def mkAdd(lhs: AST, rhs: AST): AST = ???

  override protected def mkSub(lhs: AST, rhs: AST): AST = ???

  override protected def mkMul(lhs: AST, rhs: AST): AST = ???

  override protected def mkDiv(lhs: AST, rhs: AST): AST = ???

  override protected def mkRem(lhs: AST, rhs: AST): AST = ???

  override protected def mkAnd(lhs:AST, rhs:AST):AST =
    mkAnd(List(lhs,rhs))
  override protected def mkAnd(t:List[AST]): AST = {
    val tb:Array[BoolExpr] = t.map(_.asInstanceOf[BoolExpr]).toArray
    ctx.mkAnd(tb:_*)
  }

  override protected def mkOr(lhs: AST, rhs: AST): AST =
    ctx.mkOr(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  /**
   * @param l list of boolean expressions
   * @return boolean expression that is true iff exactly one expression in l is true
   */
  override protected def mkExactlyOneOf(l:List[AST]): AST = {
    val oneorzero: List[ArithExpr] = l.map(lv =>
      ctx.mkITE(lv.asInstanceOf[BoolExpr],ctx.mkInt(1),ctx.mkInt(0)).asInstanceOf[ArithExpr])
    ctx.mkEq(ctx.mkAdd(oneorzero.toArray:_*), ctx.mkInt(1))
  }

  override protected def mkIntVal(i: Int): AST = ctx.mkInt(i)

  override protected def mkBoolVal(b: Boolean): AST = ctx.mkBool(b)

  override protected def mkIntVar(s: String): AST = ctx.mkIntConst(s)

  override protected def mkBoolVar(s: String): AST = ???

  override protected def mkAssert(t: AST): Unit = ???

  override protected def mkFieldFun(n: String): AST = {
    val fun: FuncDecl = ctx.mkFuncDecl(n, ctx.mkIntSort(), ctx.mkIntSort() )
    fun
  }
  override protected def fieldEquals(f: AST, t1 : AST, t2:AST): AST = {
    ctx.mkEq(f.asInstanceOf[FuncDecl].apply(t1.asInstanceOf[Expr]), t2.asInstanceOf[Expr])
  }

  private def interpretSolverOutput(status : Status) : Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      // this usually happens because of timeouts
      throw new IllegalStateException("Z3 decidability or timeout issue--got Status.UNKNOWN")
  }

  override protected def mkObjVar(s: PureVar): AST = ctx.mkIntConst("object_addr_" + s.id.toString)

  def printAbstSolution(model: Model,state:State) = state match{
    case State(_,_,_,traceabs) => {
      traceabs map {abs => {
        val uniqueID = System.identityHashCode(abs) + ""
        val len = mkIntVar(s"len_${uniqueID}").asInstanceOf[ArithExpr]
        println("=trace solution=")
        val traceLen: Int = model.eval(len,true).toString.toInt
        val alli = allI(abs)
        (0 until traceLen).map{ index =>{
          println(s"${index}: ")
          val msgati = alli.filter(ipred => {
            model.eval(
              mkINIConstraint(mkIFun(ipred),mkIntVal(index),
                ipred.lsVars.map(mkModelVar(_,uniqueID))).asInstanceOf[Expr],true)
              .toString == "true"
          }).mkString("***")
          println(msgati)
        }}
      }}
    }
  }

  //  private def printModelSolution()
  override protected def solverSimplify(t: AST,state:State, logDbg:Boolean): Option[AST] = {
    solver.add(t.asInstanceOf[BoolExpr])
    val status: Status = solver.check()
    status match{
      case Status.SATISFIABLE => {
        if (logDbg) {
          println(s"Model: ${solver.getModel}")
          printAbstSolution(solver.getModel(), state)
        }
        Some(t)
      }
      case Status.UNKNOWN => Some(t)
      case Status.UNSATISFIABLE => {
        if (logDbg) {
          println(s"Unsat core: ${solver.getUnsatCore.map(s=> s.toString).mkString(" AND \n")}")
        }
        None
      }
    }
  }

  override protected def mkTypeConstraint(typeFun: AST, addr:AST, tc: TypeConstraint): AST = {
    persistentConstraints.exprTypeConstraint(
      typeFun.asInstanceOf[FuncDecl].apply(addr.asInstanceOf[Expr]),tc)

  }
  override protected def createTypeFun():AST = {
    val intArgs: Array[Sort] = Array(ctx.mkIntSort())
    ctx.mkFuncDecl("addressToType", intArgs, persistentConstraints.tsort)
  }

  override protected def mkIFun(atom: I): AST = {
    // create(i,arg1,arg2 ...):Bool
    //  function for each msg - takes an index and a lst of arguments,
    //  returns true if it is at that position in the trace
    val arity = atom.lsVars.size
    val argtypes: Array[Sort] = (0 to arity).map(_=>ctx.mkIntSort()).toArray
    val sig = atom.identitySignature
    ctx.mkFuncDecl(sig, argtypes, ctx.mkBoolSort())
  }

  // Model vars have the pred identity hash code appended since they are unique to each pred
  // "_" means we don't care what the value is so just make arbitrary int
  override protected def mkModelVar(s: String, predUniqueID:String): AST =
    if (s != "_") {
      ctx.mkIntConst("model_var_" + s + "_" + predUniqueID)
    }else{
      mkFreshIntVar("_")
    }

  override protected def mkINIConstraint(ifun: AST,index:AST, modelVars: List[AST]): AST = {
    val args: Array[Expr] = (index::modelVars).map(_.asInstanceOf[Expr]).toArray
    ifun.asInstanceOf[FuncDecl].apply(args:_*)
  }

  override protected def mkFreshIntVar(s:String): AST =
    ctx.mkFreshConst(s, ctx.mkIntSort())

  /**
   * forall int condition is true
   *
   * @param cond
   */
  override protected def mkForallInt(min:AST, max:AST,cond: AST => AST): AST = {
    val j= ctx.mkFreshConst("j", ctx.mkIntSort()).asInstanceOf[ArithExpr]
    val range = mkAnd(List(mkLt(min,j), mkLt(j,max)))
    ctx.mkForall(Array(j), mkImplies(range,cond(j)).asInstanceOf[Expr]
      ,1,null,null,null,null)
  }

  override protected def mkImplies(t: AST, t1: AST): AST =
    ctx.mkImplies(t.asInstanceOf[BoolExpr], t1.asInstanceOf[BoolExpr])
}
