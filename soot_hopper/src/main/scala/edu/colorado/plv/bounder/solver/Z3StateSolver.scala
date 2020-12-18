package edu.colorado.plv.bounder.solver

import com.microsoft.z3._
import edu.colorado.plv.bounder.symbolicexecutor.state.{PureVar, State, TraceAbstraction, TypeConstraint}

class Z3StateSolver(persistentConstraints: PersistantConstraints) extends StateSolver[AST] {
  val solver: Solver = persistentConstraints.getSolver
  val ctx: Context = persistentConstraints.getCtx

  override def checkSAT(): Boolean = interpretSolverOutput(solver.check)

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

  override protected def mkAdd(lhs: AST, rhs: AST): AST = {
    ctx.mkAdd(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])
  }

  override protected def mkSub(lhs: AST, rhs: AST): AST =
    ctx.mkSub(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

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

  override protected def mkBoolVal(boolVal: Boolean): AST = ctx.mkBool(boolVal)

  override protected def mkIntVar(s: String): AST = ctx.mkIntConst(s)

  override protected def mkBoolVar(s: String): AST = ???

  override protected def mkAssert(t: AST): Unit = solver.add(t.asInstanceOf[BoolExpr])

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

  override def printDbgModel(msgName: AST, traceAbstraction: Set[TraceAbstraction], lenUID: String): Unit = {
    printAbstSolution(solver.getModel, msgName.asInstanceOf[EnumSort], traceAbstraction, lenUID)
  }

  def printAbstSolution(model: Model, msgName: EnumSort, traceAbstraction: Set[TraceAbstraction],
                        lenUID: String) {
    println(s"===model: $model")
    traceAbstraction map { abs => {
      val uniqueID = System.identityHashCode(abs) + ""
      val len = mkIntVar(s"len_$lenUID").asInstanceOf[ArithExpr]
      println("=trace solution=")
      val traceLen: Int = model.eval(len, true).toString.toInt
      val traceFun = mkTraceFn(uniqueID).asInstanceOf[FuncDecl]
      val nameFun = mkINameFn(msgName).asInstanceOf[FuncDecl]
      val argFun = mkArgFun().asInstanceOf[FuncDecl]
      (0 until traceLen).map ( index => {
        println(s"$index: ")
        val msgati = model.eval(traceFun.apply(ctx.mkInt(index)), true)
        println(s"${model.eval(nameFun.apply(msgati), true)} " +
          s"args: ${model.eval(argFun.apply(ctx.mkInt(0), msgati), true)}")
      })
    }
    }
  }

  //  private def printModelSolution()
  override protected def solverSimplify(t: AST,state:State, msgname:AST, logDbg:Boolean): Option[AST] = {
    solver.add(t.asInstanceOf[BoolExpr])
    val status: Status = solver.check()
    status match{
      case Status.SATISFIABLE =>
        if (logDbg) {
          println(s"Model: ${solver.getModel}")
          printAbstSolution(solver.getModel(),msgname.asInstanceOf[EnumSort],
            state.traceAbstraction,
            System.identityHashCode(state).toString)
        }
        Some(t)
      case Status.UNKNOWN => Some(t)
      case Status.UNSATISFIABLE =>
        if (logDbg) {
          println(s"Unsat core: ${solver.getUnsatCore.map(s=> s.toString).mkString(" AND \n")}")
        }
        None
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

  // Model vars have the pred identity hash code appended since they are unique to each pred
  // "_" means we don't care what the value is so just make arbitrary int
  override protected def mkModelVar(s: String, predUniqueID:String): AST =
    if (s != "_") {
      ctx.mkIntConst("model_var_" + s + "_" + predUniqueID)
    }else{
      mkFreshIntVar("_")
    }

  override protected def mkFreshIntVar(s:String): AST =
    ctx.mkFreshConst(s, ctx.mkIntSort())

  /**
   * forall int in (min,max) condition is true
   * @param cond function from const to boolean expression
   */
  override protected def mkForallInt(min:AST, max:AST,cond: AST => AST): AST = {
    val j= ctx.mkFreshConst("j", ctx.mkIntSort()).asInstanceOf[ArithExpr]
    val range = mkAnd(List(mkLt(min,j), mkLt(j,max)))
    ctx.mkForall(Array(j), mkImplies(range,cond(j)).asInstanceOf[Expr]
      ,1,null,null,null,null)
  }

  /**
   * there exists an int in (min,max) such that condition is true
   * @param cond function from const to boolean expression
   * @return
   */
  protected def mkExistsInt(min:AST, max:AST, cond:AST=>AST):AST = {
    val j= ctx.mkFreshConst("i", ctx.mkIntSort()).asInstanceOf[ArithExpr]
    val range = mkAnd(List(mkLt(min,j), mkLt(j,max)))
    ctx.mkExists(Array(j), mkAnd(range,cond(j)).asInstanceOf[Expr]
      ,1,null,null,null,null)
  }

  override protected def mkImplies(t: AST, t1: AST): AST =
    ctx.mkImplies(t.asInstanceOf[BoolExpr], t1.asInstanceOf[BoolExpr])

  override protected def mkTraceFn(uid: String): AST =
    ctx.mkFuncDecl(s"tracefn_$uid", ctx.mkIntSort, ctx.mkUninterpretedSort("Msg"))

  override protected def mkFreshTraceFn(uid: String): AST =
    ctx.mkFreshFuncDecl(s"tracefn_$uid", Array(ctx.mkIntSort), ctx.mkUninterpretedSort("Msg"))

  override protected def mkINameFn(enum:AST): AST =
    ctx.mkFuncDecl(s"namefn_", ctx.mkUninterpretedSort("Msg"), enum.asInstanceOf[EnumSort])

  override protected def mkArgFun(): AST =
    ctx.mkFuncDecl(s"argfun_", Array(ctx.mkIntSort(), ctx.mkUninterpretedSort("Msg")), ctx.mkIntSort)

  override protected def mkIName(enum:AST, enumNum:Int): AST = enum.asInstanceOf[EnumSort].getConst(enumNum)

  override protected def mkEnum(name: String, types: List[String]): AST =
    ctx.mkEnumSort(name, types.toArray:_*)

  override protected def getEnumElement(enum:AST, i: Int): AST = enum.asInstanceOf[EnumSort].getConst(i)

  override protected def mkTraceConstraint(traceFun: AST, index: AST): AST =
    traceFun.asInstanceOf[FuncDecl].apply(index.asInstanceOf[ArithExpr])

  override protected def mkNameConstraint(nameFun: AST, msg: AST): AST =
    nameFun.asInstanceOf[FuncDecl].apply(msg.asInstanceOf[Expr])

  override protected def mkArgConstraint(argFun: AST, argIndex: AST, msg: AST): AST =
    argFun.asInstanceOf[FuncDecl].apply(argIndex.asInstanceOf[Expr], msg.asInstanceOf[Expr])

  override protected def mkDistinct(pvList: Iterable[PureVar]): AST = {
    ctx.mkDistinct(pvList.map(a => mkObjVar(a).asInstanceOf[Expr]).toArray:_*)
  }
}
