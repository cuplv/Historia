package edu.colorado.plv.bounder.solver

import com.microsoft.z3._
import edu.colorado.plv.bounder.lifestate.LifeState.{LSAnyVal, LSVar}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, PureVar, State, TypeConstraint}

import scala.collection.immutable

case class Z3SolverCtx(ctx: Context, solver:Solver) extends SolverCtx
class Z3StateSolver(persistentConstraints: ClassHierarchyConstraints) extends StateSolver[AST,Z3SolverCtx] {

  val ctx = new Context()
  val solver = ctx.mkSolver()
  override def getSolverCtx: Z3SolverCtx = {
    Z3SolverCtx(ctx, solver)
  }

  private def addrSort(implicit zctx:Z3SolverCtx) = zctx.ctx.mkUninterpretedSort("Addr")

  override def checkSAT()(implicit zctx:Z3SolverCtx): Boolean = interpretSolverOutput(zctx.solver.check)

  override def push()(implicit zctx:Z3SolverCtx): Unit = zctx.solver.push()

  override def pop()(implicit zctx:Z3SolverCtx): Unit = zctx.solver.pop()

  override protected def mkEq(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkEq(lhs.asInstanceOf[Expr], rhs.asInstanceOf[Expr])

  override protected def mkNe(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkNot(zctx.ctx.mkEq(lhs.asInstanceOf[Expr],rhs.asInstanceOf[Expr]))

  override protected def mkGt(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST = ???

  override protected def mkLt(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkLt(lhs.asInstanceOf[ArithExpr],rhs.asInstanceOf[ArithExpr])

  override protected def mkGe(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST = ???

  override protected def mkLe(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST = ???

  override protected def mkNot(o: AST)(implicit zctx:Z3SolverCtx): AST = zctx.ctx.mkNot(o.asInstanceOf[BoolExpr])

  override protected def mkAdd(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkAdd(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])
  }

  override protected def mkSub(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkSub(lhs.asInstanceOf[ArithExpr], rhs.asInstanceOf[ArithExpr])

  override protected def mkMul(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST = ???

  override protected def mkDiv(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST = ???

  override protected def mkRem(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST = ???

  override protected def mkAnd(lhs:AST, rhs:AST)(implicit zctx:Z3SolverCtx):AST =
    mkAnd(List(lhs,rhs))
  override protected def mkAnd(t:List[AST])(implicit zctx:Z3SolverCtx): AST = {
    val tb:Array[BoolExpr] = t.map(_.asInstanceOf[BoolExpr]).toArray
    zctx.ctx.mkAnd(tb:_*)
  }

  override protected def mkOr(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkOr(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  override protected def mkOr(t: List[AST])(implicit zctx:Z3SolverCtx): AST = {
    val tb: Array[BoolExpr] = t.map(_.asInstanceOf[BoolExpr]).toArray
    zctx.ctx.mkOr(tb:_*)
  }

  /**
   * @param l list of boolean expressions
   * @return boolean expression that is true iff exactly one expression in l is true
   */
  override protected def mkExactlyOneOf(l:List[AST])(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx
    val oneorzero: List[ArithExpr] = l.map(lv =>
      ctx.mkITE(lv.asInstanceOf[BoolExpr],ctx.mkInt(1),ctx.mkInt(0)).asInstanceOf[ArithExpr])
    ctx.mkEq(ctx.mkAdd(oneorzero.toArray:_*), ctx.mkInt(1))
  }

  override protected def mkIntVal(i: Int)(implicit zctx:Z3SolverCtx): AST = zctx.ctx.mkInt(i)

  override protected def mkBoolVal(boolVal: Boolean)(implicit zctx:Z3SolverCtx): AST = zctx.ctx.mkBool(boolVal)

  override protected def mkIntVar(s: String)(implicit zctx:Z3SolverCtx): AST = zctx.ctx.mkIntConst(s)

  override protected def mkBoolVar(s: String)(implicit zctx:Z3SolverCtx): AST = ???

  override protected def mkAssert(t: AST)(implicit zctx:Z3SolverCtx): Unit = zctx.solver.add(t.asInstanceOf[BoolExpr])

  override protected def mkFieldFun(n: String)(implicit zctx:Z3SolverCtx): AST = {
    val fun: FuncDecl = zctx.ctx.mkFuncDecl(n, addrSort, addrSort )
    fun
  }
  override protected def fieldEquals(f: AST, t1 : AST, t2:AST)(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkEq(f.asInstanceOf[FuncDecl].apply(t1.asInstanceOf[Expr]), t2.asInstanceOf[Expr])
  }

  private def interpretSolverOutput(status : Status) : Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      // this usually happens because of timeouts
      throw new IllegalStateException("Z3 decidability or timeout issue--got Status.UNKNOWN")
  }

  override protected def mkObjVar(s: PureVar)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkConst("object_addr_" + s.id.toString, addrSort)

  override def printDbgModel(messageTranslator: MessageTranslator,
                             traceAbstraction: Set[AbstractTrace], lenUID: String)(implicit zctx:Z3SolverCtx): Unit = {
    printAbstSolution(zctx.solver.getModel, messageTranslator, traceAbstraction, lenUID)
  }

  def printAbstSolution(model: Model, messageTranslator: MessageTranslator, traceAbstraction: Set[AbstractTrace],
                        lenUID: String)(implicit zctx:Z3SolverCtx) {
    println(s"===model: $model")
    traceAbstraction map { abs => {
      val uniqueID = System.identityHashCode(abs) + ""
      val len = mkIntVar(s"len_$lenUID").asInstanceOf[ArithExpr]
      println("=trace solution=")
      val traceLen: Int = model.eval(len, true).toString.toInt
      val traceFun = mkTraceFn(uniqueID).asInstanceOf[FuncDecl]
      //      val nameFun = mkINameFn(msgName).asInstanceOf[FuncDecl]
      val nameFun = messageTranslator.nameFun.asInstanceOf[FuncDecl]
      val argFun = mkArgFun().asInstanceOf[FuncDecl]
      (0 until traceLen).map ( index => {
        println(s"$index: ")
        val msgati: Expr = model.eval(traceFun.apply(zctx.ctx.mkInt(index)), true)
        val pipeThing = "\\|(.*)\\|".r // Sometimes z3 eval puts | | around result?
        val m = model.eval(nameFun.apply(msgati),true).toString match{
          case pipeThing(v) => v
          case v => v
        }
        if(m != "OTHEROTHEROTHER") {
          val iset = messageTranslator.iForZ3Name(m)
          val args = (0 until iset.head.lsVars.size)
            .map(index => model.eval(argFun.apply(zctx.ctx.mkInt(index), msgati), true)).mkString(",")

          println(s"$m " +
            s"args: $args")
        }else{
          println("Other Msg")
        }
      })
    }
    }
  }

  //  private def printModelSolution()
  override protected def solverSimplify(t: AST,
                                        state:State,
                                        messageTranslator: MessageTranslator,
                                        logDbg:Boolean)(implicit zctx:Z3SolverCtx): Option[AST] = {
    val solver = zctx.solver
    solver.add(t.asInstanceOf[BoolExpr])
    val status: Status = solver.check()
    status match{
      case Status.SATISFIABLE =>
        if (logDbg) {
          println(s"Model: ${solver.getModel}")
          printAbstSolution(solver.getModel(),messageTranslator,
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

  def tsort(implicit zctx:Z3SolverCtx): UninterpretedSort = zctx.ctx.mkUninterpretedSort("ClassTypes")
  private def equalToOneOf(e : Expr, vals : Array[Expr])(implicit zctx:Z3SolverCtx):BoolExpr = {
    val ctx = zctx.ctx
    ctx.mkOr(vals.map(v => ctx.mkEq(e,v)):_*)
  }
  def equalToOneOfTypes(e: Expr, typeToSolverConst: Map[String,AST],
                        types: Set[String])(implicit zctx:Z3SolverCtx):BoolExpr = {
    val solverTypes = types.map(typeToSolverConst).map(_.asInstanceOf[Expr])
    equalToOneOf(e,solverTypes.toArray)
  }
  override protected def mkTypeConstraintForAddrExpr(typeFun: AST, typeToSolverConst:Map[String,AST],
                                                     addr:AST, tc:Set[String])(implicit zctx:Z3SolverCtx): AST = {
    //    persistentConstraints.exprTypeConstraint(
    //      typeFun.asInstanceOf[FuncDecl].apply(addr.asInstanceOf[Expr]),tc)
    equalToOneOfTypes(typeFun.asInstanceOf[FuncDecl].apply(addr.asInstanceOf[Expr]),typeToSolverConst,tc)
  }
  override protected def createTypeFun()(implicit zctx:Z3SolverCtx):AST = {
    val args: Array[Sort] = Array(addrSort)
    zctx.ctx.mkFuncDecl("addressToType", args, tsort)
  }

  // Model vars have the pred identity hash code appended since they are unique to each pred
  // "_" means we don't care what the value is so just make arbitrary int
  override protected def mkModelVar(s: String, predUniqueID:String)(implicit zctx:Z3SolverCtx): AST = s match {
    case LSVar(s) =>
      zctx.ctx.mkConst ("model_var_" + s + "_" + predUniqueID, addrSort)
    case LSAnyVal() =>
      zctx.ctx.mkFreshConst ("_", addrSort)
    case _ => throw new IllegalArgumentException("mkModelVar expects variable or any.")
  }

  override protected def mkFreshIntVar(s:String)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkFreshConst(s, zctx.ctx.mkIntSort())

  /**
   * forall int in (min,max) condition is true
   * @param cond function from const to boolean expression
   */
  override protected def mkForallInt(min:AST, max:AST,cond: AST => AST)(implicit zctx:Z3SolverCtx): AST = {
    val j= zctx.ctx.mkFreshConst("j", zctx.ctx.mkIntSort()).asInstanceOf[ArithExpr]
    val range = mkAnd(List(mkLt(min,j), mkLt(j,max)))
    zctx.ctx.mkForall(Array(j), mkImplies(range,cond(j)).asInstanceOf[Expr]
      ,1,null,null,null,null)
  }
  override protected def mkForallAddr(name:String, cond: AST=>AST)(implicit zctx:Z3SolverCtx):AST = {
    val j = zctx.ctx.mkFreshConst(name, addrSort)
    zctx.ctx.mkForall(Array(j), cond(j).asInstanceOf[Expr],1,null,null,null,null)
  }
  override protected def mkExistsAddr(name:String, cond: AST=>AST)(implicit zctx:Z3SolverCtx):AST = {
    val j = zctx.ctx.mkFreshConst(name, addrSort)
    zctx.ctx.mkExists(Array(j), cond(j).asInstanceOf[Expr],1,null,null,null,null)
  }

  /**
   * there exists an int in (min,max) such that condition is true
   * @param cond function from const to boolean expression
   * @return
   */
  protected def mkExistsInt(min:AST, max:AST, cond:AST=>AST)(implicit zctx:Z3SolverCtx):AST = {
    val ctx = zctx.ctx
    val j= ctx.mkFreshConst("i", ctx.mkIntSort()).asInstanceOf[ArithExpr]
    val range = mkAnd(List(mkLt(min,j), mkLt(j,max)))
    ctx.mkExists(Array(j), mkAnd(range,cond(j)).asInstanceOf[Expr]
      ,1,null,null,null,null)
  }

  override protected def mkImplies(t: AST, t1: AST)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkImplies(t.asInstanceOf[BoolExpr], t1.asInstanceOf[BoolExpr])

  override protected def mkTraceFn(uid: String)(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx
    ctx.mkFuncDecl(s"tracefn_$uid", ctx.mkIntSort, ctx.mkUninterpretedSort("Msg"))
  }

  override protected def mkFreshTraceFn(uid: String)(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx
    ctx.mkFreshFuncDecl(s"tracefn_$uid", Array(ctx.mkIntSort), ctx.mkUninterpretedSort("Msg"))
  }

  override protected def mkINameFn(enum:AST)(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx
    ctx.mkFuncDecl(s"namefn_", ctx.mkUninterpretedSort("Msg"), enum.asInstanceOf[EnumSort])
  }

  override protected def mkArgFun()(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx
    //TODO: swap addr int wiht uninterpreted
    ctx.mkFuncDecl(s"argfun_", Array(ctx.mkIntSort(), ctx.mkUninterpretedSort("Msg")), addrSort)
  }

  override protected def mkIsNull(addr:AST)(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx
    val isNullFun = ctx.mkFuncDecl("isNullFn", addrSort, ctx.mkBoolSort())
    isNullFun.apply(addr.asInstanceOf[Expr])
  }

  override protected def mkIName(enum:AST, enumNum:Int)(implicit zctx:Z3SolverCtx): AST = enum.asInstanceOf[EnumSort].getConst(enumNum)

  override protected def mkEnum(name: String, types: List[String])(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx
    ctx.mkEnumSort(name, types.toArray:_*)
  }

  override protected def getEnumElement(enum:AST, i: Int)(implicit zctx:Z3SolverCtx): AST =
    enum.asInstanceOf[EnumSort].getConst(i)

  override protected def mkTraceConstraint(traceFun: AST, index: AST)(implicit zctx:Z3SolverCtx): AST =
    traceFun.asInstanceOf[FuncDecl].apply(index.asInstanceOf[ArithExpr])

  override protected def mkNameConstraint(nameFun: AST, msg: AST)(implicit zctx:Z3SolverCtx): AST =
    nameFun.asInstanceOf[FuncDecl].apply(msg.asInstanceOf[Expr])

  override protected def mkArgConstraint(argFun: AST, argIndex: AST, msg: AST)(implicit zctx:Z3SolverCtx): AST = {
    argFun.asInstanceOf[FuncDecl].apply(argIndex.asInstanceOf[Expr], msg.asInstanceOf[Expr])
  }

  override protected def mkAddrConst(i: Int)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkConst(s"addr_const$i", addrSort)

  override protected def mkDistinct(pvList: Iterable[PureVar])(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkDistinct(pvList.map(a => mkObjVar(a).asInstanceOf[Expr]).toArray:_*)
  }
  override protected def mkDistinctT(pvList: Iterable[AST])(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkDistinct(pvList.map(a => a.asInstanceOf[Expr]).toArray:_*)
  }

  override protected def encodeTypeConsteraints: StateTypeSolving = persistentConstraints.getUseZ3TypeSolver

  override protected def persist: ClassHierarchyConstraints = persistentConstraints

  override protected def mkTypeConstraints(types: Set[String])(implicit zctx: Z3SolverCtx): (AST, Map[String, AST]) = {
    val ctx = zctx.ctx
    val typeMap = types.map(t => (t-> ctx.mkConst(s"type_$t", tsort))).toMap
    val allConstraints: immutable.Iterable[Expr] = typeMap.map{case (_,c) => c}
    val unique = mkDistinctT(allConstraints)
    (unique, typeMap)
  }
}
