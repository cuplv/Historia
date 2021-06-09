package edu.colorado.plv.bounder.solver

import better.files.File
import com.microsoft.z3._
import edu.colorado.plv.bounder.lifestate.LifeState.{LSAnyVal, LSVar}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, PureVal, PureVar, State}

import scala.collection.immutable
import scala.collection.mutable

case class Z3SolverCtx(ctx: Context, solver:Solver) extends SolverCtx {
  // mapping from arg index to distinct uninterpreted sort used in argument function
  var args:Array[Expr[UninterpretedSort]] = Array()
  val initializedFieldFunctions : mutable.HashSet[String] = mutable.HashSet[String]()
  var indexInitialized:Boolean = false
  val uninterpretedTypes : mutable.HashSet[String] = mutable.HashSet[String]()
  def reset(): Unit = {
    solver.reset()
    args = Array()
    initializedFieldFunctions.clear()
    indexInitialized = false
    uninterpretedTypes.clear()
  }
}
class Z3StateSolver(persistentConstraints: ClassHierarchyConstraints) extends StateSolver[AST,Z3SolverCtx] {
  private val MAX_ARGS = 10

  val ctx: ThreadLocal[Context] = ThreadLocal.withInitial[Context]{ () =>
    val tCtx = new Context()
    tCtx
  }

  private def makeSolver():Solver = {
    val solver = ctx.get().mkSolver
    val params = ctx.get().mkParams()
//        params.add("timeout", 120000)
    params.add("timeout", 600000)
    solver.setParameters(params)
    solver
  }
  val solver: ThreadLocal[Solver] = ThreadLocal.withInitial(() => {
    makeSolver()
  })

  override def getSolverCtx: Z3SolverCtx = {
    Z3SolverCtx(ctx.get(), solver.get())
  }

  private def addrSort(implicit zctx:Z3SolverCtx) = zctx.ctx.mkUninterpretedSort("Addr")

  override def checkSAT()(implicit zctx:Z3SolverCtx): Boolean = {
//    val res = dumpDbg(zctx.solver.check)
    val res = zctx.solver.check()
    interpretSolverOutput(res)
  }

  //TODO: push/pop may be causing "unreachable" issue
  override def push()(implicit zctx:Z3SolverCtx): Unit = {
//    zctx.solver.push()
  }

  override def pop()(implicit zctx:Z3SolverCtx): Unit = {
//    zctx.solver.pop()
    zctx.reset()
//    solver.set(makeSolver())
  }

  override protected def mkEq(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkEq(lhs.asInstanceOf[Expr[Sort]], rhs.asInstanceOf[Expr[Sort]])
  }

  override protected def mkNe(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkNot(zctx.ctx.mkEq(lhs.asInstanceOf[Expr[Sort]],rhs.asInstanceOf[Expr[Sort]]))

  override protected def mkLt(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkLt(lhs.asInstanceOf[ArithExpr[ArithSort]],rhs.asInstanceOf[ArithExpr[ArithSort]])

  override protected def mkNot(o: AST)(implicit zctx:Z3SolverCtx): AST = zctx.ctx.mkNot(o.asInstanceOf[BoolExpr])

  override protected def mkAdd(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkAdd(lhs.asInstanceOf[ArithExpr[ArithSort]], rhs.asInstanceOf[ArithExpr[ArithSort]])
  }

  override protected def mkSub(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkSub(lhs.asInstanceOf[ArithExpr[ArithSort]], rhs.asInstanceOf[ArithExpr[ArithSort]])
  }


  override protected def mkAnd(lhs:AST, rhs:AST)(implicit zctx:Z3SolverCtx):AST = {
    mkAnd(List(lhs,rhs))
  }

  override protected def mkAnd(t:List[AST])(implicit zctx:Z3SolverCtx): AST = {
    if(t.nonEmpty) {
      val tb: Array[BoolExpr] = t.map(_.asInstanceOf[BoolExpr]).toArray
      zctx.ctx.mkAnd(tb: _*)
    }else
      mkBoolVal(boolVal = true)
  }

  override protected def mkOr(lhs: AST, rhs: AST)(implicit zctx:Z3SolverCtx): AST =
    zctx.ctx.mkOr(lhs.asInstanceOf[BoolExpr], rhs.asInstanceOf[BoolExpr])

  override protected def mkOr(t: Iterable[AST])(implicit zctx:Z3SolverCtx): AST = {
    if(t.nonEmpty) {
      val tb: Array[BoolExpr] = t.map(_.asInstanceOf[BoolExpr]).toArray
      zctx.ctx.mkOr(tb: _*)
    }else{
      mkBoolVal(boolVal = false)
    }
  }

//  /**
//   * @param l list of boolean expressions
//   * @return boolean expression that is true iff exactly one expression in l is true
//   */
//  override protected def mkExactlyOneOf(l:List[AST])(implicit zctx:Z3SolverCtx): AST = {
////    val ctx = zctx.ctx
////    val oneorzero: Seq[Expr[Sort]] = l.map(lv =>
////      ctx.mkITE(lv.asInstanceOf[BoolExpr],ctx.mkInt(1),ctx.mkInt(0)).asInstanceOf[Expr[Sort]])
////    ctx.mkEq(ctx.mkAdd(oneorzero.toArray:_*), ctx.mkInt(1))
//    ???
//  }

  override protected def mkIntVal(i: Int)(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkInt(i)
  }

  override protected def mkBoolVal(boolVal: Boolean)(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkBool(boolVal)
  }

  override protected def mkIntVar(s: String)(implicit zctx:Z3SolverCtx): AST = zctx.ctx.mkIntConst(s)

  override protected def mkLenVar(s: String)(implicit zctx: Z3SolverCtx): AST = zctx.ctx.mkConst(s, indexSort)

  override protected def mkAssert(t: AST)(implicit zctx:Z3SolverCtx): Unit = zctx.solver.add(t.asInstanceOf[BoolExpr])

  override protected def fieldEquals(f: AST, t1 : AST, t2:AST)(implicit zctx:Z3SolverCtx): AST = {
    assert(f.isInstanceOf[FuncDecl[UninterpretedSort]])
    assert(t1.isInstanceOf[Expr[UninterpretedSort]])
    assert(t2.isInstanceOf[Expr[UninterpretedSort]])
    f.asInstanceOf[FuncDecl[UninterpretedSort]]
      .apply(t1.asInstanceOf[Expr[UninterpretedSort]],t2.asInstanceOf[Expr[UninterpretedSort]])
  }

  override protected def dumpDbg[T](cont: () => T)(implicit zctx: Z3SolverCtx): T = {
    println(s"current thread = ${Thread.currentThread().getId}")
    var failed = true
    var result:Option[T] = None
    val currentTime = (System.currentTimeMillis() / 1000).toInt
    val f = File(s"z3Timeout_${currentTime}")
    f.write(getSolverCtx.solver.toString)
    try {
      println(s"z3 dbg file written: ${f}")
      result = Some(cont())
      failed = false
    } catch{
      case t:Throwable =>
        println("error")
        throw t
    }
    if(!failed && result.nonEmpty && result.get != null){
      println(s"deleting file due to success: ${f}")
      f.delete()
    }
    result.getOrElse(throw new IllegalStateException("Unknown failure"))
  }

  private def interpretSolverOutput(status : Status) : Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      throw new IllegalStateException("Z3 decidability or timeout issue--got Status.UNKNOWN")
  }

  override def printDbgModel(messageTranslator: MessageTranslator,
                             traceAbstraction: Set[AbstractTrace], lenUID: String)(implicit zctx:Z3SolverCtx): Unit = {
    printAbstSolution(zctx.solver.getModel, messageTranslator, traceAbstraction, lenUID)
  }

  def printAbstSolution(model: Model, messageTranslator: MessageTranslator, traceAbstraction: Set[AbstractTrace],
                        lenUID: String)(implicit zctx:Z3SolverCtx) {
    println(s"===model: $model")
    traceAbstraction map { abs => {
      val uniqueID = System.identityHashCode(abs) + ""
      val len = mkLenVar(s"len_$lenUID").asInstanceOf[Expr[UninterpretedSort]]
      println("=trace solution=")
      val traceLen: Int = model.eval(len, true).toString.toInt //TODO:=============
      val traceFun = mkTraceFn(uniqueID).asInstanceOf[FuncDecl[_]]
      val nameFun = messageTranslator.nameFun.asInstanceOf[FuncDecl[_]]
      val argFun = mkArgFun().asInstanceOf[FuncDecl[_]]
      (0 until traceLen).map ( index => {
        println(s"$index: ")
        val msgati = model.eval(traceFun.apply(zctx.ctx.mkInt(index)), true)
        val mIter = messageTranslator.solverToIdentitySignature.filter{
          case (ast, _) => model.eval(mkEq(nameFun.apply(msgati), ast).asInstanceOf[BoolExpr],true).isTrue
        }
        val m = mIter.head._2

        if(m != "OTHEROTHEROTHER") {
          val iset = messageTranslator.iForZ3Name(m)
          val args = iset.head.lsVars.indices
            .map(index => model.eval(argFun.apply(zctx.args(index), msgati), true)).mkString(",")

          println(s"$m " +
            s"args: $args")
        }else{
          println("Other Msg")
        }
      })
    }
    }
  }

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
          printAbstSolution(solver.getModel,messageTranslator,
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

  def typeSort(implicit zctx:Z3SolverCtx): UninterpretedSort = zctx.ctx.mkUninterpretedSort("ClassTypes")
  def constSort(implicit zctx:Z3SolverCtx): UninterpretedSort = zctx.ctx.mkUninterpretedSort("ConstVals")
  def localSort(implicit zctx:Z3SolverCtx): UninterpretedSort = zctx.ctx.mkUninterpretedSort("Locals")
  def dynFieldSort(implicit zctx:Z3SolverCtx):UninterpretedSort = zctx.ctx.mkUninterpretedSort("DynField")
  private def equalToOneOf(e : Expr[Sort], vals : Array[Expr[Sort]])(implicit zctx:Z3SolverCtx):BoolExpr = {
    val ctx = zctx.ctx
    ctx.mkOr(vals.map(v => ctx.mkEq(e,v)):_*)
  }
  def equalToOneOfTypes(e: Expr[Sort], typeToSolverConst: Map[Int,AST],
                        types: Set[Int])(implicit zctx:Z3SolverCtx):BoolExpr = {
    val solverTypes = types.map(typeToSolverConst).map(_.asInstanceOf[Expr[Sort]])
    equalToOneOf(e,solverTypes.toArray)
  }
  override protected def mkTypeConstraintForAddrExpr(typeFun: AST, typeToSolverConst:Map[Int,AST],
                                                     addr:AST, tc:Set[Int])(implicit zctx:Z3SolverCtx): AST = {
    equalToOneOfTypes(typeFun.asInstanceOf[FuncDecl[Sort]].apply(addr.asInstanceOf[Expr[Sort]]),typeToSolverConst,tc)
  }
  override protected def createTypeFun()(implicit zctx:Z3SolverCtx):AST = {
    val args: Array[Sort] = Array(addrSort)
    zctx.ctx.mkFuncDecl("addressToType", args, typeSort)
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
    val j = zctx.ctx.mkFreshConst("j", zctx.ctx.mkIntSort())
    val range = mkAnd(List(mkLt(min,j), mkLt(j,max)))
    zctx.ctx.mkForall(Array(j), mkImplies(range,cond(j)).asInstanceOf[BoolExpr]
      ,1,null,null,null,null)
  }
  override protected def mkForallAddr(name:String, cond: AST=>AST)(implicit zctx:Z3SolverCtx):AST = {
    val j: Expr[UninterpretedSort] = zctx.ctx.mkFreshConst(name, addrSort)
    zctx.ctx.mkForall(Array(j), cond(j).asInstanceOf[BoolExpr],1,null,null,null,null)
  }

  private def nameConstMap(name:Set[String])(implicit zctx:Z3SolverCtx):(Array[Expr[_]], Map[String,AST]) = {
    val j = name.map(n => zctx.ctx.mkFreshConst(n, addrSort).asInstanceOf[Expr[_]]).toArray
    val nameToAST = (name zip j).toMap
    (j,nameToAST)
  }
  override protected def mkForallAddr(name: Set[String], cond: Map[String,AST] => AST)
                                     (implicit zctx:Z3SolverCtx): AST = {
    if(name.isEmpty){
      cond(Map())
    }else {
      val (j, nameToAST) = nameConstMap(name)
      zctx.ctx.mkForall(j,
        cond(nameToAST).asInstanceOf[Expr[BoolSort]], 1,
        null, null, null, null)
    }
  }

  override protected def mkExistsAddr(name:String, cond: AST=>AST)(implicit zctx:Z3SolverCtx):AST = {
    val j = zctx.ctx.mkFreshConst(name, addrSort)
    zctx.ctx.mkExists(Array(j), cond(j).asInstanceOf[BoolExpr],1,null,null,null,null)
  }

  override protected def mkExistsAddr(name: Set[String], cond: Map[String,AST] => AST)
                                     (implicit zctx:Z3SolverCtx): AST = {
    if(name.isEmpty){
      cond(Map())
    }else {
      val (j, nameToAST) = nameConstMap(name)
      zctx.ctx.mkExists(j,
        cond(nameToAST).asInstanceOf[Expr[BoolSort]], 1,
        null, null, null, null)
    }
  }

  /**
   * there exists an int in (min,max) such that condition is true
   * @param cond function from const to boolean expression
   * @return
   */
  protected def mkExistsInt(min:AST, max:AST, cond:AST=>AST)(implicit zctx:Z3SolverCtx):AST = {
    val ctx = zctx.ctx
    val j= ctx.mkFreshConst("i", ctx.mkIntSort()).asInstanceOf[ArithExpr[ArithSort]]
    val range = mkAnd(List(mkLt(min,j), mkLt(j,max)))
    ctx.mkExists(Array(j), mkAnd(range,cond(j)).asInstanceOf[BoolExpr]
      ,1,null,null,null,null)
  }

  override protected def mkImplies(t: AST, t1: AST)(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkImplies(t.asInstanceOf[BoolExpr], t1.asInstanceOf[BoolExpr])
  }

  override protected def mkTraceFn(uid: String)(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx
    ctx.mkFuncDecl(s"tracefn_$uid", indexSort, ctx.mkUninterpretedSort("Msg"))
  }

  override protected def mkFreshTraceFn(uid: String)(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx
    ctx.mkFreshFuncDecl(s"tracefn_$uid", Array(indexSort), ctx.mkUninterpretedSort("Msg"))
  }

  override protected def mkLocalFn(uid: String)(implicit zctx: Z3SolverCtx): FuncDecl[_] = {
    zctx.ctx.mkFuncDecl(s"localfn_${uid}", localSort, addrSort)
  }

  override protected def mkDynFieldFn(uid:String, fieldName:String)(implicit zctx:Z3SolverCtx):FuncDecl[_] = {
    val addrAddr:Array[Sort] = Array(addrSort,addrSort)
    val fun = zctx.ctx.mkFuncDecl(s"dynField_${fieldName}_${uid}", addrAddr, zctx.ctx.mkBoolSort)
    if(!zctx.initializedFieldFunctions.contains(fieldName)){
      val a1 = zctx.ctx.mkFreshConst("a1", addrSort)
      val a2 = zctx.ctx.mkFreshConst("a2", addrSort)
      val a3 = zctx.ctx.mkFreshConst("a3", addrSort)

      val b = zctx.ctx.mkForall(Array(a1,a2,a3),
        mkImplies(mkAnd(fun.apply(a1,a2), fun.apply(a1,a3)), mkEq(a2,a3)).asInstanceOf[BoolExpr],
        1, null, null, null, null )
      mkAssert(b)
      zctx.initializedFieldFunctions.add(fieldName)
    }
    fun
  }

  override protected def mkINameFn()(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx //TODO: ======
    ctx.mkFuncDecl(s"namefn_", ctx.mkUninterpretedSort("Msg"), ctx.mkUninterpretedSort("inames"))
  }
  private def getArgSort()(implicit zctx:Z3SolverCtx): UninterpretedSort = {
    zctx.ctx.mkUninterpretedSort("Arguments")
  }
  private def mkArgs(n:Int)(implicit zctx:Z3SolverCtx):Array[Expr[UninterpretedSort]] = {
    val argIds = (0 until n).map(v => zctx.ctx.mkFreshConst(s"arg___${v}", getArgSort())).toArray
    val argf = zctx.ctx.mkConst("argf__", getArgSort())
    val constraint: Expr[BoolSort] = mkOr(argIds.map(argId => mkEq(argf, argId) ).toList).asInstanceOf[Expr[BoolSort]]
    mkAssert(zctx.ctx.mkForall(Array(argf), constraint, 1, null,null,null,null))
    mkAssert(zctx.ctx.mkDistinct(argIds:_*))
    argIds
  }
  override protected def mkArgFun()(implicit zctx:Z3SolverCtx): AST = {
    if(zctx.args.isEmpty){
      zctx.args = mkArgs(MAX_ARGS)
    }
    val ctx = zctx.ctx
    val argSort:Sort = getArgSort()
    ctx.mkFuncDecl(s"argfun_", Array(argSort, ctx.mkUninterpretedSort("Msg")), addrSort)
  }

//  override protected def mkIsNull(addr:AST)(implicit zctx:Z3SolverCtx): AST = {
//    val ctx = zctx.ctx
//    val isNullFun = ctx.mkFuncDecl("isNullFn", addrSort, ctx.mkBoolSort())
//    isNullFun.apply(addr.asInstanceOf[Expr])
//  }
//
//  override protected def mkIntValueConstraint(addr:AST)(implicit zctx:Z3SolverCtx): AST = {
//    val ctx = zctx.ctx
//    val intConstFn = ctx.mkFuncDecl("intConstFn", addrSort, ctx.mkIntSort())
//    intConstFn.apply(addr.asInstanceOf[Expr])
//  }

  protected def mkConstValueConstraint(addr:AST)(implicit zctx:Z3SolverCtx):AST = {
    val ctx = zctx.ctx
    val constFn = ctx.mkFuncDecl("constFn", addrSort, constSort)
    constFn.apply(addr.asInstanceOf[Expr[UninterpretedSort]])
  }

  override protected def mkIName(enum:AST, enumNum:Int)(implicit zctx:Z3SolverCtx): AST = {
    enum.asInstanceOf[EnumSort[_]].getConst(enumNum)
  }

  override protected def mkUT(name: String, types: List[String])(implicit zctx:Z3SolverCtx): Map[String,AST] = {
    val ctx = zctx.ctx
//    ctx.mkEnumSort(name, types.toArray:_*)
    val sort = ctx.mkUninterpretedSort(name)
    val tmap:Map[String,AST] = types.map(t => (t -> ctx.mkConst(t, sort))).toMap
    if(!zctx.uninterpretedTypes.contains(name)){
      val u = ctx.mkFreshConst("u", sort)
      val eachT = mkOr(tmap.map{case (_,v) => mkEq(u, v)}).asInstanceOf[BoolExpr]
      mkAssert(ctx.mkForall(Array(u), eachT, 1, null,null,null,null))
      val tOnly = tmap.map{case (_,v) => v.asInstanceOf[Expr[UninterpretedSort]]}
      mkAssert(ctx.mkDistinct(tOnly.toArray:_*))
    }
    tmap
  }

//  override protected def getEnumElement(enum:(AST, Map[String,AST]), i: String)(implicit zctx:Z3SolverCtx): AST = {
////    enum.asInstanceOf[EnumSort[_]].getConst(i)
//    enum._2(i)
//  }

  override protected def mkTraceConstraint(traceFun: AST, index: AST)(implicit zctx:Z3SolverCtx): AST = {
    traceFun.asInstanceOf[FuncDecl[_]].apply(index.asInstanceOf[Expr[UninterpretedSort]])
  }

  override protected def mkNameConstraint(nameFun: AST, msg: AST)(implicit zctx:Z3SolverCtx): AST = {
    nameFun.asInstanceOf[FuncDecl[_]].apply(msg.asInstanceOf[Expr[Sort]])
  }

  override protected def mkArgConstraint(argFun: AST, argIndex: Int, msg: AST)(implicit zctx:Z3SolverCtx): AST = {
    assert(msg.isInstanceOf[Expr[UninterpretedSort]])
    assert(zctx.args.nonEmpty, "Must call mkArgFun before mkArgConstraint")
    assert(zctx.args.length > argIndex, s"More than ${MAX_ARGS} arguments not supported. Got arg index ${argIndex}.")
    val arg = zctx.args(argIndex)
    mkArgConstraint(argFun, arg, msg.asInstanceOf[Expr[UninterpretedSort]])
  }

  private def mkArgConstraint(argFun:AST,
                              arg:Expr[UninterpretedSort],
                              msg:Expr[UninterpretedSort])(implicit zctx:Z3SolverCtx):AST = {
    argFun.asInstanceOf[FuncDecl[_]].apply(arg,
      msg)
  }

  override protected def mkAllArgs(argFun: AST, msg: AST, pred: AST => AST)(implicit zctx:Z3SolverCtx): AST = {
    val argFun = mkArgFun()
    val argConst:Expr[UninterpretedSort] = zctx.ctx.mkFreshConst("argConst", getArgSort())
    val constraint = pred(mkArgConstraint(argFun, argConst,
      msg.asInstanceOf[Expr[UninterpretedSort]])).asInstanceOf[BoolExpr]
    zctx.ctx.mkForall(Array(argConst), constraint, 1,null,null,null,null)
  }

  override protected def mkExistsArg(argFun: AST, msg: AST, pred: AST => AST)(implicit zctx:Z3SolverCtx): AST = {
    val argFun = mkArgFun()
    val argConst = zctx.ctx.mkFreshConst("argConst", getArgSort())
    val constraint = pred(mkArgConstraint(argFun,
      argConst, msg.asInstanceOf[Expr[UninterpretedSort]])).asInstanceOf[BoolExpr]
    zctx.ctx.mkExists(Array(argConst), constraint, 1,null,null,null,null)
  }

  override protected def mkAddrConst(i: Int)(implicit zctx:Z3SolverCtx): AST = {
    zctx.ctx.mkConst(s"addr_const$i", addrSort)
  }


  override protected def mkDistinct(pvList: Iterable[PureVar],pvMap:Map[PureVar,AST])(implicit zctx:Z3SolverCtx): AST = {
    if(pvList.isEmpty){
      mkBoolVal(boolVal = true)
    }else {
      zctx.ctx.mkDistinct(pvList.map { a =>
        pvMap(a).asInstanceOf[Expr[UninterpretedSort]]
      }.toArray: _*)
    }
  }

  override protected def mkDistinctT(pvList: Iterable[AST])(implicit zctx:Z3SolverCtx): AST = {
    if(pvList.isEmpty){
      mkBoolVal(boolVal = true)
    }else {
      zctx.ctx.mkDistinct(pvList.map { a => a.asInstanceOf[Expr[UninterpretedSort]] }.toArray: _*)
    }
  }

  override protected def encodeTypeConsteraints: StateTypeSolving = persistentConstraints.getUseZ3TypeSolver

  override protected def persist: ClassHierarchyConstraints = persistentConstraints



  override protected def mkTypeConstraints(types: Set[Int])(implicit zctx: Z3SolverCtx): (AST, Map[Int, AST]) = {
    val ctx = zctx.ctx
    val typeMap = types.map(t => (t-> ctx.mkConst(s"type_$t", typeSort))).toMap
    val allConstraints = typeMap.map{case (_,c) => c}
    val unique = mkDistinctT(allConstraints)
    (unique, typeMap)
  }

  override protected def mkLocalConstraint(localIdent:AST, equalTo: AST, uid:String)
                                          (implicit zctx: Z3SolverCtx): AST = {
    val fn = mkLocalFn(uid)
    mkEq(fn.apply(localIdent.asInstanceOf[Expr[UninterpretedSort]]), equalTo)
  }

  override protected def mkDynFieldConstraint(base: AST, fieldName: String, equalTo: AST, uid:String)
                                             (implicit zctx: Z3SolverCtx): AST = {
    val fn = mkDynFieldFn(uid, fieldName)
    val appFun = fn.apply(base.asInstanceOf[Expr[Sort]], equalTo.asInstanceOf[Expr[Sort]])
//    mkEq(appFun, equalTo)
    appFun
  }

  override protected def mkStaticFieldConstraint(clazz:String, fieldName:String, equalTo:AST, uid:String)
                                             (implicit zctx:Z3SolverCtx):AST = {
    val staticField = zctx.ctx.mkConst(s"staticField___${clazz}___${fieldName}", addrSort) //.mkFuncDecl(s"dynField_${fieldName}_${uid}", addrSort)
    mkEq(staticField, equalTo)
  }

  def localToName(local:(String,Int)):String = s"local_${local._1}____${local._2}"
  override protected def mkLocalDomain(locals: Set[(String, Int)])
                                      (implicit zctx: Z3SolverCtx): (AST, Map[(String, Int), AST]) = {
    val ctx = zctx.ctx
    val localMap = locals.map(t => (t-> ctx.mkConst(localToName(t), localSort))).toMap
    val allConstraints: immutable.Iterable[Expr[UninterpretedSort]] = localMap.map{case (_,c) => c}
    val unique = mkDistinctT(allConstraints)
    (unique, localMap)
  }

  def fieldToName(fld:String):String = {
    s"field_${fld}"
  }
//  override protected def mkDynFieldDomain(fields: Set[String])(implicit zctx: Z3SolverCtx): (AST, Map[String, AST]) = {
//    val ctx = zctx.ctx
//    val fieldMap = fields.map(t => (t-> ctx.mkConst(fieldToName(t), ???))).toMap
//    val allConstraints: immutable.Iterable[Expr] = fieldMap.map{case (_,c) => c}
//    val unique = mkDistinctT(allConstraints)
//    (unique, fieldMap)
//  }

  protected def mkConstConstraintsMap(pvs: Set[PureVal])(implicit zctx: Z3SolverCtx): (AST, Map[PureVal, AST]) = {
    val ctx = zctx.ctx
    val constMap = pvs.flatMap(t => t.z3Tag.map(tag => (t-> ctx.mkConst(s"const_${tag}", constSort)))).toMap
    val allConstraints: immutable.Iterable[Expr[UninterpretedSort]] = constMap.map{case (_,c) => c}
    val unique = mkDistinctT(allConstraints)
    (unique, constMap)
  }

  protected override def mkAllAddrHavePV(pvToZT: Map[PureVar,AST])(implicit zctx:Z3SolverCtx): AST = {
    val ctx = zctx.ctx

    val pvs: Set[PureVar] = pvToZT.keySet

    val uniqueAddr = ctx.mkConst("uniqueAddr_", addrSort)
    val equalToOne = pvs.map(pv => ctx.mkEq(pvToZT(pv).asInstanceOf[Expr[UninterpretedSort]], uniqueAddr)).toArray

    // TODO: here we limit the number of addresses to the number of pure variables, Figure out if this is sound
    // Can there ever be a trace, store, and stack that satisfies our separation logic
    // formula with more addr than pv but not with as many addr as pv?
    ctx.mkForall(Array(uniqueAddr), ctx.mkOr(equalToOne:_*),
      1, null,null,null,null)
    ??? //TODO: not currently used due to unknown soundness.
  }

  def indexSort(implicit zctx: Z3SolverCtx):UninterpretedSort = {
    zctx.ctx.mkUninterpretedSort("Uint")
  }

  private def indexFuns(implicit zctx: Z3SolverCtx): (FuncDecl[BoolSort], FuncDecl[BoolSort]) = {
    val ctx = zctx.ctx
    val indexIndex:Array[Sort] = Array(indexSort, indexSort)
    val lt = ctx.mkFuncDecl("indexLT", indexIndex, zctx.ctx.mkBoolSort)
//    val succ = ctx.mkFuncDecl("indexSucc", indexIndex, zctx.ctx.mkBoolSort)
    val zero = mkZeroIndex.asInstanceOf[Expr[UninterpretedSort]]
    val maxV = ctx.mkFreshConst("maxInd", indexSort)
    if(!zctx.indexInitialized){
      // ** less than is transitive
      // forall a,b,c. a<b /\ b<c => a<c
      val i1 = ctx.mkFreshConst("i1",indexSort)
      val i2 = ctx.mkFreshConst("i2",indexSort)
      val i3 = ctx.mkFreshConst("i3",indexSort)
      val trans: BoolExpr = mkImplies(mkAnd(lt.apply(i1,i2), lt.apply(i2,i3)), lt.apply(i1,i3)).asInstanceOf[BoolExpr]

      val b = ctx.mkForall(Array(i1,i2,i3), trans, 1, null, null, null, null )
      mkAssert(b)

      // forall a,b . a<b => a != b
      val a1 = zctx.ctx.mkFreshConst("a1",indexSort)
      val b1 = zctx.ctx.mkFreshConst("b1",indexSort)
      mkAssert(ctx.mkForall(Array(a1,b1), mkImplies(lt.apply(a1,b1), mkNot(mkEq(a1,b1))).asInstanceOf[BoolExpr],
        1,null,null,null,null))


      // ** All indices are greater than or equal to zero
      val i4 = ctx.mkFreshConst("i4",indexSort)
      val zeroLTE:BoolExpr = mkOr(mkEq(zero, i4),
        lt.apply(zero, i4)).asInstanceOf[BoolExpr]
      mkAssert(ctx.mkForall(Array(i4), zeroLTE, 1, null, null, null, null))

//      // **successor is greater than value
//      // forall x,y. succ(x,y) => x<y
//      val x = zctx.ctx.mkFreshConst("x",indexSort)
//      val y = zctx.ctx.mkFreshConst("y",indexSort)
//      mkAssert(ctx.mkForall(Array(x,y), mkImplies(
//        succ.apply(x,y) // x < y
//        ,
//        lt.apply(x,y)
//      ).asInstanceOf[BoolExpr], 1, null, null, null, null))
//      zctx.indexInitialized = true
//
//      // **successor is unique
//      //forall x,y,z . succ(x,y) => (not succ(x,z)) \/ z = y
//      val x1 = zctx.ctx.mkFreshConst("x1",indexSort)
//      val y1 = zctx.ctx.mkFreshConst("y1",indexSort)
//      val z1 = zctx.ctx.mkFreshConst("z1",indexSort)
//      mkAssert(ctx.mkForall(Array(x1,y1,z1), mkImplies(
//        succ.apply(x1,y1) // x < y
//        ,
//        mkOr(mkNot(succ.apply(x1,z1)), mkEq(z1,y1)).asInstanceOf[BoolExpr]
//      ).asInstanceOf[BoolExpr], 1, null, null, null, null))
//      zctx.indexInitialized = true
//
//      // **predecessor is unique
//      //forall x,y,z . succ(x,y) => (not succ(z,y)) \/ z = x
//      mkAssert(ctx.mkForall(Array(x1,y1,z1), mkImplies(
//        succ.apply(x1,y1) // x < y
//        ,
//        mkOr(mkNot(succ.apply(z1,y1)), mkEq(z1,x1)).asInstanceOf[BoolExpr]
//      ).asInstanceOf[BoolExpr], 1, null, null, null, null))
//      zctx.indexInitialized = true
//
//
//      // ** all values have a successor except max
//      //forall x . exists y . succ(x,y) \/ (x=max /\ not succ(x,y))
//      val x3 = zctx.ctx.mkFreshConst("x3", indexSort)
//      val y3 = zctx.ctx.mkFreshConst("y3", indexSort)
//      mkAssert(ctx.mkForall(Array(x3),ctx.mkExists(Array(y3), ctx.mkOr(succ.apply(x3,y3),
//        ctx.mkAnd(ctx.mkEq(x3,maxV), ctx.mkNot(succ.apply(x3,y3)))),
//        1, null,null,null,null) ,
//        1, null,null,null,null))
//
//      // ** all values have a predecessor except zero
//      //forall x . exists y . succ(y,x) \/ (x=zero /\ not succ(y,x))
//      mkAssert(ctx.mkForall(Array(x3),
//        ctx.mkExists(Array(y3),
//          ctx.mkOr(
//            succ.apply(y3,x3),
//            ctx.mkAnd(
//              ctx.mkEq(x3, zero),
//              ctx.mkNot(succ.apply(y3,x3))
//            )
//          ),
//          1, null,null,null,null) ,
//        1, null,null,null,null))
    }

    (lt,???)
  }
  override protected def mkForallIndex(min: AST, max: AST, cond: AST => AST)(implicit zctx: Z3SolverCtx): AST = {
    val min_ = min.asInstanceOf[Expr[UninterpretedSort]]
    val max_ = max.asInstanceOf[Expr[UninterpretedSort]]
    val ctx = zctx.ctx
    val (lt,_) = indexFuns
    val j = ctx.mkFreshConst("j", indexSort)
    val range = mkAnd(mkOr(lt.apply(min_,j), mkEq(min_, j)), lt.apply(j, max_))
    ctx.mkForall(Array(j), mkImplies(range, cond(j)).asInstanceOf[BoolExpr],
      1,null,null,null,null)
  }

  override protected def mkExistsIndex(min: AST, max: AST, cond: AST => AST)(implicit zctx: Z3SolverCtx): AST = {
    val min_ = min.asInstanceOf[Expr[UninterpretedSort]]
    val max_ = max.asInstanceOf[Expr[UninterpretedSort]]
    val ctx = zctx.ctx
    val (lt,_) = indexFuns
    val j = ctx.mkFreshConst("j", indexSort)
    val range = mkAnd(mkOr(lt.apply(min_,j), mkEq(min_, j)), lt.apply(j, max_))
    ctx.mkExists(Array(j), mkImplies(range, cond(j)).asInstanceOf[BoolExpr],
      1,null,null,null,null)
  }

  override protected def mkLessThanIndex(ind1: AST, ind2: AST)(implicit zctx: Z3SolverCtx): AST = {
    val lt = indexFuns._1
    lt.apply(ind1.asInstanceOf[Expr[UninterpretedSort]],ind2.asInstanceOf[Expr[UninterpretedSort]])
  }

  override protected def mkAddOneIndex(ind: AST)(implicit zctx: Z3SolverCtx): AST = {
    val indNext = zctx.ctx.mkFreshConst("indNext", indexSort)
    val succ = indexFuns._2
    mkAssert(succ.apply(ind.asInstanceOf[Expr[UninterpretedSort]],indNext.asInstanceOf[Expr[UninterpretedSort]]))
    indNext
  }

  override protected def mkZeroIndex()(implicit zctx: Z3SolverCtx): AST = {
    zctx.ctx.mkConst("ZeroInd", indexSort)
  }
}
