package edu.colorado.plv.bounder.solver

import better.files.File
import com.microsoft.z3._
import com.microsoft.z3.enumerations.Z3_ast_print_mode
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppMethod, CBEnter, CBExit, CIEnter, CIExit, FwkMethod, TAddr, TCLInit, TMessage, TNew, TNullVal, TVal, T_, WitnessExplanation}
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState.{LSAnyVal, LSVar}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, NullVal, PureVal, PureVar, State}

import scala.collection.immutable
import scala.collection.mutable

case class Z3SolverCtx(timeout:Int, randomSeed:Int) extends SolverCtx[AST] {
  var ctx = new Context()
  val checkStratifiedSets = false // set to true to check EPR stratified sets (see Paxos Made EPR, Padon OOPSLA 2017)
  var solver:Solver = ctx.mkSolver()
  // mapping from arg index to distinct uninterpreted sort used in argument function
  var args:Array[Expr[UninterpretedSort]] = Array()
  val initializedFieldFunctions : mutable.HashSet[String] = mutable.HashSet[String]()
  var indexInitialized:Boolean = false
  val uninterpretedTypes : mutable.HashSet[String] = mutable.HashSet[String]()
  val sortEdges = mutable.HashSet[(String,String)]()
  // Method for detecting cycles in function sorts or Ɐ∃ quantifications
  private def detectCycle(edges:Set[(String,String)]):Boolean = {
    def iCycle(n:String, visited:Set[String]):Boolean = {
      if(visited.contains(n)) {
        true
      }else{
        val nextNodes = edges.flatMap{
          case (k,v) if k==n => Some(v)
          case _ => None
        }
        nextNodes.exists(nn => iCycle(nn, visited + n))
      }
    }

    val allNodes:Set[String] = edges.flatMap{
      case (k,v) => Set(k,v)
    }
    allNodes.exists(n => iCycle(n,Set()))
  }
  def mkAssert(t: AST): Unit = this.synchronized{
    if(checkStratifiedSets) {
      //sortEdges.addAll(getQuantAltEdges(t))
    }
    solver.add(t.asInstanceOf[BoolExpr])
  }
  private def getQuantAltEdges(t: AST, forallQTypes : Set[String] = Set()): Set[(String,String)] = {
    val sorts:Set[(String,String)] = t match {
      case v:BoolExpr if v.isConst =>
        Set()
      case v:BoolExpr if v.isOr || v.isAnd || v.isEq =>
        val args = v.getArgs
        args.flatMap(t => getQuantAltEdges(t,forallQTypes)).toSet
      case t:Quantifier if t.isUniversal =>
        val boundSorts = t.getBoundVariableSorts.map(_.toString)
        getQuantAltEdges(t.getBody, forallQTypes ++ boundSorts)
      case t:Quantifier if t.isExistential =>
        val boundSorts = t.getBoundVariableSorts.map(_.toString)
        if(boundSorts.exists(exV => forallQTypes.contains(exV))) {
          Set()
        } else{
          getQuantAltEdges(t.getBody, forallQTypes)
        }
      case v if v.isVar => Set()
      case v:Expr[_] if v.isApp =>
        val args = v.getArgs
        val argSort = args.map(a => a.getSort.toString)
        val resSort = v.getSort.toString
        val newEdges: Array[(String, String)] = argSort.map(argSort => argSort -> resSort)
        args.flatMap(t => getQuantAltEdges(t,forallQTypes)).toSet ++ newEdges
      case v =>
        println(v)
        ???
    }
    sorts.filter{ // Bool -> ? or ? -> Bool is fine since bool only has 2 values
      case ("Bool", _ ) => false
      case (_, "Bool") => false
      case _ => true
    }
  }
  private def makeSolver(timeout:Int):Solver = this.synchronized{
    val solver = ctx.mkSolver
//    val solver = ctx.mkSimpleSolver()
    val params = ctx.mkParams()
    params.add("timeout", timeout)
    params.add("random-seed", randomSeed)
//    params.add("timeout", 30000)
    // params.add("threads", 4) Note: threads cause weird decidability issue

    // set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)
    //    params.add("timeout", 1600000)

    //TODO: does this get rid of the "let" statements when printing?
    ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_SMTLIB_FULL)
    solver.setParameters(params)
    solver
  }
  def reset(): Unit = this.synchronized{
    //    assert(!detectCycle(sortEdges.toSet), "Quantifier Alternation Exception") //TODO: ==== remove after dbg
    // sortEdges.clear()

//    println(s"reset ctx: ${System.identityHashCode(this)}")
    args = Array()
    initializedFieldFunctions.clear()
    indexInitialized = false
    uninterpretedTypes.clear()
    ctx.close()
    ctx = new Context()
    solver = makeSolver(timeout)
//    Thread.sleep(100)
  }
}
class Z3StateSolver(persistentConstraints: ClassHierarchyConstraints, timeout:Int = 120000,
                    randomSeed:Int=30) extends StateSolver[AST,Z3SolverCtx] {
  private val MAX_ARGS = 10

  val threadLocalCtx: ThreadLocal[Z3SolverCtx] = ThreadLocal.withInitial( () => Z3SolverCtx(timeout,randomSeed))
//  val ctx: ThreadLocal[Context] = ThreadLocal.withInitial[Context]{ () =>
//    val tCtx = new Context()
//    tCtx
//  }


  //  val solver: ThreadLocal[Solver] = ThreadLocal.withInitial(() => {
  //    makeSolver()
  //  })
  override def setSeed(v: Int)(implicit zctx: Z3SolverCtx): Unit = {
    zctx.ctx.updateParamValue("random-seed",v.toString)
  }

  override def getSolverCtx: Z3SolverCtx = {
    val ctx = threadLocalCtx.get()
//    println(s"ctx: ${System.identityHashCode(ctx)}")
    ctx
  }

  private def addrSort(implicit zCtx:Z3SolverCtx) = zCtx.ctx.mkUninterpretedSort("Addr")

  override def checkSAT()(implicit zCtx:Z3SolverCtx): Boolean = {
    val res = zCtx.solver.check()
    interpretSolverOutput(res)
  }

  //TODO: push/pop may be causing "unreachable" issue
  override def push()(implicit zCtx:Z3SolverCtx): Unit = {
    zCtx.solver.push()
  }

  override def pop()(implicit zCtx:Z3SolverCtx): Unit = {
    zCtx.solver.pop()
  }
  override def reset()(implicit zCtx:Z3SolverCtx):Unit = {
    zCtx.reset()
  }

  override protected def mkEq(lhs: AST, rhs: AST)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkEq(lhs.asInstanceOf[Expr[Sort]], rhs.asInstanceOf[Expr[Sort]])
  }

  override protected def mkNe(lhs: AST, rhs: AST)(implicit zCtx:Z3SolverCtx): AST =
    zCtx.ctx.mkNot(zCtx.ctx.mkEq(lhs.asInstanceOf[Expr[Sort]],rhs.asInstanceOf[Expr[Sort]]))

  override protected def mkLt(lhs: AST, rhs: AST)(implicit zCtx:Z3SolverCtx): AST =
    zCtx.ctx.mkLt(lhs.asInstanceOf[ArithExpr[ArithSort]],rhs.asInstanceOf[ArithExpr[ArithSort]])

  override protected def mkNot(o: AST)(implicit zCtx:Z3SolverCtx): AST = {
    o match {
      case v:BoolExpr if v.isTrue => mkBoolVal(boolVal = false)
      case v:BoolExpr if v.isFalse => mkBoolVal(boolVal = true)
      case v:BoolExpr => zCtx.ctx.mkNot(v)
      case _ => throw new IllegalStateException()
    }
  }

  override protected def mkAdd(lhs: AST, rhs: AST)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkAdd(lhs.asInstanceOf[ArithExpr[ArithSort]], rhs.asInstanceOf[ArithExpr[ArithSort]])
  }

  override protected def mkSub(lhs: AST, rhs: AST)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkSub(lhs.asInstanceOf[ArithExpr[ArithSort]], rhs.asInstanceOf[ArithExpr[ArithSort]])
  }


  override protected def mkAnd(lhs:AST, rhs:AST)(implicit zCtx:Z3SolverCtx):AST = {
    mkAnd(List(lhs,rhs))
  }

  override protected def mkAnd(t:List[AST])(implicit zCtx:Z3SolverCtx): AST = {
    // Simplify for debug
    // Note: in z3, and with no arguments returns true, this retains that behavior
    val t2 = t.filter{
      case v:BoolExpr => !v.isTrue
      case _ => true
    }

    if(t2.isEmpty) {
      mkBoolVal(boolVal = true)
    }else if(t2.size == 1){
      t2.head
    } else {
      val tb: Array[BoolExpr] = t2.map(_.asInstanceOf[BoolExpr]).toArray
      zCtx.ctx.mkAnd(tb: _*)
    }
  }

  override protected def mkOr(lhs: AST, rhs: AST)(implicit zCtx:Z3SolverCtx): AST =
    mkOr(List(lhs,rhs))

  override protected def mkOr(t: Iterable[AST])(implicit zCtx:Z3SolverCtx): AST = {
    // Simplify for debug - make z3 ast easier to inspect
    // Note: in z3, or with no arguments returns false, this retains that behavior
    val t2 = t.filter{
      case v:BoolExpr => !v.isFalse
      case _ => true
    }

    // Simplify for debug -
    if(t2.size == 1) {
      t2.head
    }else if(t2.nonEmpty) {
      val tb: Array[BoolExpr] = t2.map(_.asInstanceOf[BoolExpr]).toArray
      zCtx.ctx.mkOr(tb: _*)
    }else{
      mkBoolVal(false)
    }
  }

//  /**
//   * @param l list of boolean expressions
//   * @return boolean expression that is true iff exactly one expression in l is true
//   */
//  override protected def mkExactlyOneOf(l:List[AST])(implicit zCtx:Z3SolverCtx): AST = {
////    val ctx = zCtx.ctx
////    val oneorzero: Seq[Expr[Sort]] = l.map(lv =>
////      ctx.mkITE(lv.asInstanceOf[BoolExpr],ctx.mkInt(1),ctx.mkInt(0)).asInstanceOf[Expr[Sort]])
////    ctx.mkEq(ctx.mkAdd(oneorzero.toArray:_*), ctx.mkInt(1))
//    ???
//  }

  override protected def mkIntVal(i: Int)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkInt(i)
  }

  override protected def mkBoolVal(boolVal: Boolean)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkBool(boolVal)
  }

  override protected def mkIntVar(s: String)(implicit zCtx:Z3SolverCtx): AST = zCtx.ctx.mkIntConst(s)

  override protected def mkLenVar(s: String)(implicit zCtx: Z3SolverCtx): AST = zCtx.ctx.mkConst(s, indexSort)

  override protected def mkAddrVar(pv:PureVar)(implicit zCtx:Z3SolverCtx):AST =
    zCtx.ctx.mkFreshConst(mkPvName(pv), addrSort)



  override protected def fieldEquals(f: AST, t1 : AST, t2:AST)(implicit zCtx:Z3SolverCtx): AST = {
    assert(f.isInstanceOf[FuncDecl[UninterpretedSort]])
    assert(t1.isInstanceOf[Expr[UninterpretedSort]])
    assert(t2.isInstanceOf[Expr[UninterpretedSort]])
    f.asInstanceOf[FuncDecl[UninterpretedSort]]
      .apply(t1.asInstanceOf[Expr[UninterpretedSort]],t2.asInstanceOf[Expr[UninterpretedSort]])
  }

  override protected def dumpDbg[T](cont: () => T)(implicit zCtx: Z3SolverCtx): T = {
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

  private def interpretSolverOutput(status : Status)(implicit zCtx:Z3SolverCtx) : Boolean = status match {
    case Status.UNSATISFIABLE => false
    case Status.SATISFIABLE => true
    case Status.UNKNOWN =>
      val reason = zCtx.solver.getReasonUnknown
      val f = File(s"timeout_${System.currentTimeMillis() / 1000L}.z3")
      f.createFile()
      f.writeText(zCtx.solver.toString)
      f.append("\n(check-sat)")
      var failed = false
      // Sometimes the java solver fails, we fall back to calling the command line tool
      try {
        println("fallback command line solver")
        val stdout = BounderUtil.runCmdStdout(s"timeout 120 z3 ${f}")
        if (stdout.contains("unsat"))
          false
        else
          true
      }catch {
        case e:RuntimeException =>
          println(e.getMessage)
          failed = true
          throw new IllegalStateException(s"Z3 decidability or timeout issue--got Status.UNKNOWN: ${reason}, " +
            s"smt file: ${f.canonicalPath}")
      }finally {
        if(!failed) f.delete(swallowIOExceptions = true)
      }
  }

  override def explainWitness(messageTranslator: MessageTranslator,
                              pvMap: Map[PureVar, Option[AST]])(implicit zCtx: Z3SolverCtx): WitnessExplanation = {

    val ctx = zCtx.ctx
    //val model = zCtx.solver.getModel
    assert(messageTranslator.states.size == 1, "Explain witness only applicable with single state")
    val state = messageTranslator.states.head
    val pvSet = state.pureVars()
    val varPairs = BounderUtil.repeatingPerm[PureVar](_ => pvSet, 2).filter(a => a(0) != a(1))

    // val opt = ctx.mkOptimize()
    // val params = ctx.mkParams()
    // params.add("timeout", 15)
    // opt.setParameters(params)
    // zCtx.solver.getAssertions.foreach(a => opt.Add(a))
    // varPairs.foreach{
    //   case a::b::Nil =>
    //     opt.AssertSoft(mkNe(pvMap(a).get,pvMap(b).get).asInstanceOf[BoolExpr], 1, s"${a}_${b}")
    //   case _ => throw new IllegalStateException()
    // }

    // // Note: optimizer fails if quantifiers can't be simplified out
    // // Fall back to model created by non-optimizing solver
    // val res = opt.Check()
    // val model = if(res == Status.SATISFIABLE)
    //   opt.getModel
    // else if(res == Status.UNKNOWN)
    //   zCtx.solver.getModel
    // else
    //   throw new IllegalStateException("Mismatch between optimizing solver and normal solver")
    val model = zCtx.solver.getModel

    val ta = state.traceAbstraction
    val mv = ta.modelVars
    val rightOfArrow = ta.rightOfArrow

    val pvModelValues: Map[PureVar, Expr[UninterpretedSort]] = pvMap.map{
      case (pureVar, Some(ast)) =>
        (pureVar, model.eval(ast.asInstanceOf[Expr[UninterpretedSort]],true))
      case _ =>
        ???
    }
    val pvValues: Map[Expr[UninterpretedSort], Int] = pvModelValues.values.toSet.zipWithIndex.toMap
    val constFn = ctx.mkFuncDecl("constFn", addrSort, constSort)
    val constMap = messageTranslator.getConstMap()
    val pvv: PureVar => TVal = pvi => {
      val pv = pvModelValues(pvi)
      val isNull = constMap.contains(NullVal) && model.eval(mkEq(constFn.apply(pv),
        constMap(NullVal)).asInstanceOf[Expr[UninterpretedSort]], true).isTrue
      if(isNull)
        TNullVal
      else
        TAddr(pvValues(pv))
    }
    val pmv: String => TVal = v =>
      if(v == "_") T_ else
        pvv(ta.modelVars(v).asInstanceOf[PureVar])


    val trace = rightOfArrow.map{
      case LifeState.CLInit(sig) => TCLInit(sig)
      case LifeState.FreshRef(v) => TNew(pvv(mv(v).asInstanceOf[PureVar]))
      case LifeState.I(CBEnter, sig, vars) =>
        TMessage(CBEnter,AppMethod(sig.identifier, "", None), vars.map(v => pmv(v)))
      case LifeState.I(CBExit, sig, vars) =>
        TMessage(CBExit,AppMethod(sig.identifier, "", None), vars.map(v => pmv(v)))
      case LifeState.I(CIEnter, sig, vars) =>
        TMessage(CIEnter,FwkMethod(sig.identifier, ""), vars.map(v => pmv(v)))
      case LifeState.I(CIExit, sig, vars) =>
        TMessage(CIExit,FwkMethod(sig.identifier, ""), vars.map(v => pmv(v)))
    }

    WitnessExplanation(trace)
  }

  override def printDbgModel(messageTranslator: MessageTranslator,
                             traceAbstraction: Set[AbstractTrace], lenUID: String)(implicit zCtx:Z3SolverCtx): Unit = {
    printAbstSolution(zCtx.solver.getModel, messageTranslator, traceAbstraction, lenUID)
  }

  def printAbstSolution(model: Model, messageTranslator: MessageTranslator, traceAbstraction: Set[AbstractTrace],
                        lenUID: String)(implicit zCtx:Z3SolverCtx) {
    println(s"===model: $model")
    val ctx = zCtx.ctx
    traceAbstraction foreach { abs => {
      val uniqueID = System.identityHashCode(abs) + ""
      val len = mkLenVar(s"len_$lenUID").asInstanceOf[Expr[UninterpretedSort]]
      val indices = model.getSortUniverse(zCtx.ctx.mkUninterpretedSort("Uint"))
      val lte = indexLTE
      val sortedInd = indices.sortWith((e1,e2) =>
        model.eval(ctx.mkAnd(lte.apply(e1,e2), ctx.mkNot(ctx.mkEq(e1,e2))),true).isTrue)
      println("=indices=")
      sortedInd.zipWithIndex.foreach(i => println(s"${i._2} = ${i._1}"))

      println("=function decls=")
      model.getFuncDecls.map(println)

      println("=type fun=")
      val addr = model.getSortUniverse(zCtx.ctx.mkUninterpretedSort("Addr"))
//      val classTypes = model.getSortUniverse(zCtx.ctx.mkUninterpretedSort("ClassTypes"))
      val typeFun = model.getFuncDecls.find { f =>
        val name = f.getName.toString
        name.contains("addressToType")
      }
//      addr.foreach

      println("=trace solution=")
      var traceLen = 0
      while(model.eval(mkEq(sortedInd(traceLen),len).asInstanceOf[BoolExpr], true).isFalse){
        traceLen = traceLen+1
      }
      val traceFun = mkTraceFn(uniqueID).asInstanceOf[FuncDecl[UninterpretedSort]]
      val nameFun = messageTranslator.nameFun.asInstanceOf[FuncDecl[_]]
      val argFun = mkArgFun().asInstanceOf[FuncDecl[_]]
      def printTraceElement(index:Int, traceFn: FuncDecl[UninterpretedSort]):Unit = {
        println(s"$index : ${sortedInd(index)} :")
        val msgati = model.eval(traceFn.apply(sortedInd(index).asInstanceOf[Expr[UninterpretedSort]]), true)
        val mIter = messageTranslator.solverToIdentitySignature.filter{
          case (ast, _) => model.eval(mkEq(nameFun.apply(msgati), ast).asInstanceOf[BoolExpr],true).isTrue
        }
        val m = mIter.head._2

        if(m != "OTHEROTHEROTHER") {
          val iset = messageTranslator.iForZ3Name(m)
          val args = iset.head.lsVars.indices
            .map(index => model.eval(argFun.apply(zCtx.args(index), msgati), true)).mkString(",")

          println(s"$m " +
            s"args: $args")
        }else{
          println("Other Msg")
        }
      }
      println("=traceFun=")
      (0 until traceLen).map ( index => printTraceElement(index, traceFun))

      val arrowtfs = model.getFuncDecls.filter{decl =>
        decl.getName.toString.contains("tracefn_arrowtf")}
      arrowtfs.foreach{f =>
        println(s"=traceFunArrow: ${f.getName}=")
        sortedInd.indices.foreach{ i => printTraceElement(i,f.asInstanceOf[FuncDecl[UninterpretedSort]])}
      }
      println()

    }
    }
  }

  override protected def solverSimplify(t: AST,
                                        state:State,
                                        messageTranslator: MessageTranslator,
                                        logDbg:Boolean)(implicit zCtx:Z3SolverCtx): Option[AST] = {
    val solver = zCtx.solver
    solver.add(t.asInstanceOf[BoolExpr])
    val status: Status = solver.check()
    status match{
      case Status.SATISFIABLE =>
        if (logDbg) {
          println(s"Model: ${solver.getModel}")
          printAbstSolution(solver.getModel,messageTranslator,
            Set(state.traceAbstraction),
            "")
        }
        Some(t)
      case Status.UNKNOWN =>
        Some(t)
      case Status.UNSATISFIABLE =>
        if (logDbg) {
          println(s"Unsat core: ${solver.getUnsatCore.map(s=> s.toString).mkString(" AND \n")}")
        }
        None
    }
  }

  def typeSort(implicit zCtx:Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort("ClassTypes")
  def constSort(implicit zCtx:Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort("ConstVals")
  def localSort(implicit zCtx:Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort("Locals")
  def dynFieldSort(implicit zCtx:Z3SolverCtx):UninterpretedSort = zCtx.ctx.mkUninterpretedSort("DynField")
  private def equalToOneOf(e : Expr[Sort], vals : Array[Expr[Sort]])(implicit zCtx:Z3SolverCtx):BoolExpr = {
    val ctx = zCtx.ctx
    ctx.mkOr(vals.map(v => ctx.mkEq(e,v)):_*)
  }
  def equalToOneOfTypes(e: Expr[Sort], typeToSolverConst: Map[Int,AST],
                        types: Set[Int])(implicit zCtx:Z3SolverCtx):BoolExpr = {
    val solverTypes = types.map(typeToSolverConst).map(_.asInstanceOf[Expr[Sort]])
    equalToOneOf(e,solverTypes.toArray)
  }
  override protected def mkTypeConstraintForAddrExpr(typeFun: AST, typeToSolverConst:Map[Int,AST],
                                                     addr:AST, tc:Set[Int])(implicit zCtx:Z3SolverCtx): AST = {
    if(tc.isEmpty)
      mkBoolVal(true)
    else {
      equalToOneOfTypes(typeFun.asInstanceOf[FuncDecl[Sort]].apply(addr.asInstanceOf[Expr[Sort]]), typeToSolverConst, tc)
    }
  }
  override protected def createTypeFun()(implicit zCtx:Z3SolverCtx):AST = {
    val args: Array[Sort] = Array(addrSort)
    zCtx.ctx.mkFuncDecl("addressToType", args, typeSort)
  }

  // Model vars have the pred identity hash code appended since they are unique to each pred
  // "_" means we don't care what the value is so just make arbitrary int
  override protected def mkModelVar(s: String, predUniqueID:String)(implicit zCtx:Z3SolverCtx): AST = s match {
    case LSVar(s) =>
      zCtx.ctx.mkConst ("model_var_" + s + "_" + predUniqueID, addrSort)
    case LSAnyVal() =>
      zCtx.ctx.mkFreshConst ("_", addrSort)
    case _ => throw new IllegalArgumentException("mkModelVar expects variable or any.")
  }

  override protected def mkFreshIntVar(s:String)(implicit zCtx:Z3SolverCtx): AST =
    zCtx.ctx.mkFreshConst(s, zCtx.ctx.mkIntSort())

  /**
   * forall int in (min,max) condition is true
   * @param cond function from const to boolean expression
   */
  override protected def mkForallInt(min:AST, max:AST,cond: AST => AST)(implicit zCtx:Z3SolverCtx): AST = {
    val j = zCtx.ctx.mkFreshConst("j", zCtx.ctx.mkIntSort())
    val range = mkAnd(List(mkLt(min,j), mkLt(j,max)))
    zCtx.ctx.mkForall(Array(j), mkImplies(range,cond(j)).asInstanceOf[BoolExpr]
      ,1,null,null,null,null)
  }
  override protected def mkForallAddr(name:String, cond: AST=>AST)(implicit zCtx:Z3SolverCtx):AST = {
    assert(name != "_", "Wild card variables should not be quantified")
    val j: Expr[UninterpretedSort] = zCtx.ctx.mkFreshConst(name, addrSort)
    zCtx.ctx.mkForall(Array(j), cond(j).asInstanceOf[BoolExpr],1,null,null,null,null)
  }

  private def nameConstMap(name:Map[String,Option[AST]])(implicit zCtx:Z3SolverCtx):Map[String,AST] = {
    name.map{
      case (n,None) => n -> zCtx.ctx.mkFreshConst(n, addrSort).asInstanceOf[Expr[_]]
      case (n,Some(v)) => (n->v)
    }
  }
  override protected def mkForallAddr(name: Map[String,Option[AST]], cond: Map[String,AST] => AST, solverNames:Set[AST])
                                     (implicit zCtx:Z3SolverCtx): AST = {
    assert(!name.contains("_"), "Wild card variables should not be quantified")
    if(name.isEmpty){
      cond(Map())
    }else {
      val nameToAST = nameConstMap(name)
      val j = nameToAST.map{case (_,v) => v.asInstanceOf[Expr[UninterpretedSort]]}.toSet
      zCtx.ctx.mkForall((j ++ solverNames.map(_.asInstanceOf[Expr[UninterpretedSort]])).toArray,
        cond(nameToAST).asInstanceOf[Expr[BoolSort]], 1,
        null, null, null, null)
    }
  }


  override protected def mkExistsAddr(name:String, cond: AST=>AST)(implicit zCtx:Z3SolverCtx):AST = {
    assert(name != "_", "Wild card variables should not be quantified")
    val j = zCtx.ctx.mkFreshConst(name, addrSort)
    zCtx.ctx.mkExists(Array(j), cond(j).asInstanceOf[BoolExpr],1,null,null,null,null)
  }

  override protected def mkExistsAddr(name: Map[String, Option[AST]],
                                      cond: Map[String,AST] => AST, solverNames:Set[AST])
                                     (implicit zCtx:Z3SolverCtx): AST = {
    assert(!name.contains("_"), "Wild card variables should not be quantified")
    if(name.isEmpty){
      cond(Map())
    }else {
      val nameToAST = nameConstMap(name)
      val j = nameToAST.map{case (_,v) => v.asInstanceOf[Expr[UninterpretedSort]]}.toSet
      zCtx.ctx.mkExists((j ++ solverNames.map(_.asInstanceOf[Expr[UninterpretedSort]])).toArray,
        cond(nameToAST).asInstanceOf[Expr[BoolSort]], 1,
        null, null, null, null)
    }
  }

  /**
   * there exists an int in (min,max) such that condition is true
   * @param cond function from const to boolean expression
   * @return
   */
  protected def mkExistsInt(min:AST, max:AST, cond:AST=>AST)(implicit zCtx:Z3SolverCtx):AST = {
    val ctx = zCtx.ctx
    val j= ctx.mkFreshConst("i", ctx.mkIntSort()).asInstanceOf[ArithExpr[ArithSort]]
    val range = mkAnd(List(mkLt(min,j), mkLt(j,max)))
    ctx.mkExists(Array(j), mkAnd(range,cond(j)).asInstanceOf[BoolExpr]
      ,1,null,null,null,null)
  }

  override protected def mkImplies(t: AST, t1: AST)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkImplies(t.asInstanceOf[BoolExpr], t1.asInstanceOf[BoolExpr])
  }

  override protected def mkTraceFn(uid: String)(implicit zCtx:Z3SolverCtx): AST = {
    val ctx = zCtx.ctx
    ctx.mkFuncDecl(s"tracefn_$uid", indexSort, ctx.mkUninterpretedSort("Msg"))
  }

  override protected def mkFreshTraceFn(uid: String)(implicit zCtx:Z3SolverCtx): AST = {
    val ctx = zCtx.ctx
    ctx.mkFreshFuncDecl(s"tracefn_$uid", Array(indexSort), ctx.mkUninterpretedSort("Msg"))
  }

  override protected def mkLocalFn(uid: String)(implicit zCtx: Z3SolverCtx): FuncDecl[_] = {
    zCtx.ctx.mkFuncDecl(s"localfn_${uid}", localSort, addrSort)
  }

  override protected def mkDynFieldFn(uid:String, fieldName:String)(implicit zCtx:Z3SolverCtx):FuncDecl[_] = {
    val addrAddr:Array[Sort] = Array(addrSort,addrSort)
    val fun = zCtx.ctx.mkFuncDecl(s"dynField_${fieldName}_${uid}", addrAddr, zCtx.ctx.mkBoolSort)
    if(!zCtx.initializedFieldFunctions.contains(fieldName)){
      val a1 = zCtx.ctx.mkFreshConst("a1", addrSort)
      val a2 = zCtx.ctx.mkFreshConst("a2", addrSort)
      val a3 = zCtx.ctx.mkFreshConst("a3", addrSort)

      val b = zCtx.ctx.mkForall(Array(a1,a2,a3),
        mkImplies(mkAnd(fun.apply(a1,a2), fun.apply(a1,a3)), mkEq(a2,a3)).asInstanceOf[BoolExpr],
        1, null, null, null, null )
      zCtx.mkAssert(b)
      zCtx.initializedFieldFunctions.add(fieldName)
    }
    fun
  }

  override protected def mkINameFn()(implicit zCtx:Z3SolverCtx): AST = {
    val ctx = zCtx.ctx
    ctx.mkFuncDecl(s"namefn_", ctx.mkUninterpretedSort("Msg"), ctx.mkUninterpretedSort("inames"))
  }
  private def mkArgSort()(implicit zCtx:Z3SolverCtx): UninterpretedSort = {
    zCtx.ctx.mkUninterpretedSort("Arguments")
  }
  private def mkArgs(n:Int)(implicit zCtx:Z3SolverCtx):Array[Expr[UninterpretedSort]] = {
    val argIds = (0 until n).map(v => zCtx.ctx.mkFreshConst(s"arg___${v}", mkArgSort())).toArray
    val argf = zCtx.ctx.mkConst("argf__", mkArgSort())
    val constraint: Expr[BoolSort] = mkOr(argIds.map(argId => mkEq(argf, argId) ).toList).asInstanceOf[Expr[BoolSort]]
    zCtx.mkAssert(zCtx.ctx.mkForall(Array(argf), constraint, 1, null,null,null,null))
    zCtx.mkAssert(zCtx.ctx.mkDistinct(argIds:_*))
    argIds
  }
  override protected def mkMaxMsgUint(n:Int)(implicit zCtx: Z3SolverCtx):AST = {
    val ctx = zCtx.ctx
    val msgSort = ctx.mkUninterpretedSort("Msg")
    val varMsg = ctx.mkFreshConst("someMsg", msgSort)
    val msgIDs = (0 until n).map(n => ctx.mkFreshConst(s"msg_$n", msgSort)).toArray
    val oneOf =  msgIDs
      .map(c => ctx.mkEq(varMsg, c))
    val uintIDs = (0 until (n + 5)).map(n => ctx.mkFreshConst(s"uint_$n", indexSort))
    val varUInt = ctx.mkFreshConst("someUint", indexSort)
    val oneOfUint = uintIDs.map(u => ctx.mkEq(varUInt, u))
    val msgU = mkAnd(ctx.mkForall(Array(varMsg), ctx.mkOr(oneOf:_*),
      1,null,null,null,null),
      ctx.mkDistinct(msgIDs:_*))
    val uintU = mkAnd(
      ctx.mkForall(Array(varUInt), ctx.mkOr(oneOfUint:_*), 1,null,null,null,null),
      ctx.mkDistinct(uintIDs:_*)
    )
    mkAnd(msgU, uintU)
    ??? //TODO: This seems unneeded, remove?
  }
  override protected def mkArgFun()(implicit zCtx:Z3SolverCtx): AST = {
    if(zCtx.args.isEmpty){
      zCtx.args = mkArgs(MAX_ARGS)
    }
    val ctx = zCtx.ctx
    val argSort:Sort = mkArgSort()
    ctx.mkFuncDecl(s"argfun_", Array(argSort, ctx.mkUninterpretedSort("Msg")), addrSort)
  }

//  override protected def mkIsNull(addr:AST)(implicit zCtx:Z3SolverCtx): AST = {
//    val ctx = zCtx.ctx
//    val isNullFun = ctx.mkFuncDecl("isNullFn", addrSort, ctx.mkBoolSort())
//    isNullFun.apply(addr.asInstanceOf[Expr])
//  }
//
//  override protected def mkIntValueConstraint(addr:AST)(implicit zCtx:Z3SolverCtx): AST = {
//    val ctx = zCtx.ctx
//    val intConstFn = ctx.mkFuncDecl("intConstFn", addrSort, ctx.mkIntSort())
//    intConstFn.apply(addr.asInstanceOf[Expr])
//  }

  protected def mkConstValueConstraint(addr:AST)(implicit zCtx:Z3SolverCtx):AST = {
    val ctx = zCtx.ctx
    val constFn = ctx.mkFuncDecl("constFn", addrSort, constSort)
    constFn.apply(addr.asInstanceOf[Expr[UninterpretedSort]])
  }

  override protected def mkIName(enum:AST, enumNum:Int)(implicit zCtx:Z3SolverCtx): AST = {
    enum.asInstanceOf[EnumSort[_]].getConst(enumNum)
  }

  override protected def mkUT(name: String, types: List[String])(implicit zCtx:Z3SolverCtx): Map[String,AST] = {
    val ctx = zCtx.ctx
//    ctx.mkEnumSort(name, types.toArray:_*)
    val sort = ctx.mkUninterpretedSort(name)
    val tmap:Map[String,AST] = types.map(t => (t -> ctx.mkConst(t, sort))).toMap
    if(!zCtx.uninterpretedTypes.contains(name)){
      val u = ctx.mkFreshConst("u", sort)
      val eachT = mkOr(tmap.map{case (_,v) => mkEq(u, v)}).asInstanceOf[BoolExpr]
      zCtx.mkAssert(ctx.mkForall(Array(u), eachT, 1, null,null,null,null))
      val tOnly = tmap.map{case (_,v) => v.asInstanceOf[Expr[UninterpretedSort]]}
      zCtx.mkAssert(ctx.mkDistinct(tOnly.toArray:_*))
    }
    tmap
  }

//  override protected def getEnumElement(enum:(AST, Map[String,AST]), i: String)(implicit zCtx:Z3SolverCtx): AST = {
////    enum.asInstanceOf[EnumSort[_]].getConst(i)
//    enum._2(i)
//  }

  override protected def mkTraceConstraint(traceFun: AST, index: AST)(implicit zCtx:Z3SolverCtx): AST = {
    traceFun.asInstanceOf[FuncDecl[_]].apply(index.asInstanceOf[Expr[UninterpretedSort]])
  }

  override protected def mkNameConstraint(nameFun: AST, msg: AST)(implicit zCtx:Z3SolverCtx): AST = {
    nameFun.asInstanceOf[FuncDecl[_]].apply(msg.asInstanceOf[Expr[Sort]])
  }

  override protected def mkArgConstraint(argFun: AST, argIndex: Int, msg: AST)(implicit zCtx:Z3SolverCtx): AST = {
    assert(msg.isInstanceOf[Expr[UninterpretedSort]])
    assert(zCtx.args.nonEmpty, "Must call mkArgFun before mkArgConstraint")
    assert(zCtx.args.length > argIndex, s"More than ${MAX_ARGS} arguments not supported. Got arg index ${argIndex}.")
    val arg = zCtx.args(argIndex)
    mkArgConstraint(argFun, arg, msg.asInstanceOf[Expr[UninterpretedSort]])
  }

  private def mkArgConstraint(argFun:AST,
                              arg:Expr[UninterpretedSort],
                              msg:Expr[UninterpretedSort])(implicit zCtx:Z3SolverCtx):AST = {
    argFun.asInstanceOf[FuncDecl[_]].apply(arg,
      msg)
  }

  override protected def mkExistsArg(argFun: AST, msg: AST, pred: AST => AST)(implicit zCtx:Z3SolverCtx): AST = {
    //    val argFun = mkArgFun()
    //    val argConst = zCtx.ctx.mkFreshConst("argConst", getArgSort())
    //    val constraint = pred(mkArgConstraint(argFun,
    //      argConst, msg.asInstanceOf[Expr[UninterpretedSort]])).asInstanceOf[BoolExpr]
    //    zCtx.ctx.mkExists(Array(argConst), constraint, 1,null,null,null,null)
    val ctx = zCtx.ctx
    val argIs = zCtx.args.map(arg =>
      pred(argFun.asInstanceOf[FuncDecl[UninterpretedSort]].apply(
        arg,msg.asInstanceOf[Expr[UninterpretedSort]])).asInstanceOf[BoolExpr] )
    ctx.mkOr(argIs:_*)
  }

  override protected def mkAddrConst(i: Int)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkConst(s"addr_const$i", addrSort)
  }


  override protected def mkDistinct(pvList: Iterable[PureVar],pvMap:Map[PureVar,AST])(implicit zCtx:Z3SolverCtx): AST = {
    if(pvList.isEmpty){
      mkBoolVal(boolVal = true)
    }else {
      zCtx.ctx.mkDistinct(pvList.map { a =>
        pvMap(a).asInstanceOf[Expr[UninterpretedSort]]
      }.toArray: _*)
    }
  }

  override protected def mkDistinctT(pvList: Iterable[AST])(implicit zCtx:Z3SolverCtx): AST = {
    if(pvList.isEmpty){
      mkBoolVal(boolVal = true)
    }else {
      zCtx.ctx.mkDistinct(pvList.map { a => a.asInstanceOf[Expr[UninterpretedSort]] }.toArray: _*)
    }
  }

  override protected def encodeTypeConsteraints: StateTypeSolving = persistentConstraints.getUseZ3TypeSolver

  override protected def persist: ClassHierarchyConstraints = persistentConstraints



  override protected def mkTypeConstraints(types: Set[Int])(implicit zCtx: Z3SolverCtx): (AST, Map[Int, AST]) = {
    val ctx = zCtx.ctx
    val typeMap = types.map(t => (t-> ctx.mkConst(s"type_$t", typeSort))).toMap
    val allConstraints = typeMap.map{case (_,c) => c}
    val unique = mkDistinctT(allConstraints)
    (unique, typeMap)
  }

  override protected def mkLocalConstraint(localIdent:AST, equalTo: AST, uid:String)
                                          (implicit zCtx: Z3SolverCtx): AST = {
    val fn = mkLocalFn(uid)
    mkEq(fn.apply(localIdent.asInstanceOf[Expr[UninterpretedSort]]), equalTo)
  }

  override protected def mkDynFieldConstraint(base: AST, fieldName: String, equalTo: AST, uid:String)
                                             (implicit zCtx: Z3SolverCtx): AST = {
    val fn = mkDynFieldFn(uid, fieldName)
    val appFun = fn.apply(base.asInstanceOf[Expr[Sort]], equalTo.asInstanceOf[Expr[Sort]])
//    mkEq(appFun, equalTo)
    appFun
  }

  override protected def mkStaticFieldConstraint(clazz:String, fieldName:String, equalTo:AST, uid:String)
                                             (implicit zCtx:Z3SolverCtx):AST = {
    val staticField = zCtx.ctx.mkConst(s"staticField___${clazz}___${fieldName}", addrSort) //.mkFuncDecl(s"dynField_${fieldName}_${uid}", addrSort)
    mkEq(staticField, equalTo)
  }

  def localToName(local:(String,Int)):String = s"local_${local._1}____${local._2}"
  override protected def mkLocalDomain(locals: Set[(String, Int)])
                                      (implicit zCtx: Z3SolverCtx): (AST, Map[(String, Int), AST]) = {
    val ctx = zCtx.ctx
    val localMap = locals.map(t => (t-> ctx.mkConst(localToName(t), localSort))).toMap
    val allConstraints: immutable.Iterable[Expr[UninterpretedSort]] = localMap.map{case (_,c) => c}
    val unique = mkDistinctT(allConstraints)
    (unique, localMap)
  }

  def fieldToName(fld:String):String = {
    s"field_${fld}"
  }

  protected def mkConstConstraintsMap(pvs: Set[PureVal])(implicit zCtx: Z3SolverCtx): (AST, Map[PureVal, AST]) = {
    val ctx = zCtx.ctx
    val constMap = pvs.flatMap(t => t.z3Tag.map(tag => (t-> ctx.mkConst(s"const_${tag}", constSort)))).toMap
    val allConstraints: immutable.Iterable[Expr[UninterpretedSort]] = constMap.map{case (_,c) => c}
    val unique = mkDistinctT(allConstraints)
    (unique, constMap)
  }

  def indexSort(implicit zCtx: Z3SolverCtx):UninterpretedSort = {
    zCtx.ctx.mkUninterpretedSort("Uint")
  }

  private def indexLTE(implicit zCtx: Z3SolverCtx): FuncDecl[BoolSort] = {
    val ctx = zCtx.ctx
    val indexIndex:Array[Sort] = Array(indexSort, indexSort)
    val lte = ctx.mkFuncDecl("indexLTE", indexIndex, zCtx.ctx.mkBoolSort)
    val zero = mkZeroIndex.asInstanceOf[Expr[UninterpretedSort]]
    if(!zCtx.indexInitialized){
      // Total ordering encoding used from: https://dl.acm.org/doi/pdf/10.1145/3140568
      // Paxos Made EPR: Decidable Reasoning about DistributedProtocols
      // figure 1
      // ** less than is transitive
      val x = ctx.mkFreshConst("x",indexSort)
      val y = ctx.mkFreshConst("y",indexSort)
      val z = ctx.mkFreshConst("z",indexSort)
      //forall x . x≤x
      zCtx.mkAssert(ctx.mkForall(Array(x), lte.apply(x,x), 1,null,null,null,null))

      // forall x,y,z. x≤y /\ y≤z => x≤z
      val trans: BoolExpr = mkImplies(mkAnd(lte.apply(x,y), lte.apply(y,z)), lte.apply(x,z)).asInstanceOf[BoolExpr]
      val b = ctx.mkForall(Array(x,y,z), trans, 1, null, null, null, null )
      zCtx.mkAssert(b)

      //forall x,y. x≤y /\ y≤x => y = x
      zCtx.mkAssert(ctx.mkForall(Array(x,y), ctx.mkImplies(ctx.mkAnd(lte.apply(x,y), lte.apply(y,x)), ctx.mkEq(x,y)),
        1,null,null,null,null))

      //forall x,y. x≤y \/ y≤x
      zCtx.mkAssert(ctx.mkForall(Array(x,y), ctx.mkOr(lte.apply(x,y), lte.apply(y,x)),
        1,null,null,null,null))


      // ** All indices are greater than or equal to zero
      // forall x. zero ≤ x
      val zeroLTE:BoolExpr = lte.apply(zero, x).asInstanceOf[BoolExpr]
      zCtx.mkAssert(ctx.mkForall(Array(x), zeroLTE, 1, null, null, null, null))
      zCtx.indexInitialized = true
    }

    lte
  }
  override protected def mkForallIndex(min: AST, max: AST, cond: AST => AST)(implicit zCtx: Z3SolverCtx): AST = {
    val min_ = min.asInstanceOf[Expr[UninterpretedSort]]
    val max_ = max.asInstanceOf[Expr[UninterpretedSort]]
    val ctx = zCtx.ctx
    val lte = indexLTE
    val j = ctx.mkFreshConst("j", indexSort)
    val range = mkAnd(lte.apply(min_,j), mkAnd(lte.apply(j, max_), mkNot(mkEq(j,max_))))
    ctx.mkForall(Array(j), mkImplies(range, cond(j)).asInstanceOf[BoolExpr],
      1,null,null,null,null)
  }

  override protected def mkExistsIndex(min: AST, max: AST, cond: AST => AST)(implicit zCtx: Z3SolverCtx): AST = {
    val min_ = min.asInstanceOf[Expr[UninterpretedSort]]
    val max_ = max.asInstanceOf[Expr[UninterpretedSort]]
    val ctx = zCtx.ctx
    val lte = indexLTE
    val j = ctx.mkFreshConst("j", indexSort)
    val range = mkAnd(lte.apply(min_,j), mkAnd(lte.apply(j, max_), mkNot(mkEq(j,max_))))
    ctx.mkExists(Array(j), mkAnd(range, cond(j)).asInstanceOf[BoolExpr],
      1,null,null,null,null)
  }

  override protected def mkForallIndex(cond: AST => AST)(implicit zCtx:Z3SolverCtx):AST = {
    val ctx = zCtx.ctx
    val j = ctx.mkFreshConst("j", indexSort)
    ctx.mkForall(Array(j), cond(j).asInstanceOf[BoolExpr],
      1,null,null,null,null)
  }

  override protected def mkLTEIndex(ind1: AST, ind2: AST)(implicit zCtx: Z3SolverCtx): AST = {
    val lt = indexLTE
    lt.apply(ind1.asInstanceOf[Expr[UninterpretedSort]],ind2.asInstanceOf[Expr[UninterpretedSort]])
  }
  override protected def mkLTIndex(ind1: AST, ind2: AST)(implicit zCtx: Z3SolverCtx): AST = {
    mkAnd(mkLTEIndex(ind1,ind2), mkNot(mkEq(ind1,ind2)))
  }

  /**
   * create a fresh variable that is ind+1
   * @param ind target index
   * @param zCtx solver context
   * @return (assertion that fresh var is ind+1, fresh var)
   */
  override protected def mkAddOneIndex(ind: AST)(implicit zCtx: Z3SolverCtx): (AST,AST) = {
    val ctx = zCtx.ctx
    val lte = indexLTE
    val indNext = zCtx.ctx.mkFreshConst("indNext", indexSort)
    val other = zCtx.ctx.mkFreshConst("other", indexSort)
    val indt = ind.asInstanceOf[Expr[UninterpretedSort]]
    val assert = mkAnd(List(
      lte.apply(indt,indNext),
      ctx.mkNot(ctx.mkEq(ind.asInstanceOf[Expr[UninterpretedSort]],indNext)),
      ctx.mkForall(Array(other), ctx.mkOr(lte.apply(other,indt), lte.apply(indNext, other)),
        1,null,null,null,null)
    ))
    (assert,indNext)
  }

  override protected def mkZeroIndex()(implicit zCtx: Z3SolverCtx): AST = {
    zCtx.ctx.mkConst("ZeroInd", indexSort)
  }
  override protected def mkMaxInd(ind:AST)(implicit zCtx: Z3SolverCtx):Unit = {
    val lte = indexLTE
    val indt = ind.asInstanceOf[Expr[UninterpretedSort]]
    val other = zCtx.ctx.mkFreshConst("other", indexSort)
    val ctx = zCtx.ctx
    zCtx.mkAssert(ctx.mkForall(Array(other), lte.apply(other, indt), 1,null,null,null,null))
  }
  override protected def mkAllArgs(msg: AST, pred: AST => AST)(implicit zCtx:Z3SolverCtx): AST = {
    //    val argFun = mkArgFun()
    //    val argConst:Expr[UninterpretedSort] = zCtx.ctx.mkFreshConst("argConst", getArgSort())
    //    val constraint = pred(mkArgConstraint(argFun, argConst,
    //      msg.asInstanceOf[Expr[UninterpretedSort]])).asInstanceOf[BoolExpr]
    //    zCtx.ctx.mkForall(Array(argConst), constraint, 1,null,null,null,null)
    val argFun = mkArgFun()
    val ctx = zCtx.ctx
    val argIs = zCtx.args.map(arg =>
      pred(argFun.asInstanceOf[FuncDecl[UninterpretedSort]].apply(
        arg,msg.asInstanceOf[Expr[UninterpretedSort]])).asInstanceOf[BoolExpr] )
    ctx.mkAnd(argIs:_*)
  }
  override protected def encodeRef(v: AST, traceFn: AST, traceLen: AST)(implicit zCtx: Z3SolverCtx): AST = {
    val ctx = zCtx.ctx
    val argFun = mkArgFun().asInstanceOf[FuncDecl[UninterpretedSort]]
    // forall index method, seems to cause timeouts
    //    val tf = traceFn.asInstanceOf[FuncDecl[UninterpretedSort]]
    //    mkForallIndex{ind =>
    //      val msg = tf.apply(ind.asInstanceOf[Expr[UninterpretedSort]])
    ////      mkImplies( mkAnd(mkLTEIndex(mkZeroIndex(), ind),mkLTIndex(ind,traceLen)),
    //        mkAllArgs(msg, {arg => mkNot(mkEq(v,arg))})
    ////      )
    //    }
    val m = ctx.mkConst("allMsg", ctx.mkUninterpretedSort("Msg"))
    val v_ = v.asInstanceOf[Expr[UninterpretedSort]]
    val pred:BoolExpr = ctx.mkAnd(
      zCtx.args.map(arg =>
        ctx.mkNot(ctx.mkEq(
            argFun.apply(arg,m),v_))):_*)
    ctx.mkForall(Array(m), pred, 1, null,null,null,null)
  }
}
