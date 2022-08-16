package edu.colorado.plv.bounder.solver

import better.files.File
import com.microsoft.z3._
import com.microsoft.z3.enumerations.Z3_ast_print_mode
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppMethod, CBEnter, CBExit, CIEnter, CIExit, FwkMethod, TAddr, TCLInit, TMessage, TNew, TNullVal, TVal, T_, TraceElement, WitnessExplanation}
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, NullVal, PureExpr, PureVal, PureVar, State, TopVal}
import org.slf4j.{Logger, LoggerFactory}

import scala.collection.immutable
import scala.collection.mutable

case class Z3SolverCtx(timeout:Int, randomSeed:Int) extends SolverCtx[AST] {
  private var ictx = new Context()
  val checkStratifiedSets = false // set to true to check EPR stratified sets (see Paxos Made EPR, Padon OOPSLA 2017)
  private var isolver:Solver = ictx.mkSolver()
  val initializedFieldFunctions : mutable.HashSet[String] = mutable.HashSet[String]()
  var indexInitialized:Boolean = false
  val uninterpretedTypes : mutable.HashSet[String] = mutable.HashSet[String]()
  val sortEdges = mutable.HashSet[(String,String)]()
  var acquired:Option[Long] = None
  private var zeroInitialized:Boolean = false
  def initializeZero:Unit ={
    zeroInitialized = true
  }
  def isZeroInitialized:Boolean = zeroInitialized
  def ctx:Context ={
    val currentThread:Long = Thread.currentThread().getId
    assert(acquired.isDefined)
    assert(acquired.get == currentThread)
    ictx
  }
  def solver:Solver = {
    val currentThread:Long = Thread.currentThread().getId
    assert(acquired.isDefined)
    assert(acquired.get == currentThread)
    isolver
  }


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
    val currentThread:Long = Thread.currentThread().getId
    assert(acquired.isDefined)
    assert(acquired.get == currentThread)
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
  private def makeSolver(timeout:Int, newRandomSeed:Option[Int]):Solver = this.synchronized{
    val solver = ctx.mkSolver
//    val solver = ctx.mkSimpleSolver()
    val params = ctx.mkParams()
    params.add("timeout", timeout)
    params.add("logic", "AUFLIA")
    newRandomSeed.foreach { rs =>
      params.add("random-seed", rs + randomSeed)
    }
    // params.add("threads", 4) Note: threads cause weird decidability issue

    // set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)

    //TODO: does this get rid of the "let" statements when printing?
    //    ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_LOW_LEVEL)
    solver.setParameters(params)
    solver
  }
  def release(): Unit = this.synchronized{
    //    assert(!detectCycle(sortEdges.toSet), "Quantifier Alternation Exception") //TODO:  remove after dbg
    // sortEdges.clear()

//    println(s"reset ctx: ${System.identityHashCode(this)}")
//    if(!acquired.isDefined) {
//      assert(acquired.isDefined)
//    }
    if(acquired.isDefined) {
      val currentThread: Long = Thread.currentThread().getId
      assert(acquired.get == currentThread)
      acquired = None
      ictx.close()
      isolver = null
      zeroInitialized = false
      indexInitialized = false
      initializedFieldFunctions.clear()
    }
//    Thread.sleep(100)
  }

  override def acquire(randomSeed:Option[Int]): Unit = {
    val currentThread:Long = Thread.currentThread().getId

    assert(acquired.isEmpty)
    acquired = Some(currentThread)
    initializedFieldFunctions.clear()
    indexInitialized = false
    uninterpretedTypes.clear()
//    ictx.close()
    ictx = new Context()
    isolver = makeSolver(timeout, randomSeed)
  }
}
class Z3StateSolver(persistentConstraints: ClassHierarchyConstraints, timeout:Int = 30000,
                    randomSeed:Int=3578,
                    defaultOnSubsumptionTimeout: Z3SolverCtx=> Boolean = _ => false,
                    pushSatCheck:Boolean = true
                   ) extends StateSolver[AST,Z3SolverCtx] {
//  private val MAX_ARGS = 10

  override def iDefaultOnSubsumptionTimeout(implicit zCtx:Z3SolverCtx): Boolean = this.defaultOnSubsumptionTimeout(zCtx)
//  private val threadLocalCtx: ThreadLocal[Z3SolverCtx] = ThreadLocal.withInitial( () => Z3SolverCtx(timeout,randomSeed))
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
  private val iCtx = Z3SolverCtx(timeout,randomSeed)
  override def getSolverCtx: Z3SolverCtx = {
//    val ctx = threadLocalCtx.get()
//    ctx
    iCtx
  }

  def initializeAllAxioms(messageTranslator: MessageTranslator)(implicit zCtx: Z3SolverCtx):Unit = {
    if(!zCtx.indexInitialized)
      initializeOrderAxioms(messageTranslator)
    if(!zCtx.isZeroInitialized)
      initializeZeroAxioms(messageTranslator)
    if(zCtx.initializedFieldFunctions.isEmpty)
      initializeFieldAxioms(messageTranslator)
  }
  override def solverString(messageTranslator: MessageTranslator)(implicit zCtx: Z3SolverCtx):String = {
    //initializeAllAxioms(messageTranslator)
    zCtx.solver.toString
  }

  override def checkSAT(messageTranslator: MessageTranslator,
                        axioms: List[MessageTranslator => Unit])(implicit zCtx: Z3SolverCtx): Boolean ={
    if(pushSatCheck)
      checkSatPush(messageTranslator, axioms)
    else
      checkSATOne(messageTranslator, axioms)

  }
  override def checkSatPush(messageTranslator: MessageTranslator,
                            axioms: List[MessageTranslator => Unit])(implicit zCtx:  Z3SolverCtx): Boolean = {
    val res: Status = zCtx.solver.check()

    val interp = (res,axioms) match {
      case (Status.UNSATISFIABLE, _) =>
        // Already unsatisfiable, no need to add axioms
        false
      case (Status.SATISFIABLE, h::t) =>
        zCtx.solver.push()
        h(messageTranslator)
        checkSatPush(messageTranslator, t)
      case (Status.UNKNOWN, h::t) =>
        zCtx.solver.push()
        h(messageTranslator)
        checkSatPush(messageTranslator, t)
      case (Status.SATISFIABLE, Nil) =>
        // No more axioms to try
        true
      case (Status.UNKNOWN, Nil) =>
        throw new IllegalStateException("Unknown, no more axioms, failure.")
    }
    interp
  }

  override def checkSATOne(messageTranslator: MessageTranslator,
                        axioms: List[MessageTranslator => Unit])(implicit zCtx:Z3SolverCtx): Boolean = {
    axioms.foreach{ax => ax(messageTranslator)}
    val useCmd = false
    if(useCmd) {
      lazy val timeoutS = timeout.toString
      File.temporaryFile().apply{ f =>
        println(s"file: $f")
        f.writeText(zCtx.solver.toString)
        f.append("\n(check-sat)")
        // Sometimes the java solver fails, we fall back to calling the command line tool
        try {
          val stdout = BounderUtil.runCmdStdout(s"timeout $timeoutS z3 ${f}")
          if(stdout.contains("unknown")){
            throw new RuntimeException()
          }
          val isSat = !stdout.contains("unsat")
          assert(stdout.contains("sat"), s"Malformed z3 output: ${stdout}")
          isSat
        } catch {
          case e: RuntimeException =>
            println(e.getMessage)
            val f2 = File(s"timeout_${System.currentTimeMillis()}.z3")
            if(f2.exists()) {
              println(s"deleting existing file ${f2}")
              f2.delete()
            }
            f.copyTo(f2)
            throw new IllegalStateException(s"Command line timeout." +
              s"smt file: ${f2.canonicalPath}")
        }
      }
    } else {
      try {
        val res = zCtx.solver.check()
        val interp = interpretSolverOutput(res)
        interp
      } catch {
        case e: IllegalArgumentException =>
            println(s"timeout: ${e.getMessage}")
            throw e
//          println(s"Fallback from z3 exception: ${e}")
//          if(!useCmd)
//            checkSAT(useCmd = true)
//          else
//            throw new IllegalStateException(e.getMessage)
      }
    }
  }

  //TODO: push/pop may be causing "unreachable" issue
  override def push()(implicit zCtx:Z3SolverCtx): Unit = {
    zCtx.solver.push()
  }

  override def pop()(implicit zCtx:Z3SolverCtx): Unit = {
    zCtx.solver.pop()
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

  override protected def mkIntVal(i: Int)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkInt(i)
  }

  override protected def mkBoolVal(boolVal: Boolean)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkBool(boolVal)
  }

  override protected def mkLenVar(s: String)(implicit zCtx: Z3SolverCtx): AST = zCtx.ctx.mkConst(s, msgSort)

  override protected def mkAddrVar(pv:PureVar)(implicit zCtx:Z3SolverCtx):AST =
    zCtx.ctx.mkFreshConst(mkPvName(pv), addrSort)

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
//      val f = File(s"timeout_${System.currentTimeMillis() / 1000L}.z3")
//      f.createFile()
//      f.writeText(zCtx.solver.toString)
//      f.append("\n(check-sat)")
      throw new IllegalArgumentException(s"status unknown, reason: ${reason}")
  }

  override def explainWitness(messageTranslator: MessageTranslator,
                              pvMap: Map[PureVar, AST])(implicit zCtx: Z3SolverCtx): WitnessExplanation = {
    //TODO: this seems to be broken, but we don't really use it for anything?
    ??? //TODO: update with set tracefn
    val ctx = zCtx.ctx
    assert(messageTranslator.states.size == 1, "Explain witness only applicable with single state")
    val state = messageTranslator.states.head
    val pvSet = state.pureVars()
    val varPairs = BounderUtil.repeatingPerm[PureVar](_ => pvSet, 2).filter(a => a(0) != a(1))

    val model = zCtx.solver.getModel

    val ta = state.traceAbstraction
    val mv = ta.modelVars
    val rightOfArrow = ta.rightOfArrow

    val pvModelValues: Map[PureVar, Expr[UninterpretedSort]] = pvMap.map{
      case (pureVar, ast) =>
        (pureVar, model.eval(ast.asInstanceOf[Expr[UninterpretedSort]],true))
    }
    val pvValues: Map[Expr[UninterpretedSort], Int] = pvModelValues.values.toSet.zipWithIndex.toMap
    val constFn: FuncDecl[UninterpretedSort] = ctx.mkFuncDecl("constFn", addrSort, constSort)
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

    val pmv: PureExpr => TVal = {
      case p:PureVar => pvv(p)
      case TopVal => T_
      case v => throw new IllegalArgumentException(s"Undefined model variable ${v}")
    }
    //    val pmv: String => TVal = v =>
    //      if(v == "_") T_ else {
    //        if(ta.modelVars.contains(v))
    //          pvv(ta.modelVars(v).asInstanceOf[PureVar])
    //        else throw new IllegalArgumentException(s"Undefined model variable ${v}, did you quantify a void value?")
    //      }


    val trace = rightOfArrow.map{
      case LifeState.CLInit(sig) => TCLInit(sig)
      case LifeState.FreshRef(v) => TNew(pvv(mv(v).asInstanceOf[PureVar]))
      case LifeState.Once(CBEnter, sig, vars) =>
        TMessage(CBEnter,AppMethod(sig.identifier, "", None), vars.map(v => pmv(v)))
      case LifeState.Once(CBExit, sig, vars) =>
        TMessage(CBExit,AppMethod(sig.identifier, "", None), vars.map(v => pmv(v)))
      case LifeState.Once(CIEnter, sig, vars) =>
        TMessage(CIEnter,FwkMethod(sig.identifier, ""), vars.map(v => pmv(v)))
      case LifeState.Once(CIExit, sig, vars) =>
        TMessage(CIExit,FwkMethod(sig.identifier, ""), vars.map(v => pmv(v)))
    }

    WitnessExplanation(trace)
  }

  override def printDbgModel(messageTranslator: MessageTranslator,
                             traceAbstraction: Set[AbstractTrace])(implicit zCtx:Z3SolverCtx): Unit = {
    try {
      printAbstSolution(zCtx.solver.getModel, messageTranslator, traceAbstraction)
    }catch{
      case e:Z3Exception =>
        throw e
    }
  }

  def printAbstSolution(model: Model, messageTranslator: MessageTranslator,
                        traceAbstraction: Set[AbstractTrace])(implicit zCtx:Z3SolverCtx) {
    println(s"===model: $model")
    val ctx = zCtx.ctx
    traceAbstraction foreach { abs => {
      val indices = model.getSortUniverse(msgSort).filter{msg =>
        val res = model.eval(mkTraceFn.asInstanceOf[FuncDecl[BoolSort]].apply(msg),true).isTrue
        res
      }
      initializeOrderAxioms(messageTranslator)
      val lte = msgLTE
      val sortedInd = indices.sortWith((e1,e2) =>
        model.eval(ctx.mkAnd(lte.apply(e1,e2), ctx.mkNot(ctx.mkEq(e1,e2))),true).isTrue)
      println("=indices=")
      sortedInd.zipWithIndex.foreach(i => println(s"${i._2} = ${i._1}"))

      println("=function decls=")
      model.getFuncDecls.foreach(println)

      println("=type fun=")
      val addr = model.getSortUniverse(addrSort)
      val typeFun = model.getFuncDecls.find { f =>
        val name = f.getName.toString
        name.contains("addressToType")
      }
      //      addr.foreach

//      println("=trace solution=")
//      var traceLen = 0
//      while(model.eval(mkEq(sortedInd(traceLen),len).asInstanceOf[BoolExpr], true).isFalse){
//        traceLen = traceLen+1
//      }
      //      val traceFun = mkTraceFn(uniqueID).asInstanceOf[FuncDecl[UninterpretedSort]]
      val nameFun = messageTranslator.nameFun.asInstanceOf[FuncDecl[_]]
      val argFun = (0 until messageTranslator.maxArgs).map(i => mkArgFun(i).asInstanceOf[FuncDecl[_]])
      def printTraceElement(index:Int):Unit = {
        println(s"$index : ${sortedInd(index)} :")
        val msgati = sortedInd(index).asInstanceOf[Expr[UninterpretedSort]]
        val mIter = messageTranslator.solverToIdentitySignature.filter{
          case (ast, _) => model.eval(mkEq(nameFun.apply(msgati), ast).asInstanceOf[BoolExpr],true).isTrue
        }
        val m = mIter.head._2

        if(m != "OTHEROTHEROTHER") {
          val iset = messageTranslator.iForZ3Name(m)
          val args = iset.head.lsVars.indices
            .map(index => model.eval(argFun(index).apply(msgati), true)).mkString(",")

          println(s"$m " +
            s"args: $args")
        }else{
          println("Other Msg")
        }
      }
      println("=traceModel=")
      sortedInd.indices.foreach(printTraceElement)

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
            Set(state.traceAbstraction))
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
      mkBoolVal(boolVal = true)
    else {
      equalToOneOfTypes(typeFun.asInstanceOf[FuncDecl[Sort]].apply(addr.asInstanceOf[Expr[Sort]]), typeToSolverConst, tc)
    }
  }
  override protected def createTypeFun()(implicit zCtx:Z3SolverCtx):AST = {
    val args: Array[Sort] = Array(addrSort)
    zCtx.ctx.mkFuncDecl("addressToType", args, typeSort)
  }

  override protected def mkForallAddr(name:PureVar, cond: AST=>AST)(implicit zCtx:Z3SolverCtx):AST = {

    val j = mkFreshPv(name)
    zCtx.ctx.mkForall(Array(j), cond(j).asInstanceOf[BoolExpr],1,null,null,null,null)
  }

  override protected def mkForallAddr(nameToAST: Map[PureVar,AST], cond: Map[PureVar,AST] => AST)
                                     (implicit zCtx:Z3SolverCtx): AST = {
    if(nameToAST.isEmpty){
      cond(Map())
    }else {
      val j = nameToAST.map{case (_,v) => v.asInstanceOf[Expr[UninterpretedSort]]}.toSet
      zCtx.ctx.mkForall(j.toArray,
        cond(nameToAST).asInstanceOf[Expr[BoolSort]], 1,
        null, null, null, null)
    }
  }


  override protected def mkExistsT(t:List[AST], cond:AST)(implicit zCtx:Z3SolverCtx):AST = {
    if(t.nonEmpty) {
      val tc: Array[Expr[_]] = t.map(v => v.asInstanceOf[Expr[UninterpretedSort]]).toArray
      zCtx.ctx.mkExists(tc, cond.asInstanceOf[BoolExpr], 1, null, null, null, null)
    }else cond
  }
  override protected def mkExistsAddr(name:PureVar, cond: AST=>AST)(implicit zCtx:Z3SolverCtx):AST = {
    val j = mkFreshPv(name)
    zCtx.ctx.mkExists(Array(j), cond(j).asInstanceOf[BoolExpr],1,null,null,null,null)
  }

  override protected def mkExistsAddr(nameToAST: Map[PureVar, AST],
                                      cond: Map[PureVar,AST] => AST)
                                     (implicit zCtx:Z3SolverCtx): AST = {
    if(nameToAST.isEmpty){
      cond(Map())
    }else {
      val j = nameToAST.map{case (_,v) => v.asInstanceOf[Expr[UninterpretedSort]]}.toSet
      zCtx.ctx.mkExists(j.toArray,
        cond(nameToAST).asInstanceOf[Expr[BoolSort]], 1,
        null, null, null, null)
    }
  }

  override protected def mkFreshPv(pv: PureVar)(implicit zCtx:Z3SolverCtx):Expr[UninterpretedSort] = {
    val pvName = mkPvName(pv)
    zCtx.ctx.mkFreshConst(pvName, addrSort)
  }

  /**
   * there exists an int in (min,max) such that condition is true
   * @param cond function from const to boolean expression
   * @return
   */
  protected def mkExistsInt(min:AST, max:AST, cond:AST=>AST)(implicit zCtx:Z3SolverCtx):AST = {
    val j= zCtx.ctx.mkFreshConst("i", zCtx.ctx.mkIntSort()).asInstanceOf[ArithExpr[ArithSort]]
    val range = mkAnd(List(mkLt(min,j), mkLt(j,max)))
    zCtx.ctx.mkExists(Array(j), mkAnd(range,cond(j)).asInstanceOf[BoolExpr]
      ,1,null,null,null,null)
  }

  override protected def mkImplies(t: AST, t1: AST)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkImplies(t.asInstanceOf[BoolExpr], t1.asInstanceOf[BoolExpr])
  }

  override protected def mkLocalFn()(implicit zCtx: Z3SolverCtx): FuncDecl[_] = {
    zCtx.ctx.mkFuncDecl(s"localfn_", localSort, addrSort)
  }

  def mkDynFieldName(fieldName:String):String = s"dynField_${fieldName}_"

  override protected def mkDynFieldFn(fieldName:String)(implicit zCtx:Z3SolverCtx):FuncDecl[_] = {
    val addrAddr:Array[Sort] = Array(addrSort,addrSort)
    val fun = zCtx.ctx.mkFuncDecl(mkDynFieldName(fieldName), addrAddr, zCtx.ctx.mkBoolSort)
    fun
  }

  override protected def mkINameFn()(implicit zCtx:Z3SolverCtx): FuncDecl[UninterpretedSort] = {
    zCtx.ctx.mkFuncDecl(s"namefn_", msgSort, iNameSort)
  }
//  private def mkArgSort()(implicit zCtx:Z3SolverCtx): UninterpretedSort = {
//    zCtx.ctx.mkUninterpretedSort("Arguments")
//  }
//  private def mkArgs(n:Int)(implicit zCtx:Z3SolverCtx):Array[Expr[UninterpretedSort]] = {
//    val argIds = (0 until n).map(v => zCtx.ctx.mkFreshConst(s"arg___${v}", mkArgSort())).toArray
//    val argf = zCtx.ctx.mkConst("argf__", mkArgSort())
//    val constraint: Expr[BoolSort] = mkOr(argIds.map(argId => mkEq(argf, argId) ).toList).asInstanceOf[Expr[BoolSort]]
//    zCtx.mkAssert(zCtx.ctx.mkForall(Array(argf), constraint, 1, null,null,null,null))
//    zCtx.mkAssert(zCtx.ctx.mkDistinct(argIds:_*))
//    argIds
//  }

  override protected def mkArgFun(i:Int)(implicit zCtx:Z3SolverCtx): AST = {
//    if(zCtx.args.isEmpty){
//      zCtx.args = mkArgs(MAX_ARGS)
//    }
//    val argSort:Sort = mkArgSort()
    zCtx.ctx.mkFuncDecl(s"argfun_$i", msgSort, addrSort)
  }

  protected def mkConstValueConstraint(addr:AST)(implicit zCtx:Z3SolverCtx):AST = {
    val constFn = zCtx.ctx.mkFuncDecl("constFn", addrSort, constSort)
    constFn.apply(addr.asInstanceOf[Expr[UninterpretedSort]])
  }

  override protected def mkIName(enum:AST, enumNum:Int)(implicit zCtx:Z3SolverCtx): AST = {
    enum.asInstanceOf[EnumSort[_]].getConst(enumNum)
  }

  override protected def mkNames(types: List[String])(implicit zCtx:Z3SolverCtx): Map[String,AST] = {
    val tmap:Map[String,AST] = types.map(t => (t -> zCtx.ctx.mkConst(t, iNameSort))).toMap
    tmap
  }

  override protected def mkNameConstraint(nameFun: AST, msg: AST)(implicit zCtx:Z3SolverCtx): AST = {
    nameFun.asInstanceOf[FuncDecl[_]].apply(msg.asInstanceOf[Expr[Sort]])
  }

  override protected def mkArgConstraint(argIndex: Int, msg: AST)(implicit zCtx:Z3SolverCtx): AST = {
    assert(msg.isInstanceOf[Expr[UninterpretedSort]])
    val argFun = mkArgFun(argIndex)
    argFun.asInstanceOf[FuncDecl[_]].apply(msg.asInstanceOf[Expr[UninterpretedSort]])
  }

//  private def mkArgConstraint(argFun:AST,
//                              arg:Expr[UninterpretedSort],
//                              msg:Expr[UninterpretedSort])(implicit zCtx:Z3SolverCtx):AST = {
//    argFun.asInstanceOf[FuncDecl[_]].apply(arg,
//      msg)
//  }

  override protected def mkAddrConst(i: Int)(implicit zCtx:Z3SolverCtx): AST = {
    zCtx.ctx.mkConst(s"addr_const$i", addrSort)
  }

  override protected def mkMsgConst(i:Int, msg:Option[TraceElement])(implicit zCtx:Z3SolverCtx): AST = {
//    if(i == 0){
//      assert(msg.contains(TInitial) || msg.isEmpty, "Initial trace element should be TInitial")
//      return mkZeroMsg
//    }
    val sig = (i,msg) match {
//      case (_,Some(TInitial)) => throw new IllegalArgumentException("bad initial message position")
      case (_,Some(TCLInit(_))) => ???
      case (_,Some(TNew(_))) => ???
      case (i,Some(TMessage(mType, method, _))) => s"${mType}_${method.name}_$i"
      case (i,None) => s"__unn__$i"
    }
    zCtx.ctx.mkConst(s"msgat_$sig", msgSort)
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

  override protected def persist: ClassHierarchyConstraints = persistentConstraints



  override protected def mkTypeConstraints(types: Set[Int])(implicit zCtx: Z3SolverCtx): (AST, Map[Int, AST]) = {
    val typeMap = types.map(t => (t-> zCtx.ctx.mkConst(s"type_$t", typeSort))).toMap
    val allConstraints = typeMap.map{case (_,c) => c}
    val unique = mkDistinctT(allConstraints)
    (unique, typeMap)
  }

  override protected def mkLocalConstraint(localIdent:AST, equalTo: AST)
                                          (implicit zCtx: Z3SolverCtx): AST = {
    val fn = mkLocalFn()
    mkEq(fn.apply(localIdent.asInstanceOf[Expr[UninterpretedSort]]), equalTo)
  }

  override protected def mkDynFieldConstraint(base: AST, fieldName: String, equalTo: AST)
                                             (implicit zCtx: Z3SolverCtx): AST = {
    val fn = mkDynFieldFn(fieldName)
    val appFun = fn.apply(base.asInstanceOf[Expr[Sort]], equalTo.asInstanceOf[Expr[Sort]])
//    mkEq(appFun, equalTo)
    appFun
  }

  override protected def mkStaticFieldConstraint(clazz:String, fieldName:String, equalTo:AST)
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

  protected def mkConstConstraintsMap(pvs: Set[PureVal])(implicit zCtx: Z3SolverCtx): Map[PureVal, AST] = {
    val ctx = zCtx.ctx
    val constMap = pvs.flatMap{t =>
      t.z3Tag.map(tag => (t-> ctx.mkConst(s"const_${tag}", constSort)))
    }.toMap
    constMap
  }

  private def iNameString = "inames"
  // index sort used before msg was the order
  //  private def indexSort(implicit zCtx: Z3SolverCtx):UninterpretedSort = zCtx.ctx.mkUninterpretedSort("Uint")
  private def addrSort(implicit zCtx:Z3SolverCtx) = zCtx.ctx.mkUninterpretedSort("Addr")
  private def msgSort(implicit zCtx: Z3SolverCtx):UninterpretedSort = zCtx.ctx.mkUninterpretedSort("Msg")
  private def typeSort(implicit zCtx:Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort("ClassTypes")
  private def constSort(implicit zCtx:Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort("ConstVals")
  private def localSort(implicit zCtx:Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort("Locals")
  private def iNameSort(implicit zCtx:Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort(iNameString)

  /**
   * create msgLTE function such that (msgLTE X Y) means X ≤ Y
   */
  private def msgLTE(implicit zCtx: Z3SolverCtx): FuncDecl[BoolSort] = {
    val msgMsg: Array[Sort] = Array(msgSort, msgSort)
    zCtx.ctx.mkFuncDecl("msgLTE", msgMsg, zCtx.ctx.mkBoolSort)
  }

  override def initializeNameAxioms(messageTranslator:MessageTranslator)(implicit zCtx:Z3SolverCtx):Unit = {
    if(!zCtx.uninterpretedTypes.contains(iNameString)){
      val u = zCtx.ctx.mkFreshConst("u", iNameSort)
      val tmap = mkNames(messageTranslator.inamelist)
      val eachT = mkOr(tmap.map{case (_,v) => mkEq(u, v)}).asInstanceOf[BoolExpr]
      val tOnly = tmap.map{case (_,v) => v.asInstanceOf[Expr[UninterpretedSort]]}
      zCtx.mkAssert(zCtx.ctx.mkForall(Array(u), eachT, 1, null,null,null,null))
      zCtx.mkAssert(zCtx.ctx.mkDistinct(tOnly.toArray:_*))
    }
  }
  override def initalizeConstAxioms(messageTranslator: MessageTranslator)(implicit zCtx:Z3SolverCtx): Unit = {
    val ctx = zCtx.ctx
    val constMap = mkConstConstraintsMap(messageTranslator.pureValSet)
    val allConstraints = constMap.map{
      case (_,c) => c.asInstanceOf[Expr[UninterpretedSort]]
    }
    val unique = mkDistinctT(allConstraints)
    zCtx.mkAssert(unique)
    val const = ctx.mkFreshConst("constVal", constSort)
    val oneOf = allConstraints.map(c => mkEq(c,const)).reduce(mkOr).asInstanceOf[BoolExpr]
    val forall = ctx.mkForall(Array(const), oneOf,1, null, null, null, null)
    zCtx.mkAssert(forall)
  }
  override def initializeZeroAxioms(messageTranslator: MessageTranslator)(implicit zCtx:Z3SolverCtx): Unit = {
    val ctx = zCtx.ctx
    val lte = msgLTE
    if(!zCtx.isZeroInitialized) {
      zCtx.initializeZero
      val x = ctx.mkFreshConst("x", msgSort)
      // ** All messages are greater than or equal to zero
      // forall x. zero ≤ x
      val zeroLTE: BoolExpr = lte.apply(mkZeroMsg, x).asInstanceOf[BoolExpr]
      zCtx.mkAssert(ctx.mkForall(Array(x), zeroLTE, 1, null, null, null, null))
      val nameFN = mkINameFn()
      zCtx.mkAssert(mkEq(nameFN.apply(mkZeroMsg), messageTranslator.getZeroMsgName))
    }
  }

  override def initializeFieldAxioms(messageTranslator:MessageTranslator)(implicit zCtx:Z3SolverCtx):Unit = {
    val fieldNames:Iterable[String] = messageTranslator.dynFieldSet.map(mkDynFieldName)
    fieldNames.foreach { fieldName =>
      val fun = mkDynFieldFn(fieldName)
      if (!zCtx.initializedFieldFunctions.contains(fieldName)) {
        val a1 = zCtx.ctx.mkFreshConst("a1", addrSort)
        val a2 = zCtx.ctx.mkFreshConst("a2", addrSort)
        val a3 = zCtx.ctx.mkFreshConst("a3", addrSort)

        val b = zCtx.ctx.mkForall(Array(a1, a2, a3),
          mkImplies(mkAnd(fun.apply(a1, a2), fun.apply(a1, a3)), mkEq(a2, a3)).asInstanceOf[BoolExpr],
          1, null, null, null, null)
        zCtx.mkAssert(b)
        zCtx.initializedFieldFunctions.add(fieldName)
      }
    }
  }

  /**
   * Apply axioms to enforce total order to messages in history.
   * Note: this used to be an uninterpreted index sort, but was simplified to a total order over messages.
   * @param zCtx z3 context object
   * @return ≤ relation between messages
   */
  override def initializeOrderAxioms(messageTranslator: MessageTranslator)
                                (implicit zCtx: Z3SolverCtx):Unit = {

    val ctx = zCtx.ctx
    val lte = msgLTE
    if(!zCtx.indexInitialized){

      // Total ordering encoding used from: https://dl.acm.org/doi/pdf/10.1145/3140568
      // Paxos Made EPR: Decidable Reasoning about DistributedProtocols
      // figure 1
      // ** less than is transitive
      val x = ctx.mkFreshConst("x",msgSort)
      val y = ctx.mkFreshConst("y",msgSort)
      val z = ctx.mkFreshConst("z",msgSort)
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

      zCtx.indexInitialized = true
    }
  }

  override protected def encodeValueCreatedInFuture(v: AST, maxArgs:Int)(implicit zCtx: Z3SolverCtx): AST = {
    val ctx = zCtx.ctx
    val argFuns = (0 until maxArgs).map(i => mkArgFun(i).asInstanceOf[FuncDecl[UninterpretedSort]])
    val m = ctx.mkConst("allMsg", msgSort)
    val v_ = v.asInstanceOf[Expr[UninterpretedSort]]
//    val pred:BoolExpr = ctx.mkAnd(
//      zCtx.args.map(arg =>
//        ctx.mkNot(ctx.mkEq(
//            argFun.apply(arg,m),v_))):_*)
    val pred= argFuns.map(argFun => mkNe(argFun.apply(m), v)).reduce(mkAnd).asInstanceOf[BoolExpr]
    ctx.mkForall(Array(m), pred, 1, null,null,null,null)
  }

  override def getLogger: Logger =
    LoggerFactory.getLogger("Z3StateSolver")

  override protected def mkTraceFn()(implicit zCtx: Z3SolverCtx):AST={
    val ctx = zCtx.ctx
    ctx.mkFuncDecl("traceFn", msgSort, ctx.mkBoolSort())
  }

  override protected def mkTraceFnContains(traceFn: AST, v: AST)(implicit zCtx: Z3SolverCtx): Expr[BoolSort] = {
    val iTraceFn = traceFn.asInstanceOf[FuncDecl[BoolSort]]
    iTraceFn.apply(v.asInstanceOf[Expr[UninterpretedSort]])
  }


  override protected def mkExistsMsg(traceFn:AST, cond: AST => AST)(implicit zCtx: Z3SolverCtx): Expr[BoolSort] = {
    val ctx = zCtx.ctx
    val j = zCtx.ctx.mkFreshConst("j", msgSort)
    val cond2: BoolExpr = ctx.mkAnd(
      mkTraceFnContains(traceFn,j),cond(j).asInstanceOf[BoolExpr])
    ctx.mkExists(Array(j),cond2
      , 1, null, null, null, null)
  }

  override protected def mkForallMsg(traceFn:AST, cond: AST => AST)(implicit zCtx: Z3SolverCtx): AST = {
    val ctx = zCtx.ctx
    val j = zCtx.ctx.mkFreshConst("j", msgSort)
    val cond2 = ctx.mkImplies(mkTraceFnContains(traceFn,j),cond(j).asInstanceOf[BoolExpr])
    ctx.mkForall(Array(j), cond2
      , 1, null, null, null, null)
  }

  override protected def mkLTEMsg(ind1: AST, ind2: AST)(implicit zctx: Z3SolverCtx): AST =
    msgLTE.apply(ind1.asInstanceOf[Expr[UninterpretedSort]], ind2.asInstanceOf[Expr[UninterpretedSort]])

  override protected def mkLTMsg(ind1: AST, ind2: AST)(implicit zctx: Z3SolverCtx): AST =
    mkAnd(mkLTEMsg(ind1,ind2), mkNot(mkEq(ind1,ind2)))

  override protected def mkAddOneMsg(traceFn:AST, ind: AST)(implicit zctx: Z3SolverCtx): (AST, AST) = {
    val mConst = zctx.ctx.mkFreshConst("msg",msgSort)

    val req = mkForallMsg(traceFn, m => mkOr(List(mkLTEMsg(m,ind), mkLTEMsg(mConst,m))) )

    (req,mConst)
  }

  /**
   * create a fresh variable that is ind+1
   * @param ind target index
   * @param zCtx solver context
   * @return (assertion that fresh var is ind+1, fresh var)
   */
  //  override protected def mkAddOneIndex(ind: AST)(implicit zCtx: Z3SolverCtx): (AST,AST) = {
  //    val ctx = zCtx.ctx
  //    val lte = indexLTE
  //    val indNext = zCtx.ctx.mkFreshConst("indNext", indexSort)
  //    val other = zCtx.ctx.mkFreshConst("other", indexSort)
  //    val indt = ind.asInstanceOf[Expr[UninterpretedSort]]
  //    val assert = mkAnd(List(
  //      lte.apply(indt,indNext),
  //      ctx.mkNot(ctx.mkEq(ind.asInstanceOf[Expr[UninterpretedSort]],indNext)),
  //      ctx.mkForall(Array(other), ctx.mkOr(lte.apply(other,indt), lte.apply(indNext, other)),
  //        1,null,null,null,null)
  //    ))
  //    (assert,indNext)
  //  }

  protected def mkZeroMsg(implicit zCtx:Z3SolverCtx):Expr[UninterpretedSort] = {
    assert(zCtx.isZeroInitialized, "zero must be initialized to make zero message")
    zCtx.ctx.mkConst("zeroMessage___",msgSort)
  }
}
