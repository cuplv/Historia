package edu.colorado.plv.bounder.solver

import better.files.File
import com.microsoft.z3._
import com.microsoft.z3.enumerations.Z3_ast_print_mode
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppMethod, CBEnter, CBExit, CIEnter, CIExit, FwkMethod, TCLInit, TMessage, TNew, TraceElement, WitnessExplanation}
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, CLInit, FreshRef, OAbsMsg, Signature}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, BotVal, ConcreteAddr, ConcreteVal, NamedPureVar, NullVal, OutputMode, PureExpr, PureVal, PureVar, State, TopVal}
import io.github.andrebeat.pool.{Lease, Pool}
import org.slf4j.{Logger, LoggerFactory}
import smtlib.lexer.Lexer
import smtlib.lexer.Lexer.UnexpectedCharException
import smtlib.parser.Parser
import smtlib.printer.RecursivePrinter
import smtlib.trees.Commands.Assert
import smtlib.trees.{Commands, CommandsResponses, Terms}
import smtlib.trees.Terms.{Exists, Forall, FunctionApplication, Identifier, Let, QualifiedIdentifier, SList, SSymbol, SortedVar, Term, VarBinding}

import java.io.StringReader
import scala.collection.concurrent.TrieMap
import scala.collection.immutable
import scala.collection.mutable
import scala.jdk.CollectionConverters._
import scala.concurrent.duration._
import scala.language.postfixOps

case class Z3SolverCtx(timeout:Int, randomSeed:Int) extends SolverCtx[AST] {
  var acquired:Boolean = false
  private val argsUsed = mutable.HashSet[Integer]()
  private var ictx = new Context()
  private var isolver: Solver = null
  makeSolver(timeout, Some(randomSeed))
  val initializedFieldFunctions: mutable.HashSet[String] = mutable.HashSet[String]()
  var indexInitialized: Boolean = false
  val uninterpretedTypes: mutable.HashSet[String] = mutable.HashSet[String]()

  def release(): Unit = this.synchronized {
    if(solver != null)
      isolver.reset()
    argsUsed.clear()
    initializedFieldFunctions.clear()
    uninterpretedTypes.clear()
    if (acquired) {
      //val currentThread: Long = Thread.currentThread().getId
      //assert(acquired.get == currentThread)
      acquired = false
      zeroInitialized = false
      indexInitialized = false
    }
  }
  def setArgUsed(i: Int) = argsUsed.add(i)
  def getArgUsed():Set[Integer] = argsUsed.toSet
  private var overridden = false
  def overrideTimeoutAndSeed(alternateTimeout:Int, seed:Int): Unit = {
    overridden = true
    isolver.reset()
    makeSolver(alternateTimeout, Some(seed))
  }
  def resetTimeoutAndSeed(): Unit = {
    if(overridden)
      makeSolver(timeout, Some(randomSeed))

    overridden = false
  }


  //val sortEdges = mutable.HashSet[(String,String)]()
  private var zeroInitialized:Boolean = false
  def initializeZero:Unit ={
    zeroInitialized = true
  }
  def isZeroInitialized:Boolean = zeroInitialized
  def ctx:Context ={
    assert(acquired)
    ictx
  }
  def solver:Solver = {
    assert(acquired)
    isolver
  }

  def mkAssert(t: AST): Unit = this.synchronized{
    //TODO: trim existential of things not used ====

    //val t2 = pruneUnusedQuant(t)
//    val t2 = t
    assert(acquired)
    solver.add(t.asInstanceOf[BoolExpr])
  }


  // Method for detecting cycles in function sorts or Ɐ∃ quantifications
  private def detectCycle(edges: Set[(String, String)]): Boolean = {
    def iCycle(n: String, visited: Set[String]): Boolean = {
      if (visited.contains(n)) {
        true
      } else {
        val nextNodes = edges.flatMap {
          case (k, v) if k == n => Some(v)
          case _ => None
        }
        nextNodes.exists(nn => iCycle(nn, visited + n))
      }
    }

    val allNodes: Set[String] = edges.flatMap {
      case (k, v) => Set(k, v)
    }
    allNodes.exists(n => iCycle(n, Set()))
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
  private def makeSolver(timeout:Int, newRandomSeed:Option[Int]) = this.synchronized {
    if(isolver != null ){
      try {
        isolver.reset()
      }catch{
        case e:Z3Exception if e.getMessage == "Context closed" => {
          // ignore, reset is just to reduce mem leaks
        }
      }
    }
    isolver = ictx.mkSolver
//    val solver = ctx.mkSimpleSolver()
    val params = ictx.mkParams()
    params.add("timeout", timeout)
    params.add("logic", "AUFLIA")
    //params.add("model.compact", true)
    // Global.setParameter("parallel.enable", "true") // note: parallel z3 does not seem to speed things up
    //Global.setParameter("memory_max_size", "5000") //todo: is there a way to set mem usage per query?
    newRandomSeed.foreach { rs =>
      params.add("random-seed", rs + randomSeed)
    }
    // params.add("threads", 4) Note: threads cause weird decidability issue

    // set_option(max_args=10000000, max_lines=1000000, max_depth=10000000, max_visited=1000000)

    //TODO: does this get rid of the "let" statements when printing?
    //    ctx.setPrintMode(Z3_ast_print_mode.Z3_PRINT_LOW_LEVEL)
    isolver.setParameters(params)
  }

  def dispose():Unit = this.synchronized{
    release()
    argsUsed.clear()
    if(isolver != null){
      isolver.reset()
    }
    isolver = null;
    if(ictx != null){
      ictx.close()
    }
    ictx = null;
  }

  private var acquireCount = 0
  override def acquire(cRandomSeed:Option[Int]): Unit = {
//    ictx = new Context()
//    isolver = makeSolver(timeout,cRandomSeed)
    acquireCount +=1
    //val currentThread:Long = Thread.currentThread().getId

    assert(!acquired)
    acquired = true
    initializedFieldFunctions.clear()
    indexInitialized = false
    uninterpretedTypes.clear()
    if(acquireCount % 5 == 0) {
      isolver.reset()
      ictx.close()
      ictx = new Context()
      makeSolver(timeout, Some(randomSeed))
    } else {
      isolver.reset()
    }
  }
}
object Z3StateSolver{
}

/**
 *
 * @param persistentConstraints
 * @param timeout
 * @param randomSeed
 * @param defaultOnSubsumptionTimeout
 * @param pushSatCheck
 * @param strict_test true to crash if something times out
 */
class Z3StateSolver(persistentConstraints: ClassHierarchyConstraints,
                    logTimes:Boolean,
                    timeout:Int = 40000,
                    randomSeed:Int=3578,
                    defaultOnSubsumptionTimeout: () => Boolean = () => false,
                    pushSatCheck:Boolean = true,
                    strict_test:Boolean = false,
                    z3InstanceLimit:Int = -1
                   ) extends StateSolver[AST,Z3SolverCtx] {
  private val mZ3InstanceLimit = if(z3InstanceLimit > 0) z3InstanceLimit else {
    Runtime.getRuntime.availableProcessors
  }
  //  private val MAX_ARGS = 10

  override def shouldLogTimes:Boolean = this.logTimes

  /**
   * Used to dedup let exists and forall in free vars
   */
  def dummyVarBinding(sv: SortedVar): VarBinding =
    VarBinding(sv.name, QualifiedIdentifier(Identifier(SSymbol("true"), Seq()), None))

  def freeVar(t: Terms.SExpr): Set[SSymbol] = t match {
    case q: QualifiedIdentifier =>
      Set(q.id.symbol)
    case FunctionApplication(fun, terms) => terms.flatMap(freeVar).toSet
    case Let(b, bindings, term) =>
      val bind = b +: bindings
      val boundHere: Set[SSymbol] = bind.map {
        case VarBinding(name, term) => name
      }.toSet
      // Remove vars bound by let and add free vars of expressions assigned to vars
      freeVar(term).diff(boundHere) ++ bind.flatMap { case VarBinding(_, term) => freeVar(term) }
    case Exists(sv, svs, term) => freeVar(Let(dummyVarBinding(sv), svs.map(dummyVarBinding), term))
    case Forall(sv, svs, term) => freeVar(Let(dummyVarBinding(sv), svs.map(dummyVarBinding), term))
    case v =>
      println(v)
      ???
  }

  def pruneUnusedQuant(t: AST)(implicit zCtx: Z3SolverCtx): AST = {
    val expr = z3ExprToSmtLib(t)
    //val expr: Terms.SExpr = parser.parseSExpr


    def handleQuant(sortedVar: SortedVar, sortedVars: Seq[SortedVar], body: Term): List[SortedVar] = {
      val vars = sortedVar :: sortedVars.toList
      val fv = freeVar(body)
      val filtQuantifiedVars = vars.filter { case SortedVar(symb, _) => fv.contains(symb) }
      filtQuantifiedVars
    }

    def iPrune(t: Terms.SExpr): Terms.SExpr = t match {
      case Terms.Exists(sortedVar, sortedVars, term) =>
        val newVars = handleQuant(sortedVar, sortedVars, term)
        if (newVars.nonEmpty)
          Terms.Exists(newVars.head, newVars.tail, term)
        else
          term
      case Terms.Forall(sortedVar, sortedVars, term) =>
        val newVars = handleQuant(sortedVar, sortedVars, term)
        if (newVars.nonEmpty)
          Terms.Forall(newVars.head, newVars.tail, term)
        else term
      case q => q
    }


    val pruned = iPrune(expr)
    val res = smtToZ3(pruned)(zCtx)
    res
  }

  def stringExprToSmtLib(expr: String): Term = {
    val lexer = new Lexer(new StringReader(s"(assert $expr)"))
    val parser = new Parser(lexer)
    parser.parseCommand match {
      case Assert(term) => term
      case _ => throw new IllegalStateException("Should not be possible, expression constructed above.")
    }
  }

  private def z3ExprToSmtLib(t: AST): Term = {
    stringExprToSmtLib(t.toString)
  }

  object SmtLibBool {
    def unapply(t: Terms.SExpr): Option[Boolean] = t match {
      case QualifiedIdentifier(Identifier(SSymbol("true"), _), _) => Some(true)
      case QualifiedIdentifier(Identifier(SSymbol("false"), _), _) => Some(false)
      case _ => None
    }
  }

  private def sortedVarToConst(v: SortedVar)(implicit zCtx: Z3SolverCtx) = {
    val sortName = v.sort.id.symbol.name
    zCtx.ctx.mkConst(v.name.name, zCtx.ctx.mkUninterpretedSort(sortName))
  }

  private def asSmtExpr_(v: Terms.SExpr)(implicit zCtx: Z3SolverCtx): Expr[_] = smtToZ3(v).asInstanceOf[Expr[_]]

  private def asSmtExprB(v: Terms.SExpr)(implicit zCtx: Z3SolverCtx): Expr[BoolSort] = smtToZ3(v).asInstanceOf[Expr[BoolSort]]

  private def swapB(v: SSymbol, withExpr: Term, b: VarBinding): VarBinding = b match {
    case VarBinding(name, term) => VarBinding(name, swap(v, withExpr, term))
  }

  private def swap(v: SSymbol, withExpr: Term, in: Term): Term = in match {
    case QualifiedIdentifier(Identifier(v2, _), _) if v2 == v => withExpr
    case q: QualifiedIdentifier => q
    case Exists(sv, svs, term) if sv.name != v && svs.forall(sv => sv.name != v) => Exists(sv, svs, swap(v, withExpr, term))
    case Forall(sv, svs, term) if sv.name != v && svs.forall(sv => sv.name != v) => Forall(sv, svs, swap(v, withExpr, term))
    case Let(bi, bis, term) if bi.name != v && bis.forall(sv => sv.name != v) =>
      Let(swapB(v, withExpr, bi), bis.map(b => swapB(v, withExpr, b)), swap(v, withExpr, term))
    case l: Let => l // avoid variable capture
    case e: Exists => e
    case a: Forall => a
    case FunctionApplication(fun, terms) => FunctionApplication(fun, terms.map(t => swap(v, withExpr, t)))
    case other =>
      println(other)
      ???
  }

  def inlineAllLet(t: Term): Term = {
    def iInline(t: Term): Term = t match {
      case Let(bi, bis, term) =>
        val newTerm = (bi :: bis.toList).foldLeft(term) { case (acc, toSwap) => swap(toSwap.name, toSwap.term, acc) }
        iInline(newTerm)
      case Exists(sv, svs, term) => Exists(sv, svs, iInline(term))
      case Forall(sv, svs, term) => Forall(sv, svs, iInline(term))
      case FunctionApplication(fun, terms) => FunctionApplication(fun, terms.map(t => iInline(t)))
      case q: QualifiedIdentifier => q
      case other =>
        throw new IllegalArgumentException(s"unimplemented: ${other} ${other.getClass}")
    }

    iInline(t)
  }

  def inlineLet(let: Let): Term = {
    val b = let.binding
    val binds = let.bindings
    val bind = b :: binds.toList
    val term = let.term
    val res = bind.foldLeft(term) {
      case (acc, VarBinding(name, term)) => swap(name, term, acc)
    }
    res
  }

  def smtToZ3(t: Terms.SExpr)(implicit zCtx: Z3SolverCtx): AST = t match {
    case SmtLibBool(b) =>
      mkBoolVal(b)
    case l: Let =>
      smtToZ3(inlineLet(l))
    case FunctionApplication(fun, terms) if fun.id.symbol.name == "distinct" =>
      zCtx.ctx.mkDistinct(terms.map(asSmtExpr_).toArray: _*)
    case FunctionApplication(fun, terms) if fun.id.symbol.name == "or" =>
      zCtx.ctx.mkOr(terms.map(asSmtExprB).toArray: _*)
    case FunctionApplication(fun, terms) if fun.id.symbol.name == "and" =>
      val res = zCtx.ctx.mkAnd(terms.map(asSmtExprB).toArray: _*)
      res
    case not@FunctionApplication(fun, terms) if fun.id.symbol.name == "not" =>
      assert(terms.size == 1, s"Wrong number of args for not: $not")
      zCtx.ctx.mkNot(terms.map(asSmtExprB).head)
    case eq@FunctionApplication(fun, terms) if fun.id.symbol.name == "=" =>
      assert(terms.size == 2, s"Wrong number of args for equality: $eq")
      val cTerms = terms.map(asSmtExpr_)
      zCtx.ctx.mkEq(cTerms.head, cTerms.last)
    case impl@FunctionApplication(fun, terms) if fun.id.symbol.name == "=>" =>
      assert(terms.size == 2, s"Wrong number of args for equality: $impl")
      val cTerms = terms.map(asSmtExprB)
      zCtx.ctx.mkImplies(cTerms.head, cTerms.last)
    case FunctionApplication(fun, terms) =>
      val func = functFromName(fun.id.symbol.name)
      val args = terms.map(v => smtToZ3(v).asInstanceOf[Expr[_]])
      func.apply(args.toArray: _*)
    case QualifiedIdentifier(qname, _) =>
      // hack to reconstruct types
      val name = qname.symbol.name
      val sort = constNameToSort(name)
      zCtx.ctx.mkConst(name, sort)
    case Exists(v1, v2, body) =>
      val ctx = zCtx.ctx
      val v = v1 :: v2.toList
      ctx.mkExists(v.map(sortedVarToConst).toArray, smtToZ3(body).asInstanceOf[BoolExpr],
        1, null, null, null, null)
    case Forall(v1, v2, body) =>
      val ctx = zCtx.ctx
      val v = v1 :: v2.toList
      ctx.mkForall(v.map(sortedVarToConst).toArray, smtToZ3(body).asInstanceOf[BoolExpr],
        1, null, null, null, null)


    case SList(cmd :: rest) =>
      println(cmd)
      ???

    case Terms.SKeyword(kw) =>
      println(kw)
      ???

    case term: Terms.Term =>
      ???
    case command: Commands.Command =>
      ???
    case response: CommandsResponses.CommandResponse =>
      ???
    case value: Terms.AttributeValue =>
      ???
  }

  override def iDefaultOnSubsumptionTimeout(): Boolean = this.defaultOnSubsumptionTimeout()

  override def setSeed(v: Int)(implicit zctx: Z3SolverCtx): Unit = {
    zctx.ctx.updateParamValue("random-seed", v.toString)
  }


  //private val threadLocalCtx = ThreadLocal.withInitial(() => Z3SolverCtx(timeout, randomSeed))
  private val zctxPool = Pool(mZ3InstanceLimit, () => {  // look at other low level profiling tools - runlim
      val ctx = Z3SolverCtx(timeout,randomSeed)
      ctx.acquire()
      ctx
    },
    reset = (z:Z3SolverCtx) => {
      z.release()
      z.acquire()
    },
    maxIdleTime = 10 seconds,
    dispose = (z:Z3SolverCtx) => {
      z.dispose()
    }
  )

  override def getSolverCtx(): LeaseEnforceOnePerThread[Z3SolverCtx] = {
    LeaseEnforceOnePerThread(zctxPool.acquire())
  }

  override def solverString(messageTranslator: MessageTranslator)(implicit zCtx: Z3SolverCtx): String = {
    //initializeAllAxioms(messageTranslator)
    zCtx.solver.toString
  }

  override def checkSAT(messageTranslator: MessageTranslator,
                        axioms: Option[List[MessageTranslator => Unit]] = None,
                        shouldPushSat:Boolean
                       )(implicit zCtx: Z3SolverCtx): Boolean = {
    val getAxioms = axioms.getOrElse(
      List(m => initalizeConstAxioms(m),
        m => initializeNameAxioms(m),
        m => initializeFieldAxioms(m),
        m => initializeArgFunAxioms(m),
        m => initializeArgTotalityAxioms(m), // note: this one adds cycle in quant alternation graph
        m => initializeOrderAxioms(m),
      ))
    if (shouldPushSat)
      checkSatPush(messageTranslator, getAxioms)
    else
      checkSATOne(messageTranslator, getAxioms)

  }

  override def checkSatPush(messageTranslator: MessageTranslator,
                            axioms: List[MessageTranslator => Unit])(implicit zCtx: Z3SolverCtx): Boolean = {
    val res: Status = zCtx.solver.check()

    try {
      val interp = (res, axioms) match {
        case (Status.UNSATISFIABLE, _) =>
          // Already unsatisfiable, no need to add axioms
          false
        case (Status.SATISFIABLE, h :: t) =>
          zCtx.solver.push()
          h(messageTranslator)
          checkSatPush(messageTranslator, t)
        case (Status.UNKNOWN, h :: t) =>
          zCtx.solver.push()
          h(messageTranslator)
          checkSatPush(messageTranslator, t)
        case (Status.SATISFIABLE, Nil) =>
          // No more axioms to try
          true
        case (Status.UNKNOWN, Nil) =>
          throw new IllegalArgumentException("Unknown, no more axioms, failure.")
      }
      interp
    } catch {
      case z: Z3Exception =>
        throw new IllegalArgumentException("Unknown, no more axioms, failure.")

    }
  }

  override def checkSATOne(messageTranslator: MessageTranslator,
                           axioms: List[MessageTranslator => Unit])(implicit zCtx: Z3SolverCtx): Boolean = {
    axioms.foreach { ax => ax(messageTranslator) }
    val useCmd = false
    if (useCmd) {
      lazy val timeoutS = timeout.toString
      File.temporaryFile().apply { f =>
        println(s"file: $f")
        f.writeText(zCtx.solver.toString)
        f.append("\n(check-sat)")
        // Sometimes the java solver fails, we fall back to calling the command line tool
        try {
          val stdout = BounderUtil.runCmdStdout(s"timeout $timeoutS z3 ${f}")
          if (stdout.contains("unknown")) {
            throw new RuntimeException()
          }
          val isSat = !stdout.contains("unsat")
          assert(stdout.contains("sat"), s"Malformed z3 output: ${stdout}")
          isSat
        } catch {
          case e: RuntimeException =>
            println(e.getMessage)
            val f2 = File(s"timeout_${System.currentTimeMillis()}.z3")
            if (f2.exists()) {
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
  override def push()(implicit zCtx: Z3SolverCtx): Unit = {
    zCtx.solver.push()
  }

  override def pop()(implicit zCtx: Z3SolverCtx): Unit = {
    zCtx.solver.pop()
  }

  override protected def mkEq(lhs: AST, rhs: AST)(implicit zCtx: Z3SolverCtx): AST = {
    zCtx.ctx.mkEq(lhs.asInstanceOf[Expr[Sort]], rhs.asInstanceOf[Expr[Sort]])
  }

  override protected def mkNe(lhs: AST, rhs: AST)(implicit zCtx: Z3SolverCtx): AST =
    zCtx.ctx.mkNot(zCtx.ctx.mkEq(lhs.asInstanceOf[Expr[Sort]], rhs.asInstanceOf[Expr[Sort]]))

  override protected def mkLt(lhs: AST, rhs: AST)(implicit zCtx: Z3SolverCtx): AST =
    zCtx.ctx.mkLt(lhs.asInstanceOf[ArithExpr[ArithSort]], rhs.asInstanceOf[ArithExpr[ArithSort]])

  override protected def mkNot(o: AST)(implicit zCtx: Z3SolverCtx): AST = {
    o match {
      case v: BoolExpr if v.isTrue => mkBoolVal(boolVal = false)
      case v: BoolExpr if v.isFalse => mkBoolVal(boolVal = true)
      case v: BoolExpr => zCtx.ctx.mkNot(v)
      case _ => throw new IllegalStateException()
    }
  }

  override protected def mkSub(lhs: AST, rhs: AST)(implicit zCtx: Z3SolverCtx): AST = {
    zCtx.ctx.mkSub(lhs.asInstanceOf[ArithExpr[ArithSort]], rhs.asInstanceOf[ArithExpr[ArithSort]])
  }


  override protected def mkAnd(lhs: AST, rhs: AST)(implicit zCtx: Z3SolverCtx): Expr[BoolSort] = {
    mkAnd(List(lhs, rhs))
  }

  override protected def mkAnd(t: Iterable[AST])(implicit zCtx: Z3SolverCtx): Expr[BoolSort] = {
    // Simplify for debug
    // Note: in z3, and with no arguments returns true, this retains that behavior
    val t2 = t.filter {
      case v: BoolExpr => !v.isTrue
      case _ => true
    }

    if (t2.isEmpty) {
      mkBoolVal(boolVal = true)
    } else if (t2.size == 1) {
      t2.head.asInstanceOf[Expr[BoolSort]]
    } else {
      val tb: Array[BoolExpr] = t2.map(_.asInstanceOf[BoolExpr]).toArray
      zCtx.ctx.mkAnd(tb: _*)
    }
  }

  override protected def mkOr(lhs: AST, rhs: AST)(implicit zCtx: Z3SolverCtx): AST =
    mkOr(List(lhs, rhs))

  override protected def mkOr(t: Iterable[AST])(implicit zCtx: Z3SolverCtx): AST = {
    // Simplify for debug - make z3 ast easier to inspect
    // Note: in z3, or with no arguments returns false, this retains that behavior
    val t2 = t.filter {
      case v: BoolExpr => !v.isFalse
      case _ => true
    }

    // Simplify for debug -
    if (t2.size == 1) {
      t2.head
    } else if (t2.nonEmpty) {
      val tb: Array[BoolExpr] = t2.map(_.asInstanceOf[BoolExpr]).toArray
      zCtx.ctx.mkOr(tb: _*)
    } else {
      mkBoolVal(false)
    }
  }

  override protected def mkIntVal(i: Int)(implicit zCtx: Z3SolverCtx): AST = {
    zCtx.ctx.mkInt(i)
  }

  override protected def mkBoolVal(boolVal: Boolean)(implicit zCtx: Z3SolverCtx): BoolExpr = {
    zCtx.ctx.mkBool(boolVal)
  }

  override protected def mkLenVar(s: String)(implicit zCtx: Z3SolverCtx): AST = zCtx.ctx.mkConst(s, msgSort)

  override protected def mkAddrVar(pv: PureVar)(implicit zCtx: Z3SolverCtx): AST =
    zCtx.ctx.mkFreshConst(mkPvName(pv), addrSort)

  override protected def dumpDbg[T](cont: () => T)(implicit zCtx: Z3SolverCtx): T = {
    getSolverCtx() { solver =>
      println(s"current thread = ${Thread.currentThread().getId}")
      var failed = true
      var result: Option[T] = None
      val currentTime = (System.currentTimeMillis() / 1000).toInt
      val f = File(s"z3Timeout_${currentTime}")
      f.write(solver.toString)
      try {
        println(s"z3 dbg file written: ${f}")
        result = Some(cont())
        failed = false
      } catch {
        case t: Throwable =>
          println("error")
          throw t
      }
      if (!failed && result.nonEmpty && result.get != null) {
        println(s"deleting file due to success: ${f}")
        f.delete()
      }
      result.getOrElse(throw new IllegalStateException("Unknown failure"))
    }
  }

  private def interpretSolverOutput(status: Status)(implicit zCtx: Z3SolverCtx): Boolean = status match {
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
                              pvMap: Map[PureExpr, AST])(implicit zCtx: Z3SolverCtx): WitnessExplanation = {
    //TODO: have not implemented the set trace function here, will need this for synth loop
    val ctx = zCtx.ctx
    assert(messageTranslator.states.size == 1, "Explain witness only applicable with single state")
    val state = messageTranslator.states.head
    val pvSet = state.pureVars()
    val varPairs = BounderUtil.repeatingPerm[PureVar](_ => pvSet, 2).filter(a => a.head != a(1))

    val model = zCtx.solver.getModel

    val ta = state.traceAbstraction
    val mv = ta.modelVars
    val rightOfArrow = ta.rightOfArrow

    val pvModelValues: Map[PureExpr, Expr[UninterpretedSort]] = pvMap.map {
      case (pureVar, ast) =>
        (pureVar, model.eval(ast.asInstanceOf[Expr[UninterpretedSort]], true))
    }
    val pvValues: Map[Expr[UninterpretedSort], Int] = pvModelValues.values.toSet.zipWithIndex.toMap
//    val constFn: FuncDecl[UninterpretedSort] = mkConstFn
    val constMap = messageTranslator.getConstMap()

    def pvv(pvi: PureExpr): ConcreteVal = {
      val pv = pvModelValues(pvi)
      val isNull = constMap.contains(NullVal) && model.eval(mkEq(pv,
        constMap(NullVal)).asInstanceOf[Expr[UninterpretedSort]], true).isTrue
      if (isNull)
        NullVal
      else
        ConcreteAddr(pvValues(pv))
    }

    val pmv: PureExpr => PureVal = {
      case TopVal => TopVal
      case p: PureExpr => pvv(p)
      case v =>
        throw new IllegalArgumentException(s"Undefined model variable ${v}")
    }
    //    val pmv: String => TVal = v =>
    //      if(v == "_") T_ else {
    //        if(ta.modelVars.contains(v))
    //          pvv(ta.modelVars(v).asInstanceOf[PureVar])
    //        else throw new IllegalArgumentException(s"Undefined model variable ${v}, did you quantify a void value?")
    //      }


    val trace = rightOfArrow.map {
      case CLInit(sig) => TCLInit(sig)
      case FreshRef(v) =>
        TNew(v, state.sf.typeConstraints(v))
      case OAbsMsg(CBEnter, sig, vars) =>
        TMessage(CBEnter, AppMethod(sig.example(), None), vars.map(v => pmv(v)))
      case OAbsMsg(CBExit, sig, vars) =>
        TMessage(CBExit, AppMethod(sig.example(), None), vars.map(v => pmv(v)))
      case OAbsMsg(CIEnter, sig, vars) =>
        TMessage(CIEnter, FwkMethod(sig.example()), vars.map(v => pmv(v)))
      case OAbsMsg(CIExit, sig, vars) =>
        TMessage(CIExit, FwkMethod(sig.example()), vars.map(v => pmv(v)))
      //      case AnyAbsMsg => ??? //TODO: how to explain any?
    }

    WitnessExplanation(trace)
  }

  override def printDbgModel(messageTranslator: MessageTranslator,
                             traceAbstraction: Set[AbstractTrace])(implicit zCtx: Z3SolverCtx): Unit = {
    try {
      printAbstSolution(zCtx.solver.getModel, messageTranslator, traceAbstraction)
    } catch {
      case e: Z3Exception =>
        throw e
    }
  }

  def printAbstSolution(model: Model, messageTranslator: MessageTranslator,
                        traceAbstraction: Set[AbstractTrace])(implicit zCtx: Z3SolverCtx) {
    println(s"===model: $model")
    val ctx = zCtx.ctx
    traceAbstraction foreach { abs => {
      val indices = model.getSortUniverse(msgSort).filter { msg =>
        val res = model.eval(mkTraceFn.asInstanceOf[FuncDecl[BoolSort]].apply(msg), true).isTrue
        res
      }
      initializeOrderAxioms(messageTranslator)
      val lte = msgLTE
      val sortedInd = indices.sortWith((e1, e2) =>
        model.eval(ctx.mkAnd(lte.apply(e1, e2), ctx.mkNot(ctx.mkEq(e1, e2))), true).isTrue)
      println("=indices=")
      sortedInd.zipWithIndex.foreach(i => println(s"${i._2} = ${i._1}"))

      println("=function decls=")
      model.getFuncDecls.foreach(println)

      println("=type fun=")
      //      val addr = model.getSortUniverse(addrSort)
      //      val typeFun = model.getFuncDecls.find { f =>
      //        val name = f.getName.toString
      //        name.contains("addressToType")
      //      }
      //      addr.foreach

      //      println("=trace solution=")
      //      var traceLen = 0
      //      while(model.eval(mkEq(sortedInd(traceLen),len).asInstanceOf[BoolExpr], true).isFalse){
      //        traceLen = traceLen+1
      //      }
      //      val traceFun = mkTraceFn(uniqueID).asInstanceOf[FuncDecl[UninterpretedSort]]
      val nameFun = messageTranslator.nameFun.asInstanceOf[FuncDecl[_]]

      val addrs: Array[Expr[UninterpretedSort]] = model.getSortUniverse(addrSort)

      def argFun(index: Int, msg: Expr[UninterpretedSort]) = {
        val argF = mkArgFun(index).asInstanceOf[FuncDecl[_]]
        addrs.find(addr => argF.apply(msg, addr).isTrue).get
      }

      def printTraceElement(index: Int): Unit = {
        println(s"$index : ${sortedInd(index)} :")
        val msgati = sortedInd(index).asInstanceOf[Expr[UninterpretedSort]]
        val mIter = messageTranslator.solverToIdentitySignature.filter {
          case (ast, _) => model.eval(mkEq(nameFun.apply(msgati), ast).asInstanceOf[BoolExpr], true).isTrue
        }
        val m = mIter.head._2

        if (m != "OTHEROTHEROTHER") {
          val iset = messageTranslator.iForZ3Name(m)
          val args = iset.head.lsVars.indices
            .map(index => model.eval(argFun(index, msgati), true)).mkString(",")

          println(s"$m " +
            s"args: $args")
        } else {
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
                                        state: State,
                                        messageTranslator: MessageTranslator,
                                        logDbg: Boolean)(implicit zCtx: Z3SolverCtx): Option[AST] = {
    val solver = zCtx.solver
    solver.add(t.asInstanceOf[BoolExpr])
    val status: Status = solver.check()
    status match {
      case Status.SATISFIABLE =>
        if (logDbg) {
          println(s"Model: ${solver.getModel}")
          printAbstSolution(solver.getModel, messageTranslator,
            Set(state.traceAbstraction))
        }
        Some(t)
      case Status.UNKNOWN =>
        Some(t)
      case Status.UNSATISFIABLE =>
        if (logDbg) {
          println(s"Unsat core: ${solver.getUnsatCore.map(s => s.toString).mkString(" AND \n")}")
        }
        None
    }
  }

  private def equalToOneOf(e: Expr[Sort], vals: Array[Expr[Sort]])(implicit zCtx: Z3SolverCtx): BoolExpr = {
    val ctx = zCtx.ctx
    ctx.mkOr(vals.map(v => ctx.mkEq(e, v)): _*)
  }

  def equalToOneOfTypes(e: Expr[Sort], typeToSolverConst: Map[Int, AST],
                        types: Set[Int])(implicit zCtx: Z3SolverCtx): BoolExpr = {
    val solverTypes = types.map(typeToSolverConst).map(_.asInstanceOf[Expr[Sort]])
    equalToOneOf(e, solverTypes.toArray)
  }

  override protected def mkTypeConstraintForAddrExpr(typeFun: AST, typeToSolverConst: Map[Int, AST],
                                                     addr: AST, tc: Set[Int])(implicit zCtx: Z3SolverCtx): AST = {
    if (tc.isEmpty)
      mkBoolVal(boolVal = true)
    else {
      equalToOneOfTypes(typeFun.asInstanceOf[FuncDecl[Sort]].apply(addr.asInstanceOf[Expr[Sort]]), typeToSolverConst, tc)
    }
  }

  override protected def createTypeFun()(implicit zCtx: Z3SolverCtx): FuncDecl[UninterpretedSort] = {
    val args: Array[Sort] = Array(addrSort)
    zCtx.ctx.mkFuncDecl("addressToTypeFn", args, typeSort)
  }

  def uCombName(name: String): String = s"ucomb__$name"

  override protected def mkUcomb(name: String, args: List[AST])(implicit zCtx: Z3SolverCtx): AST = {
    val ctx = zCtx.ctx
    val argsort: Array[Sort] = args.indices.map(_ => ctx.getBoolSort).toArray
    val fun = ctx.mkFuncDecl(uCombName(name), argsort, ctx.getBoolSort)
    val argsCast: Array[Expr[BoolSort]] = args.map(_.asInstanceOf[Expr[BoolSort]]).toArray
    fun.apply(argsCast: _*)
  }

  override protected def mkForallAddr(name: PureVar, cond: AST => AST)(implicit zCtx: Z3SolverCtx): AST = {

    val j = mkFreshPv(name)
    zCtx.ctx.mkForall(Array(j), cond(j).asInstanceOf[BoolExpr], 1, null, null, null, null)
  }

  override protected def mkForallAddr(nameToAST: Map[PureVar, AST], cond: Map[PureVar, AST] => AST)
                                     (implicit zCtx: Z3SolverCtx): BoolExpr = {
    if (nameToAST.isEmpty) {
      cond(Map()).asInstanceOf[BoolExpr]
    } else {
      val j = nameToAST.map { case (_, v) => v.asInstanceOf[Expr[UninterpretedSort]] }.toSet
      zCtx.ctx.mkForall(j.toArray,
        cond(nameToAST).asInstanceOf[Expr[BoolSort]], 1,
        null, null, null, null)
    }
  }


  override protected def mkExistsT(t: List[AST], cond: AST)(implicit zCtx: Z3SolverCtx): AST = {
    if (t.nonEmpty) {
      val tc: Array[Expr[_]] = t.map(v => v.asInstanceOf[Expr[UninterpretedSort]]).toArray
      zCtx.ctx.mkExists(tc, cond.asInstanceOf[BoolExpr], 1, null, null, null, null)
    } else cond
  }

  override protected def mkExistsAddr(name: PureVar, cond: AST => AST)(implicit zCtx: Z3SolverCtx): AST = {
    val j = mkFreshPv(name)
    zCtx.ctx.mkExists(Array(j), cond(j).asInstanceOf[BoolExpr], 1, null, null, null, null)
  }

  override protected def mkExistsAddr(nameToAST: Map[PureVar, AST],
                                      cond: Map[PureVar, AST] => AST)
                                     (implicit zCtx: Z3SolverCtx): BoolExpr = {
    if (nameToAST.isEmpty) {
      cond(Map()).asInstanceOf[BoolExpr]
    } else {
      val j = nameToAST.map { case (_, v) => v.asInstanceOf[Expr[UninterpretedSort]] }.toSet
      zCtx.ctx.mkExists(j.toArray,
        cond(nameToAST).asInstanceOf[Expr[BoolSort]], 1,
        null, null, null, null)
    }
  }

  override protected def mkFreshPv(pv: PureVar)(implicit zCtx: Z3SolverCtx): Expr[UninterpretedSort] = {
    val pvName = mkPvName(pv)
    zCtx.ctx.mkFreshConst(pvName, addrSort)
  }

  /**
   * there exists an int in (min,max) such that condition is true
   *
   * @param cond function from const to boolean expression
   * @return
   */
  protected def mkExistsInt(min: AST, max: AST, cond: AST => AST)(implicit zCtx: Z3SolverCtx): AST = {
    val j = zCtx.ctx.mkFreshConst("i", zCtx.ctx.mkIntSort()).asInstanceOf[ArithExpr[ArithSort]]
    val range = mkAnd(List(mkLt(min, j), mkLt(j, max)))
    zCtx.ctx.mkExists(Array(j), mkAnd(range, cond(j)).asInstanceOf[BoolExpr]
      , 1, null, null, null, null)
  }

  override protected def mkImplies(t: AST, t1: AST)(implicit zCtx: Z3SolverCtx): AST = {
    zCtx.ctx.mkImplies(t.asInstanceOf[BoolExpr], t1.asInstanceOf[BoolExpr])
  }

  override protected def mkLocalFn()(implicit zCtx: Z3SolverCtx): FuncDecl[_] = {
    zCtx.ctx.mkFuncDecl(s"localfn_", localSort, addrSort)
  }

  def mkDynFieldName(fieldName: String): String = s"dynField_${fieldName}_"

  override protected def mkDynFieldFn(fieldName: String)(implicit zCtx: Z3SolverCtx): FuncDecl[_] = {
    val addrAddr: Array[Sort] = Array(addrSort, addrSort)
    val fun = zCtx.ctx.mkFuncDecl(mkDynFieldName(fieldName), addrAddr, zCtx.ctx.mkBoolSort)
    fun
  }

  override protected def mkINameFn()(implicit zCtx: Z3SolverCtx): FuncDecl[UninterpretedSort] = {
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

  protected def mkArgFun(i: Int)(implicit zCtx: Z3SolverCtx): FuncDecl[BoolSort] = {
    //    if(zCtx.args.isEmpty){
    //      zCtx.args = mkArgs(MAX_ARGS)
    //    }
    //    val argSort:Sort = mkArgSort()
    zCtx.setArgUsed(i)
    val args: Array[Sort] = Array(msgSort, addrSort)
    zCtx.ctx.mkFuncDecl(s"argfun_$i", args, zCtx.ctx.mkBoolSort())
  }

//  protected def mkConstValueConstraint(addr: AST)(implicit zCtx: Z3SolverCtx): AST = {
//    val constFn = zCtx.ctx.mkFuncDecl("constFn", addrSort, constSort)
//    constFn.apply(addr.asInstanceOf[Expr[UninterpretedSort]])
//  }

  override protected def mkIName(enum: AST, enumNum: Int)(implicit zCtx: Z3SolverCtx): AST = {
    enum.asInstanceOf[EnumSort[_]].getConst(enumNum)
  }

  override protected def mkNames(types: List[String])(implicit zCtx: Z3SolverCtx): Map[String, AST] = {
    val tmap: Map[String, AST] = types.map(t => (t -> zCtx.ctx.mkConst(t, iNameSort))).toMap
    tmap
  }

  override protected def mkNameConstraint(nameFun: AST, msg: AST)(implicit zCtx: Z3SolverCtx): AST = {
    nameFun.asInstanceOf[FuncDecl[_]].apply(msg.asInstanceOf[Expr[Sort]])
  }

  override protected def mkArgConstraint(argIndex: Int, msg: AST, addr: AST)(implicit zCtx: Z3SolverCtx): AST = {
    val argFun = mkArgFun(argIndex)
    argFun.asInstanceOf[FuncDecl[_]].apply(msg.asInstanceOf[Expr[UninterpretedSort]],
      addr.asInstanceOf[Expr[UninterpretedSort]])
  }

  //  private def mkArgConstraint(argFun:AST,
  //                              arg:Expr[UninterpretedSort],
  //                              msg:Expr[UninterpretedSort])(implicit zCtx:Z3SolverCtx):AST = {
  //    argFun.asInstanceOf[FuncDecl[_]].apply(arg,
  //      msg)
  //  }

  override protected def mkAddrConst(i: Int)(implicit zCtx: Z3SolverCtx): AST = {
    zCtx.ctx.mkConst(s"addr_const$i", addrSort)
  }

  override protected def mkMsgConst(i: Int, msg: Option[TraceElement])(implicit zCtx: Z3SolverCtx): AST = {
    //    if(i == 0){
    //      assert(msg.contains(TInitial) || msg.isEmpty, "Initial trace element should be TInitial")
    //      return mkZeroMsg
    //    }
    val sig = (i, msg) match {
      //      case (_,Some(TInitial)) => throw new IllegalArgumentException("bad initial message position")
      case (_, Some(TCLInit(_))) => ???
      case (_, Some(TNew(_, _))) => ???
      case (i, Some(TMessage(mType, method, _, _))) => s"${mType}_${method.sig.methodSignature}_$i"
      case (i, None) => s"__unn__$i"
    }
    zCtx.ctx.mkConst(s"msgat_$sig", msgSort)
  }


  override protected def mkDistinct(pvList: Iterable[PureVar], pvMap: Map[PureExpr, AST])(implicit zCtx: Z3SolverCtx): AST = {
    if (pvList.isEmpty) {
      mkBoolVal(boolVal = true)
    } else {
      zCtx.ctx.mkDistinct(pvList.map { a =>
        pvMap(a).asInstanceOf[Expr[UninterpretedSort]]
      }.toArray: _*)
    }
  }

  override protected def mkDistinctT(pvList: Iterable[AST])(implicit zCtx: Z3SolverCtx): AST = {
    if (pvList.isEmpty) {
      mkBoolVal(boolVal = true)
    } else {
      zCtx.ctx.mkDistinct(pvList.map { a => a.asInstanceOf[Expr[UninterpretedSort]] }.toArray: _*)
    }
  }

  override protected def persist: ClassHierarchyConstraints = persistentConstraints


  //TODO: hack to go b
  def functFromName(name: String)(implicit zCtx: Z3SolverCtx): FuncDecl[_] = {
    if (name == "msgLTE") {
      msgLTE
      //    else if (name == "constFn")
      //      mkConstFn
    } else if (name == "localfn_")
      mkLocalFn
    else if (name == "addressToTypeFn")
      createTypeFun
    else if (name.startsWith("dynField_")) { //"dynField_f_")
      val fieldName = name.dropWhile(c => c != '_').drop(1).dropRight(1)
      val fn = mkDynFieldFn(fieldName)
      val funName = fn.getName.toString
      assert(funName == name, s"failed to extract field name: ${name}")
      fn
    } else if (name.startsWith("traceFn")) {
      mkTraceFn()
    } else if (name.startsWith("namefn_")) {
      mkINameFn()
    } else if (name.startsWith("argfun_")) {
      val ind = name.split("_")(1)
      mkArgFun(ind.toInt)
    } else
      ???
  }

  def constNameToSort(constName: String)(implicit zCtx: Z3SolverCtx): Sort = {
    def st(s: String): Boolean = constName.startsWith(s)

    if (st("type_"))
      typeSort
    else if (st("staticField_")) {
      addrSort
    } else if (st("addr_const")) {
      addrSort
    } else if (st("msgat_") || st("msg_") || st("zeroMessage___")) {
      msgSort
    } else if (st("local_")) {
      localSort
      //    } else if (st("const_"))
      //      constSort
    }else if (st("pv-") || st("npv-") || st("a1!") || st("a2!") || st("a3!"))
      addrSort
    else if (st("I_CB") || st("I_CI") || st("iname_"))
      iNameSort
    else if (st("OTHEROTHEROTHER") || st("INITINIT"))
    //msgSort
      iNameSort
    else {
      ???
    }
  }


  override protected def mkTypeConstraints(types: Set[Int])(implicit zCtx: Z3SolverCtx): (AST, Map[Int, AST]) = {
    val typeMap = types.map(t => (t -> zCtx.ctx.mkConst(s"type_$t", typeSort))).toMap
    val allConstraints = typeMap.map { case (_, c) => c }
    val unique = mkDistinctT(allConstraints)
    (unique, typeMap)
  }

  override protected def mkLocalConstraint(localIdent: AST, equalTo: AST)
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

  override protected def mkStaticFieldConstraint(clazz: String, fieldName: String, equalTo: AST)
                                                (implicit zCtx: Z3SolverCtx): AST = {
    val staticField = zCtx.ctx.mkConst(s"staticField___${clazz}___${fieldName}", addrSort) //.mkFuncDecl(s"dynField_${fieldName}_${uid}", addrSort)
    mkEq(staticField, equalTo)
  }

  def localToName(local: (String, Int)): String = s"local_${local._1}____${local._2}"

  override protected def mkLocalDomain(locals: Set[(String, Int)])
                                      (implicit zCtx: Z3SolverCtx): (AST, Map[(String, Int), AST]) = {
    val ctx = zCtx.ctx
    val localMap = locals.map(t => (t -> ctx.mkConst(localToName(t), localSort))).toMap
    val allConstraints: immutable.Iterable[Expr[UninterpretedSort]] = localMap.map { case (_, c) => c }
    val unique = mkDistinctT(allConstraints)
    (unique, localMap)
  }

  def fieldToName(fld: String): String = {
    s"field_${fld}"
  }

  protected def mkConstConstraintsMap(pvs: Set[PureVal])(implicit zCtx: Z3SolverCtx): Map[PureVal, AST] = {
    val ctx = zCtx.ctx
    val constMap = pvs.map { t =>
      t -> ctx.mkConst(t.solverName, addrSort)
    }.toMap
    constMap
  }

  private def iNameString = "inames"

  protected def typeSort(implicit zCtx: Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort("ClassTypes")

  // index sort used before msg was the order
  //  private def indexSort(implicit zCtx: Z3SolverCtx):UninterpretedSort = zCtx.ctx.mkUninterpretedSort("Uint")
  protected def addrSort(implicit zCtx: Z3SolverCtx) = zCtx.ctx.mkUninterpretedSort("Addr")

  protected def msgSort(implicit zCtx: Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort("Msg")

//  protected def constSort(implicit zCtx: Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort("ConstVals")

  protected def localSort(implicit zCtx: Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort("Locals")

  protected def iNameSort(implicit zCtx: Z3SolverCtx): UninterpretedSort = zCtx.ctx.mkUninterpretedSort(iNameString)

  /**
   * create msgLTE function such that (msgLTE X Y) means X ≤ Y
   */
  private def msgLTE(implicit zCtx: Z3SolverCtx): FuncDecl[BoolSort] = {
    val msgMsg: Array[Sort] = Array(msgSort, msgSort)
    zCtx.ctx.mkFuncDecl("msgLTE", msgMsg, zCtx.ctx.mkBoolSort)
  }

//  private def mkConstFn(implicit zCtx: Z3SolverCtx): FuncDecl[UninterpretedSort] = {
//    zCtx.ctx.mkFuncDecl("constFn", addrSort, constSort)
//  }

  override def initializeNameAxioms(messageTranslator: MessageTranslator)(implicit zCtx: Z3SolverCtx): Unit = {
    if (!zCtx.uninterpretedTypes.contains(iNameString)) {
      val u = zCtx.ctx.mkFreshConst("iname_u", iNameSort)
      val tmap = mkNames(messageTranslator.inamelist)
      val eachT = mkOr(tmap.map { case (_, v) => mkEq(u, v) }).asInstanceOf[BoolExpr]
      val tOnly = tmap.map { case (_, v) => v.asInstanceOf[Expr[UninterpretedSort]] }
      mkAssert(zCtx.ctx.mkForall(Array(u), eachT, 1, null, null, null, null))
      mkAssert(zCtx.ctx.mkDistinct(tOnly.toArray: _*))
    }
  }

  override def initalizeConstAxioms(messageTranslator: MessageTranslator)(implicit zCtx: Z3SolverCtx): Unit = {
    val constMap = mkConstConstraintsMap(messageTranslator.pureValSet)
    val allConstraints = constMap.map {
      case (_, c) => c.asInstanceOf[Expr[UninterpretedSort]]
    }
    val unique = mkDistinctT(allConstraints)
    mkAssert(unique)
  }

  override def initializeZeroAxioms(messageTranslator: MessageTranslator)(implicit zCtx: Z3SolverCtx): Unit = {
    val ctx = zCtx.ctx
    val lte = msgLTE
    if (!zCtx.isZeroInitialized) {
      zCtx.initializeZero
      val x = ctx.mkFreshConst("msg_x", msgSort)
      // ** All messages are greater than or equal to zero
      // forall x. zero ≤ x
      val zeroLTE: BoolExpr = lte.apply(mkZeroMsg, x).asInstanceOf[BoolExpr]
      mkAssert(ctx.mkForall(Array(x), zeroLTE, 1, null, null, null, null))
      val nameFN = mkINameFn()
      mkAssert(mkEq(nameFN.apply(mkZeroMsg), messageTranslator.getZeroMsgName))
    }
  }

  override def initializeFieldAxioms(messageTranslator: MessageTranslator)(implicit zCtx: Z3SolverCtx): Unit = {
    val fieldNames: Iterable[String] = messageTranslator.dynFieldSet.map(mkDynFieldName)
    fieldNames.foreach { fieldName =>
      val fun = mkDynFieldFn(fieldName)
      if (!zCtx.initializedFieldFunctions.contains(fieldName)) {
        val a1 = zCtx.ctx.mkFreshConst("a1", addrSort)
        val a2 = zCtx.ctx.mkFreshConst("a2", addrSort)
        val a3 = zCtx.ctx.mkFreshConst("a3", addrSort)

        val b = zCtx.ctx.mkForall(Array(a1, a2, a3),
          mkImplies(mkAnd(fun.apply(a1, a2), fun.apply(a1, a3)), mkEq(a2, a3)).asInstanceOf[BoolExpr],
          1, null, null, null, null)
        mkAssert(b)
        zCtx.initializedFieldFunctions.add(fieldName)
      }
    }
  }

  override def initializeArgTotalityAxioms(messageTranslator:MessageTranslator)(implicit zCtx: Z3SolverCtx):Unit = {
    val args = zCtx.getArgUsed()
    args.foreach{ arg =>
      val f = mkArgFun(arg)
      // Ɐ m:Msg. tracefn(msg) =>
      zCtx.mkAssert(mkForallMsg(msg => mkExistsAddr(NamedPureVar("argAddr"),
        (addr: AST) => f.apply(msg.asInstanceOf[Expr[UninterpretedSort]], addr.asInstanceOf[Expr[UninterpretedSort]]))))
    }
  }
  override def initializeArgFunAxioms(messageTranslator: MessageTranslator)(implicit zCtx: Z3SolverCtx): Unit = {
    val args = zCtx.getArgUsed()
    args.foreach { arg =>
      val f = mkArgFun(arg)
      // assert(forall((m Msg)(a1 Addr)(a2 Addr))( => (and(argfun_1 m a1)(argfun_1 m a2))( = a1 a2 ) ) ) )
      zCtx.mkAssert(mkForallMsg(msg =>
        mkForallAddr(NamedPureVar("a1"), (a1: AST) =>
          mkForallAddr(NamedPureVar("a2 "), (a2: AST) =>
            mkImplies(
              mkAnd(f.apply(msg.asInstanceOf[Expr[UninterpretedSort]], a1.asInstanceOf[Expr[UninterpretedSort]]),
                f.apply(msg.asInstanceOf[Expr[UninterpretedSort]], a2.asInstanceOf[Expr[UninterpretedSort]])),
              mkEq(a1, a2))
          ))))
    }
  }

  /**
   * Apply axioms to enforce total order to messages in history.
   * Note: this used to be an uninterpreted index sort, but was simplified to a total order over messages.
   *
   * @param zCtx z3 context object
   * @return ≤ relation between messages
   */
  override def initializeOrderAxioms(messageTranslator: MessageTranslator)
                                    (implicit zCtx: Z3SolverCtx): Unit = {

    val ctx = zCtx.ctx
    val lte = msgLTE
    if (!zCtx.indexInitialized) {

      // Total ordering encoding used from: https://dl.acm.org/doi/pdf/10.1145/3140568
      // Paxos Made EPR: Decidable Reasoning about DistributedProtocols
      // figure 1
      // ** less than is transitive
      val x = ctx.mkFreshConst("msg_x", msgSort)
      val y = ctx.mkFreshConst("msg_y", msgSort)
      val z = ctx.mkFreshConst("msg_z", msgSort)
      //forall x . x≤x
      mkAssert(ctx.mkForall(Array(x), lte.apply(x, x), 1, null, null, null, null))

      // forall x,y,z. x≤y /\ y≤z => x≤z
      val trans: BoolExpr = mkImplies(mkAnd(lte.apply(x, y), lte.apply(y, z)), lte.apply(x, z)).asInstanceOf[BoolExpr]
      val b = ctx.mkForall(Array(x, y, z), trans, 1, null, null, null, null)
      mkAssert(b)

      //forall x,y. x≤y /\ y≤x => y = x
      mkAssert(ctx.mkForall(Array(x, y), ctx.mkImplies(ctx.mkAnd(lte.apply(x, y), lte.apply(y, x)), ctx.mkEq(x, y)),
        1, null, null, null, null))

      //forall x,y. x≤y \/ y≤x
      mkAssert(ctx.mkForall(Array(x, y), ctx.mkOr(lte.apply(x, y), lte.apply(y, x)),
        1, null, null, null, null))

      zCtx.indexInitialized = true
    }
  }

  override protected def encodeValueCreatedInFuture(v: AST, maxArgs: Int)(implicit zCtx: Z3SolverCtx): AST = {
    val ctx = zCtx.ctx
    val args = (0 until maxArgs)
    val m = ctx.mkConst("msg_all", msgSort)
    val vUnin = v.asInstanceOf[Expr[UninterpretedSort]]

    val pred = args.map(arg => mkNot(mkArgFun(arg).apply(m, vUnin))).reduce(mkAnd).asInstanceOf[BoolExpr]
    ctx.mkForall(Array(m), pred, 1, null, null, null, null)
  }

  private lazy val logger =
    LoggerFactory.getLogger("Z3StateSolver")

  override def getLogger: Logger = logger

  override protected def mkTraceFn()(implicit zCtx: Z3SolverCtx): FuncDecl[BoolSort] = {
    val ctx = zCtx.ctx
    ctx.mkFuncDecl("traceFn", msgSort, ctx.mkBoolSort())
  }

  override protected def mkTraceFnContains(traceFn: AST, v: AST)(implicit zCtx: Z3SolverCtx): Expr[BoolSort] = {
    val iTraceFn = traceFn.asInstanceOf[FuncDecl[BoolSort]]
    iTraceFn.apply(v.asInstanceOf[Expr[UninterpretedSort]])
  }


  override protected def mkExistsMsg(traceFn: AST, cond: AST => AST)(implicit zCtx: Z3SolverCtx): Expr[BoolSort] = {
    val ctx = zCtx.ctx
    val j = zCtx.ctx.mkFreshConst("msg_j", msgSort)
    val cond2: BoolExpr = ctx.mkAnd(
      mkTraceFnContains(traceFn, j), cond(j).asInstanceOf[BoolExpr])
    ctx.mkExists(Array(j), cond2
      , 1, null, null, null, null)
  }

  override protected def mkForallTraceMsg(traceFn: AST, cond: AST => AST)(implicit zCtx: Z3SolverCtx): AST = {
    val ctx = zCtx.ctx
    val j = zCtx.ctx.mkFreshConst("msg_j", msgSort)
    val cond2 = ctx.mkImplies(mkTraceFnContains(traceFn, j), cond(j).asInstanceOf[BoolExpr])
    ctx.mkForall(Array(j), cond2
      , 1, null, null, null, null)
  }

  override protected def mkForallMsg(cond: AST => AST)(implicit zCtx: Z3SolverCtx): AST ={
    val ctx = zCtx.ctx
    val j = zCtx.ctx.mkFreshConst("msg_j", msgSort)
    val cond2 = cond(j).asInstanceOf[BoolExpr]
    ctx.mkForall(Array(j), cond2
      , 1, null, null, null, null)
  }

  override protected def mkLTEMsg(ind1: AST, ind2: AST)(implicit zctx: Z3SolverCtx): AST =
    msgLTE.apply(ind1.asInstanceOf[Expr[UninterpretedSort]], ind2.asInstanceOf[Expr[UninterpretedSort]])

  override protected def mkLTMsg(ind1: AST, ind2: AST)(implicit zctx: Z3SolverCtx): AST =
    mkAnd(mkLTEMsg(ind1,ind2), mkNot(mkEq(ind1,ind2)))

  override protected def mkAddOneMsg(traceFn:AST, ind: AST)(implicit zctx: Z3SolverCtx): (AST, AST) = {
    val mConst = zctx.ctx.mkFreshConst("msg_",msgSort)

    val req = mkForallTraceMsg(traceFn, m => mkOr(List(mkLTEMsg(m,ind), mkLTEMsg(mConst,m))) )

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

  /**
   * Encode set of something in z3
   * @param values names of things in set
   * @param typeName name of set (must be unique from other sets)
   * @param allEqualToSomeValue true if every element of this set must be equal to a member of values
   * @param eachValueDistinct no two elements of this set may be equal
   */
  case class Z3SetEncoder(values:Set[Nameable],
                          typeName:String,
                          allEqualToSomeValue:Boolean = true,
                          eachValueDistinct:Boolean = true,
                         ) extends SetEncoder[AST, Z3SolverCtx]{
    private var nameableToSolver: Option[Map[Nameable,Expr[UninterpretedSort]]] = None
    private def init()(implicit zCtx: Z3SolverCtx):Unit = {
      if(nameableToSolver.isEmpty){
        val ctx = zCtx.ctx
        nameableToSolver = Some(values.map{v => v -> ctx.mkConst(v.solverName, getSort)}.toMap)
      }
    }

    def getSort(implicit zCtx: Z3SolverCtx):UninterpretedSort = zCtx.ctx.mkUninterpretedSort(typeName)
    def solverExprFor(n:Nameable)(implicit zCtx: Z3SolverCtx):Expr[UninterpretedSort] = {
      init()
      nameableToSolver.get(n)
    }

    override def getAxioms()(implicit zCtx: Z3SolverCtx): Expr[BoolSort] = {
      init()
      val ctx = zCtx.ctx
      val upperBound = if(allEqualToSomeValue) {
        val v = ctx.mkFreshConst("v", getSort)
        val condList: Array[BoolExpr] = nameableToSolver.get.values.map{ nv => ctx.mkEq(v,nv)}.toArray
        val cond = mkOr(condList).asInstanceOf[BoolExpr]
        Some(ctx.mkForall(Array(v),cond, 1,null,null,null,null))
      } else None

      val lowerBound = if(eachValueDistinct)
        Some(ctx.mkDistinct(nameableToSolver.get.values.toArray:_*))
      else None
      mkAnd(List(upperBound, lowerBound).flatten)
    }
  }

  //TODO: de-duplicate this logic for names, const values, addresses, and allocation sites
  override def getSetEncoder(values:Set[Nameable],
                             typeName:String,
                             allEqualToSomeValue:Boolean = true,
                             eachValueDistinct:Boolean = true,
                            ):SetEncoder[AST, Z3SolverCtx] =
    Z3SetEncoder(values, typeName, allEqualToSomeValue, eachValueDistinct)

  override def mkAssert(t: AST)(implicit zCtx: Z3SolverCtx): Unit = {
    //z3ExprToSmtLib(t) match { //TODO: Open bug on this to look at later, toString was taking too long
    //  case FunctionApplication(fun, terms) if fun.id.symbol.name == "distinct" && terms.size < 2 =>
    //    return
    //  case QualifiedIdentifier(id,_) if id.symbol.name == "true" =>
    //    return
    //  case _ =>
    //}
    // note: attempted to prune unused quantifiers to address timeout, does not seem to work
    // left smtlib conversion code because it seems useful for debug.
    //val pruned = pruneUnusedQuant(t)
    val pruned = t
    zCtx.mkAssert(pruned)
  }

  override def STRICT_TEST: Boolean = this.strict_test
}
