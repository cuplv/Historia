package edu.colorado.plv.bounder.solver

import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppMethod, BitTypeSet, EmptyTypeSet, MessageType, PrimTypeSet, TMessage, TopTypeSet, Trace, TraceElement, TypeSet, WitnessExplanation}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecSpace}
import edu.colorado.plv.bounder.lifestate.LifeState._
import edu.colorado.plv.bounder.solver.EncodingTools.repHeapCells
import edu.colorado.plv.bounder.symbolicexecutor.SubsumptionMode
import edu.colorado.plv.bounder.symbolicexecutor.state.{HeapPtEdge, _}
import org.slf4j.{Logger, LoggerFactory}
import upickle.default.{read, write}

import scala.annotation.tailrec
import scala.collection.{immutable, mutable}

//TODO: replace all "sets of things" with SetOfEncoder
trait Nameable{
  def solverName:String
}

trait SetEncoder[T, C <: SolverCtx[T]]{
  def getAxioms()(implicit zCtx:C):T
}

trait SolverCtx[T]{
  //def mkAssert(t:T):Unit
  def acquire(randomSeed:Option[Int] = None):Unit
  def release():Unit
}

sealed trait SubsumptionMethod

/**
 * Encode subsumption as Z3 query
 */
case object SubsZ3 extends SubsumptionMethod

/**
 * Use a subtraction/unification like algorithm like O'Hearn papers
 */
case object SubsUnify extends SubsumptionMethod

/**
 * Use both subsumption methods and assert the results are the same
 */
case object SubsDebug extends SubsumptionMethod

/**
 * Try using Unify and if that fails use Z3
 */
case object SubsFailOver extends SubsumptionMethod
/** SMT solver parameterized by its AST or expression type */
trait StateSolver[T, C <: SolverCtx[T]] {
  def shouldLogTimes:Boolean
  def STRICT_TEST:Boolean
  def mkAssert(t:T)(implicit zCtx:C):Unit
  def pruneUnusedQuant(t: T)(implicit zCtx:C): T

  /**
   *
   * @param values A directed graph representing the lattice, all transitive edges must exist,
   *               An implicit edge from top to all other edges exists.
   *               For single distinct elements, create an edge from the element to Bot
   * @param typeName solver name for types in this lattice
   * @param closed Are all values represented by the lattice or are "other" values possible
   * @return
   */
  def getSetEncoder(values:Set[Nameable],
                    typeName:String,
                    allEqualToSomeValue:Boolean = true,
                    eachValueDistinct:Boolean = true,
                   ):SetEncoder[T,C]
  def setSeed(v:Int)(implicit zCtx: C):Unit
  // checking
  def getSolverCtx(overrideTimeout:Option[Int] = None): C
  def getLogger:Logger
  def iDefaultOnSubsumptionTimeout(implicit zCtx:C):Boolean

  // axiom initializers add interpreted properties to uninterpreted domains e.g. zero, heap cells, message order
  def initializeZeroAxioms(messageTranslator: MessageTranslator)(implicit zCtx:C):Unit


  def initializeArgFunAxioms(messageTranslator:MessageTranslator)(implicit zCtx: C):Unit
  def initializeArgTotalityAxioms(messageTranslator:MessageTranslator)(implicit zCtx: C):Unit
  def initializeOrderAxioms(messageTranslator: MessageTranslator)(implicit zCtx:C):Unit

  def initializeFieldAxioms(messageTranslator: MessageTranslator)(implicit zCtx:C):Unit

  def initializeNameAxioms(messageTranslator: MessageTranslator)(implicit zCtx:C):Unit

  def initalizeConstAxioms(messageTranslator: MessageTranslator)(implicit zCtx:C):Unit

  def solverString(messageTranslator: MessageTranslator)(implicit zCtx:C):String

  /**
   *
   * @param messageTranslator object to encode field and message names in solver
   * @param axioms axioms for behavior of heap and message indices, none for default
   * @param zCtx solver context
   * @return whether formula is satisfiable
   */
  def checkSAT(messageTranslator: MessageTranslator,
                  axioms: Option[List[MessageTranslator => Unit] ] = None,
               shouldPushSat:Boolean
              )(implicit zCtx: C): Boolean
  /**
   * Check satisfiability of fomrula in solver
   * @throws IllegalStateException if formula is undecidable or times out
   * @param useCmd if true, call z3 using bash
   * @param zCtx solver context
   * @return satisfiability of formula
   */
  def checkSATOne(messageTranslator: MessageTranslator,
               axioms: List[MessageTranslator => Unit ])(implicit zCtx: C): Boolean

  /**
   * Try satisfiability with fewer axioms then add more if satisfiable.
   * If unsatisfiable, adding axioms won't chage result.
   * @param axioms list of functions that generate axioms adding interpretations to uninterpreted domains
   *               (initializeOrderAxioms, initializeFieldAxioms, initializeZeroAxiom)
   * @return satisfiability of formula
   */
  def checkSatPush(messageTranslator: MessageTranslator,
                   axioms: List[MessageTranslator => Unit ])(implicit zCtx: C):Boolean

  def push()(implicit zCtx: C): Unit

  def pop()(implicit zCtx: C): Unit

  /**
   * Write debugging info, delete if cont finishes without failure
   * Used to debug native crashes in solver
   *
   * @param cont call solver code in continuation, return result
   */
  protected def dumpDbg[V](cont: () => V)(implicit zCtx: C): V

  protected def mkUcomb(name:String, args:List[T])(implicit zctx: C):T
  protected def mkForallAddr(name: PureVar, cond: T => T)(implicit zctx: C): T

  protected def mkForallAddr(name: Map[PureVar, T], cond: Map[PureVar, T] => T)(implicit zCtx: C): T

  protected def mkExistsT(t:List[T], cond:T)(implicit zCtx: C):T
  protected def mkExistsAddr(name: PureVar, cond: T => T)(implicit zctx: C): T

  protected def mkExistsAddr(name: Map[PureVar,T], cond: Map[PureVar, T] => T)(implicit zCtx: C): T
  protected def mkFreshPv(pv:PureVar)(implicit zCtx:C):T

  protected def mkZeroMsg(implicit zCtx:C):T

  protected def mkTraceFn()(implicit zCtx:C):T

  protected def mkTraceFnContains(traceFn:T, v:T)(implicit zCtx:C):T

  protected def mkExistsMsg(traceFn:T, cond: T => T)(implicit zCtx: C): T

  protected def mkForallTraceMsg(traceFn:T, cond: T => T)(implicit zCtx: C): T
  protected def mkForallMsg(cond: T => T)(implicit zCtx:C):T

  protected def mkLTEMsg(ind1: T, ind2: T)(implicit zctx: C): T

  protected def mkLTMsg(ind1: T, ind2: T)(implicit zctx: C): T

  protected def mkAddOneMsg(tracefn:T, ind: T)(implicit zctx: C): (T, T)

  // comparison operations
  protected def mkEq(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkNe(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkLt(lhs: T, rhs: T)(implicit zctx: C): T

  // Logical operations
  protected def mkImplies(t: T, t1: T)(implicit zctx: C): T

  protected def mkNot(o: T)(implicit zctx: C): T

  protected def mkSub(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkAnd(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkAnd(t: Iterable[T])(implicit zctx: C): T

  protected def mkOr(lhs: T, rhs: T)(implicit zctx: C): T

  protected def mkOr(t: Iterable[T])(implicit zctx: C): T

  // creation of variables, constants, assertions
  protected def mkIntVal(i: Int)(implicit zctx: C): T

  protected def mkBoolVal(b: Boolean)(implicit zctx: C): T

  protected def mkLenVar(s: String)(implicit zCtx: C): T

  protected def mkAddrVar(pv: PureVar)(implicit zCtx: C): T

  protected def solverSimplify(t: T,
                               state: State,
                               messageTranslator: MessageTranslator,
                               logDbg: Boolean = false)(implicit zctx: C): Option[T]

  protected def mkTypeConstraints(types: Set[Int])(implicit zctx: C): (T, Map[Int, T])

  protected def mkLocalDomain(locals: Set[(String, Int)])(implicit zctx: C): (T, Map[(String, Int), T])

  protected def mkConstConstraintsMap(pvs: Set[PureVal])(implicit zctx: C): Map[PureVal, T]

  protected def mkTypeConstraintForAddrExpr(typeFun: T, typeToSolverConst: Map[Int, T],
                                            addr: T, tc: Set[Int])(implicit zctx: C): T

  protected def createTypeFun()(implicit zctx: C): T

  protected def mkNames(types: List[String])(implicit zctx: C): Map[String, T]

  protected def mkLocalFn()(implicit zctx: C): T

  protected def mkLocalConstraint(localIdent: T, equalTo: T)(implicit zctx: C): T

  protected def mkDynFieldFn(fieldName: String)(implicit zctx: C): T

  protected def mkDynFieldConstraint(base: T, fieldName: String, equalTo: T)(implicit zctx: C): T

  protected def mkStaticFieldConstraint(clazz: String, fieldName: String, equalTo: T)(implicit zctx: C): T

  // function msg -> iname
  protected def mkINameFn()(implicit zctx: C): T

  // functions for each argument msg -> addr
  //protected def mkArgFun(i:Int)(implicit zctx: C): T

  /**
   * Attempt to limit Uint and msg to fix z3 timeout
   *
   * @param n maximum number of uninterpreted integers
   * @param zCtx solver context
   * @return boolean asserting fixed Uint count
   */
//  protected def mkMaxMsgInd(n: Int)(implicit zCtx: C): T

//  protected def mkConstValueConstraint(addr: T)(implicit zctx: C): T

  // Get enum value for I based on index
  protected def mkIName(enum: T, enumNum: Int)(implicit zctx: C): T

  //TODO%%%% rm
  // function from index to message (message is at index in trace)
//  protected def mkTraceConstraint(traceFun: T, index: T)(implicit zctx: C): T

  // function msg -> funname
  protected def mkNameConstraint(nameFun: T, msg: T)(implicit zctx: C): T

  // function argumentindex -> msg -> argvalue
  protected def mkArgConstraint(argIndex: Int, msg: T, addr:T)(implicit zCtx: C): T

  protected def mkAddrConst(i: Int)(implicit zCtx: C): T

  protected def mkMsgConst(i:Int, msg:Option[TraceElement])(implicit zCtx:C): T

  def printDbgModel(messageTranslator: MessageTranslator, traceabst: Set[AbstractTrace])(implicit zCtx: C): Unit
  def explainWitness(messageTranslator:MessageTranslator,
                     pvMap: Map[PureExpr, T])(implicit zCtx:C): WitnessExplanation
//  def compareConstValueOf(rhs: T, op: CmpOp, pureVal: PureVal, constMap: Map[PureVal, T])(implicit zCtx: C): T =
//    (pureVal, op) match {
//      case (TopVal, _) => mkBoolVal(b = true)
//      case (ClassVal(_), _) => mkBoolVal(b = true) //TODO: add class vals if necessary for precision
//      case (v: PureVal, Equals) =>
//        if(!constMap.contains(v))
//          throw new IllegalStateException(s"Missing constant $v")
//        mkEq(constMap(v), rhs)
//      case (v: PureVal, NotEquals) =>
//        mkNot(mkEq(constMap(v), rhs))
//      case (_: PureVal, _) =>
//        mkBoolVal(b = true)
//      case v =>
//        println(v)
//        ???
//    }

  def toAST(p: PureConstraint, pvMap: Map[PureExpr, T])(implicit zctx: C): T = p match {
    case PureConstraint(v1, Equals, v2) => mkEq(pvMap(v1), pvMap(v2))
    case PureConstraint(v1, NotEquals, v2) => mkNot(mkEq(pvMap(v1), pvMap(v2)))
    case _ => ???
  }

//  def toAST(p: PureExpr, pvMap: Map[PureVar, T])(implicit zctx: C): T = p match {
//    case p: PureVar => pvMap(p)
//    case _ => throw new IllegalStateException("Values should be handled at a higher level")
//  }

  def toAST(lhs: T, op: CmpOp, rhs: T)(implicit zctx: C): T = op match {
    case Equals => mkEq(lhs, rhs)
    case NotEquals =>
      mkNe(lhs, rhs)
    case _ =>
      ???
  }

  private def msgModelsTraceElement(msg:T,
                                    element:TMessage,
                                    messageTranslator: MessageTranslator,
                                    argVals: Map[Int, T]
                                   )(implicit zCtx: C): T = {
    val nameFun = messageTranslator.nameFun
    val onceOpt = messageTranslator.iForMsg(element)
    val nameConstraint = onceOpt.map(o => mkEq(mkNameConstraint(nameFun, msg), messageTranslator.enumFromI(o)))
    val argConstraints:List[T] = element.args.zipWithIndex.map{
      case (ConcreteAddr(addr), argnum) => mkArgConstraint(argnum,msg, argVals(addr))
      case _ => ???
    }
    mkAnd(argConstraints.prependedAll(nameConstraint))
  }
  private def msgModelsOnce(msg:T,
                            once: AbsMsg,
                            messageTranslator: MessageTranslator,
                            lsTypeMap: Map[PureVar, TypeSet],
                            typeToSolverConst: Map[Int, T],
                            pvMap: PureExpr => T)(implicit zctx: C): T = {
    val nameFun = messageTranslator.nameFun
    val nameConstraint = mkEq(mkNameConstraint(nameFun, msg), messageTranslator.enumFromI(once))
    val argConstraints = once.lsVars.zipWithIndex.flatMap {
      case (TopVal, _) => None
      case (msgVar:PureVar, ind) =>
        val modelExpr = pvMap(msgVar)
        val typeConstraint = lsTypeMap.get(msgVar) match {
          case Some(BitTypeSet(s)) =>
              mkTypeConstraintForAddrExpr(createTypeFun(), typeToSolverConst, pvMap(msgVar), s.toSet)
          case _ => mkBoolVal(b = true)
        }
        Some(mkAnd(
          mkArgConstraint(ind, msg, modelExpr),
          typeConstraint
        ))
      case (const:PureVal, ind) =>
        Some(mkArgConstraint(ind,msg,messageTranslator.getConstMap()(const)))
    }

      mkAnd(nameConstraint, mkAnd(argConstraints))
  }

  private def msgModelsHNOE(msg: T,
                            hnoe:HNOE,
                            messageTranslator: MessageTranslator,
                            lsTypeMap: Map[PureVar, TypeSet],
                            typeToSolverConst: Map[Int, T],
                            pvMap: PureExpr => T)(implicit zctx: C): T = {
    val once = hnoe.m
    assert(once.lsVars.count(v => v == hnoe.v) == 1,
      s"Within HNOE. Once, ${once} , must contain one instance of ${hnoe.v}")
    val arityOfTgt: Int = once.lsVars.indexOf(hnoe.v)
    val nameFun = messageTranslator.nameFun
    val nameConstraint = mkNot(mkEq(mkNameConstraint(nameFun, msg), messageTranslator.enumFromI(once)))
    val argConstraints = once.lsVars.zipWithIndex.flatMap {
      case (TopVal, _) => None
      case (msgVar: PureVar, ind) if ind == arityOfTgt => None
      case (msgVar: PureVar, ind) if ind != arityOfTgt =>
        val modelExpr = pvMap(msgVar)
        val typeConstraint = lsTypeMap.get(msgVar) match {
          case Some(BitTypeSet(s)) =>
            mkTypeConstraintForAddrExpr(createTypeFun(), typeToSolverConst, pvMap(msgVar), s.toSet)
          case _ => mkBoolVal(b = true)
        }
        Some(mkOr(
          mkNot(mkArgConstraint(ind, msg, modelExpr)),
          mkNot(typeConstraint)
        ))
      case (const: PureVal, ind) =>
        Some(mkNot(mkArgConstraint(ind, msg, messageTranslator.getConstMap()(const))))

    }

    val targetArgEqu = mkArgConstraint(arityOfTgt, msg, pvMap(hnoe.extV))

    mkOr(nameConstraint, mkOr(targetArgEqu, mkOr(argConstraints) ))
  }


  protected def encodePred(combinedPred: LifeState.LSPred,
                         messageTranslator: MessageTranslator, pvMap: PureExpr => T,
                         typeToSolverConst: Map[Int, T],
                         typeMap: Map[PureVar, TypeSet])(implicit zctx: C): T = {
    val res = combinedPred match {
      case Forall(h::t, p) =>
        mkForallAddr(h, (v:T) => {
          val newModelVarMap:PureExpr => T = s => if(s == h) v else pvMap(s)
          encodePred(Forall(t, p), messageTranslator, newModelVarMap, typeToSolverConst, typeMap)
        })
      case Exists(h::t, p) =>
        mkExistsAddr(h, (v:T) => {
          val newModelVarMap:PureExpr => T = s => if(s == h) v else pvMap(s)
          encodePred(Exists(t, p), messageTranslator, newModelVarMap, typeToSolverConst, typeMap)
        })
      case Forall(Nil, p) =>
        encodePred(p, messageTranslator, pvMap, typeToSolverConst, typeMap)
      case Exists(Nil, p) =>
        encodePred(p, messageTranslator, pvMap, typeToSolverConst, typeMap)
      case LSImplies(l1,l2) => mkImplies(
        encodePred(l1, messageTranslator, pvMap, typeToSolverConst, typeMap),
        encodePred(l2, messageTranslator, pvMap, typeToSolverConst, typeMap)
      )
      case LSConstraint(v1, Equals,v2) =>
        mkEq(pvMap(v1), pvMap(v2))
      case LSConstraint(v1, NotEquals, v2) =>
        mkNot(mkEq(pvMap(v1), pvMap(v2)))
//      case LSConstraint(v1, op, c:PureVal) => toAST(PureConstraint(v1, op, c))
        //compareConstValueOf(modelVarMap(v1), op, c, constMap)
      case And(l1, l2) => mkAnd(encodePred(l1, messageTranslator,
        pvMap, typeToSolverConst, typeMap),
        encodePred(l2, messageTranslator, pvMap, typeToSolverConst, typeMap))
      case Or(l1, l2) => mkOr(encodePred(l1, messageTranslator, pvMap, typeToSolverConst,
        typeMap),
        encodePred(l2, messageTranslator, pvMap, typeToSolverConst, typeMap))
//      case Not(l) =>
//        mkNot(encodePred(l, traceFn, len, messageTranslator, modelVarMap, typeToSolverConst, typeMap, constMap))
      case Not(once:AbsMsg) =>
        //mkNot(encodePred(once,messageTranslator,modelVarMap,typeToSolverConst,typeMap,constMap))
        mkForallTraceMsg(mkTraceFn, msg =>
          mkNot(msgModelsOnce(msg,once, messageTranslator, typeMap, typeToSolverConst, pvMap)))
      case hnoe:HNOE =>
        mkForallTraceMsg(mkTraceFn, msg =>
          msgModelsHNOE(msg, hnoe, messageTranslator, typeMap, typeToSolverConst, pvMap)
        )
      case Not(p) => //throw new IllegalArgumentException(s"arbitrary negation of lspred is not supported: $p")
        mkNot(encodePred(p, messageTranslator, pvMap, typeToSolverConst, typeMap))
      case o: AbsMsg =>
        mkExistsMsg(mkTraceFn, msg => msgModelsOnce(msg, o, messageTranslator, typeMap, typeToSolverConst, pvMap))
      case NS(m1, m2) =>
        mkExistsMsg(mkTraceFn, msg1 => mkAnd(
          msgModelsOnce(msg1, m1, messageTranslator, typeMap, typeToSolverConst, pvMap),
          mkForallTraceMsg(mkTraceFn, msg2 => mkImplies(mkLTMsg(msg1,msg2),mkNot(msgModelsOnce(msg2, m2, messageTranslator,
            typeMap, typeToSolverConst, pvMap))))
        ))
      case FreshRef(v) =>
        ???
//        val msgAt: T => T = index => mkTraceConstraint(traceFn, index)
//        mkExistsIndex(mkZeroIndex, len, ind => mkValContainedInMsg(msgAt(ind), modelVarMap(v), negated = false))
//      case FreshRef(v) if negate =>
//        val msgAt: T => T = index => mkTraceConstraint(traceFn, index)
//        mkForallIndex(mkZeroIndex, len, ind => mkValContainedInMsg(msgAt(ind), modelVarMap(v), negated = true))
      case LSFalse =>
        mkBoolVal(b = false)
      case LSTrue =>
        mkBoolVal(true)
    }
    res
  }


  private def allITraceAbs(traceAbstractionSet: Set[AbstractTrace]): Set[AbsMsg] =
    traceAbstractionSet.flatMap(a => allI(a))


  private def allI(abs: AbstractTrace): Set[AbsMsg] = {
    abs.rightOfArrow.flatMap {
      case i: AbsMsg => Some(i)
      case _ => None
    }.toSet
  }

  private case class TraceAndSuffixEnc(trace: Option[T] = None) {

    /**
     *
     * @param traceConstraint list of constraints from applicable specs at trace point
     * @param zctx solver context
     * @return trace and suffix encoding object
     */
    def conjunctHistReq(traceConstraint:List[T])(implicit zctx: C):TraceAndSuffixEnc = {
      if(traceConstraint.isEmpty)
        return this
      // If we have two overlapping specs e.g.
      //  I(bar(x)) <= x = Foo() /\ x != null
      //  ¬I(bar(x)) <= x = Foo() /\ x == null
      // And a message x=Foo() then we have:
      // [x!=null => I(bar(x))] && [x=null => ¬I(bar(x))]

      if(trace.isDefined)
        this.copy(trace = Some(mkAnd(List(trace.get, mkAnd(traceConstraint) ))))
      else
        this.copy(trace = Some(mkAnd(traceConstraint)))
    }
  }


  /**
   * If a value must be created in the future, then it may not be referenced by any past messages.
   * @param v value created in the future
   * @return
   */
  protected def encodeValueCreatedInFuture(v:T, maxArgs:Int)(implicit zCtx:C):T

  /**
   * Encode .|>m1|>m2...
   *
   * @return
   */
  private def encodeTraceAbs(abs: AbstractTrace,
                             messageTranslator: MessageTranslator,
                             specSpace: SpecSpace,
                             shouldEncodeRef:Boolean = true,
                             definedPvMap:Map[PureVar, T],
                             debug: Boolean = false)(implicit zCtx: C): TraceAndSuffixEnc = {
    val typeToSolverConst = messageTranslator.getTypeToSolverConst
    val rhs: Seq[LSSingle] = abs.rightOfArrow
    val pvMap:Map[PureExpr,T] = (definedPvMap ++ messageTranslator.constMap).toMap

    // Instantiate and update specifications for each ▷m̂
    // only include the disallow if it is the last one in the chain
    val rulePreds: Set[LSPred] = EncodingTools.rhsToPred(rhs, specSpace).map(EncodingTools.simplifyPred)

    //Encode that each preceding |> constraint cannot be equal to an allocation
    def encodeRefV(rhs: Seq[LSSingle], previous:Set[PureVar] = Set()):Option[(LSPred, Set[FreshRef])] = rhs match {
      case (ref@FreshRef(v))::t =>
        val currentConstr: Set[LSConstraint] = previous.map{ other =>
            LSConstraint(other, NotEquals, v)
        }
        // TODO: constrain all args prior to not be equal to ref ======

        val c = currentConstr.reduceOption(And)
        val n = encodeRefV(t,previous)
        n.getOrElse((LSTrue, Set[FreshRef]())) match {
          case (lsPred, refs) =>
            Some((And(c.getOrElse(LSTrue),lsPred), refs + ref))
        }
      case Nil => None
      case h::t => encodeRefV(t, previous ++ h.lsVar )
    }
    val refVPred: Option[(LSPred, Set[FreshRef])] = if(shouldEncodeRef) encodeRefV(rhs) else None
    val preds = refVPred.map(_._1) ++ rulePreds

    val traceAndSuffixEnc:TraceAndSuffixEnc = TraceAndSuffixEnc()
    //TODO: why do I have model type map here if its always empty?
    val modelTypeMap = Map[PureVar,TypeSet]()
    val encoded = preds.foldLeft(traceAndSuffixEnc){(acc,p) =>
      val encodedPred = encodePred(p, messageTranslator, pvMap, typeToSolverConst,
        modelTypeMap)
      acc.conjunctHistReq(List(encodedPred))
    }
    val refs = refVPred.map(_._2).getOrElse(Set()).toList.map{
      case FreshRef(v) =>
        encodeValueCreatedInFuture(definedPvMap(v), messageTranslator.maxArgs)
    }
    encoded.conjunctHistReq(refs)
  }

  protected def mkDistinct(pvList: Iterable[PureVar], pvMap:Map[PureExpr,T])(implicit zctx: C): T

  protected def mkDistinctT(tList: Iterable[T])(implicit zctx: C): T

  protected def persist: ClassHierarchyConstraints

  private implicit val ch = persist

  def toAST(ll:Map[(String,Int), PureVar],pvMap:Map[PureExpr,T],
            messageTranslator: MessageTranslator)(implicit zctx:C):T = {
    val localConstraints: List[T] = ll.map { case (local, pureVar) =>
      mkLocalConstraint(messageTranslator.localDomain(local), pvMap(pureVar))
    }.toList
    mkAnd(localConstraints)
  }
  def toAST(heap: Map[HeapPtEdge, PureExpr], pvMap:Map[PureExpr,T])(implicit zctx: C): T = {
    // In addition to heap function, we assert that heap domain elements are distinct.
    // e.g. a^.f -> b^ * c^.f->d^ means a^ != c^
    // alternatively a^.f ->b^ * c^.g->d^ does not mean a^!=c^
    val fields = heap.groupBy {
      case (FieldPtEdge(_, fieldName), _) => fieldName
      case (StaticPtEdge(_, _), _) => "@static"
      case (ArrayPtEdge(_, _), _) => "@array"
    }
    val heapAst = fields.foldLeft(mkBoolVal(true)) { (acc, v) =>
      val pvList = v._2.flatMap {
        case (FieldPtEdge(pv, _), _) => Some(pv)
        case (StaticPtEdge(_, _), _) => None
        case (ArrayPtEdge(pv, _), _) => None //TODO: array encoding
      }
      mkAnd(acc, mkDistinct(pvList,pvMap))
    }

    //represent heap function
    val heapFunConst = heap.flatMap{
      case (FieldPtEdge(base,name),tgt) =>
        val out = Some(mkDynFieldConstraint(pvMap(base), name, pvMap(tgt)))
        out
      case (StaticPtEdge(clazz,name),tgt)  =>
        Some(mkStaticFieldConstraint(clazz,name, pvMap(tgt)))
      case (ArrayPtEdge(_,_),_) => None
    }.toList
    mkAnd(heapAst, mkAnd(heapFunConst))
  }

  def mkPvName(pv:PureVar): String = pv match {
    case NPureVar(id) => s"pv-${id}"
    case NamedPureVar(n) => s"npv-${n}"
  }

  /**
   * "[[_R_]]" from semantics
   *
   * @param state R ::= <O,M,P> where O is suffix of trace that may reach assertion
   *                M is separation logic memory
   *                P is pure vars
   *                call stack explicitly represented too (but may be elided from paper?)
   * @param messageTranslator mapping from I name to solver uninterpreted sort
   * @param maxWitness optional maximum trace length, if defined, debugging info is printed
   * @param zctx solver context
   * @return encoded formula for solver
   */
  def toASTState(state: State,
                       messageTranslator: MessageTranslator,
                       maxWitness: Option[Int] = None,
                       specSpace: SpecSpace,
                       negate:Boolean,
                       debug:Boolean = false)(implicit zctx: C): T =
    toASTStateWithPv(state,messageTranslator, maxWitness, specSpace,negate, debug, false)._1

  def toASTStateWithPv(state: State,
                       messageTranslator: MessageTranslator,
                       maxWitness: Option[Int] = None,
                       specSpace: SpecSpace,
                       negate:Boolean,
                       debug:Boolean = false,
                       exposePv:Boolean)(implicit zCtx: C): (T, Map[PureVar,T]) = {

    if(debug){
      println(s"encoding state: ${state}")
    }

    def withPVMap(pvMap:Map[PureVar, T]):T =  {
      val combMap:Map[PureExpr,T] = (pvMap ++ messageTranslator.getConstMap()).toMap
      val traceAbs = state.traceAbstraction
      val traceEnc: TraceAndSuffixEnc = encodeTraceAbs(traceAbs, messageTranslator,
        specSpace = specSpace, debug = debug, definedPvMap = pvMap)

      // typeFun is a function from addresses to concrete types in the program
      val typeFun = createTypeFun()

      // *** Pure constraints ***
      val pureAst = state.pureFormula.foldLeft(mkBoolVal(true))((acc, v) =>
          mkAnd(acc, toAST(v, combMap))
      )

      // *** Type constraints
      val tc = state.typeConstraints
      val encodedTypeConstraints = encodeTypeConstraints(tc, typeFun, messageTranslator, pvMap)

      // Encode locals
      val ll: Map[(String, Int), PureVar] = levelLocalPv(state)
      val localAST = toAST(ll, combMap,messageTranslator)

      // Encode heap
      val heapAst = toAST(state.heapConstraints, combMap)

      //TODO:Unclear if this adds any precision

      // Encode Ref (pv in heap or memory can't equal value created in the future)
      // pure values created in the future
      val refs = state.sf.traceAbstraction.rightOfArrow.flatMap{
        case FreshRef(v) => Some(v)
        case _ => None
      }
      // pure values referenced by separation logic
      val memPV: Set[PureVar] = ll.values.toSet ++ state.sf.heapConstraints.flatMap{
        case (StaticPtEdge(_,_),pv:PureVar) => Set(pv)
        case (FieldPtEdge(pv1,_),pv2:PureVar) => Set(pv1,pv2)
        case (StaticPtEdge(_,_),_) => Set.empty
        case (FieldPtEdge(pv1,_),_) => Set(pv1)
        case (ArrayPtEdge(_,_),_) =>
          ???
      }
      val refNeq = mkAnd(refs.flatMap{
        case r:PureVar =>
          Some(mkAnd(memPV.toList.map(l => mkNe(pvMap(r),pvMap(l)))))
        case _ => None
      })

      val out = mkAnd(List(refNeq, pureAst, localAST, heapAst, encodedTypeConstraints) ++ traceEnc.trace)
      maxWitness match{
        case None => out
        case Some(len) => mkAnd(out, //max length means each message needs to be equal to one of len consts
          mkForallTraceMsg(mkTraceFn, m => //note: 0 mkMsgConst makes "zero" message equality
            mkOr((0 until len).map(i => mkEq(m,mkMsgConst(i,None))).toList)))
      }
    }

    val statePV = state.pureVars()

    val pureVars: Map[PureVar,T] = statePV.map{pv => pv -> mkFreshPv(pv)}.toMap

    val res = if(exposePv){
      assert(!negate, "cannot negate and expose pv")
      mkAnd(withPVMap(pureVars),messageTranslator.mkConstDistinct(pureVars, state.pureVars()))
    }else if(negate) {
      mkForallAddr(pureVars, (m:Map[PureVar,T]) =>
        mkImplies(messageTranslator.mkConstDistinct(m, state.pureVars()),mkNot(withPVMap(m))))
    }else {
      mkExistsAddr(pureVars, (m:Map[PureVar,T]) => mkAnd(withPVMap(m),
        messageTranslator.mkConstDistinct(m, state.pureVars())))
    }
    (res,pureVars)
  }

  private def encodeTypeConstraints(tc: Map[PureVar, TypeSet], typeFun:T,messageTranslator: MessageTranslator,
                                    pvMap:Map[PureVar,T] )(implicit zCtx:C): T = {

    val typeConstraints = tc.map { case (k, v) => k -> v.getValues }
    mkAnd(typeConstraints.flatMap {
      case (pv, Some(ts)) =>
        val tc = mkTypeConstraintForAddrExpr(typeFun, messageTranslator.getTypeToSolverConst, pvMap(pv), ts)
        Some(tc)
      case _ => None
    }.toList)

  }

  object MessageTranslator {
    def getAllI(states: Iterable[State], specSpace: Iterable[SpecSpace]): Set[AbsMsg] = {
      allITraceAbs(states.map(_.traceAbstraction).toSet) ++ specSpace.flatMap(_.allI)
    }

    def dynFieldSet(states: Iterable[State]): Set[String] = {
      states.flatMap { s =>
        s.sf.heapConstraints.flatMap {
          case (FieldPtEdge(_, fieldName), _) => Some(fieldName)
          case _ => None
        }
      }.toSet
    }

    def pureValSet(states: Iterable[State]): Set[PureVal] = {
      states.flatMap {
        v => v.pureVals()
      }.toSet + NullVal + IntVal(0) + IntVal(1) //+ BoolVal(true) + BoolVal(false) + IntVal(0) + IntVal(1)

    }
    def typeValSet(states:Iterable[State])(implicit ctx: C):Set[Int] = {
      states.foldLeft(Set[Int]()){
        case (acc,s) => acc.union(allTypes(s))
      }
    }

    def localSet(states:Iterable[State]):Set[(String, Int)] = {
      states.flatMap{ state =>
        val localAtStackDepth: Map[(String, Int), PureVar] = levelLocalPv(state)
        val out = localAtStackDepth.keySet
        out
      }.toSet
    }
    def apply(states:Iterable[State], specs:Iterable[SpecSpace])(implicit ctx:C):MessageTranslator = {
      MessageTranslator(states.toList,
        getAllI(states,specs), dynFieldSet(states), pureValSet(states), typeValSet(states),
        localSet(states))
    }
    def apply(preds:Iterable[LSPred])(implicit ctx:C):MessageTranslator = {
      val allI: Set[AbsMsg] = preds.flatMap{ p => SpecSpace.allI(p).asInstanceOf[Iterable[AbsMsg]]}.toSet
      val allPv = preds.flatMap{p => p.lsVar}
      MessageTranslator(Nil, allI, Set.empty, pureValSet(Nil), Set.empty, Set.empty)
    }
  }

  /**
   * An object to consistently translate messages and heap fields to consistent solver names
   * @param states for fields and message names
   * @param specSpace for message names
   * @param zCtx solver context
   */
  case class MessageTranslator(states:List[State], alli:Set[AbsMsg],dynFieldSet:Set[String], pureValSet:Set[PureVal],
                               allTypeValues:Set[Int],allLocal: Set[(String, Int)])(implicit zCtx: C) {
    // Trace messages
    private val inameToI: Map[String, Set[AbsMsg]] = alli.groupBy(_.identitySignature)
    // OTHER is name for unmodeled messages, INIT is name for first message
    lazy val inamelist = "OTHEROTHEROTHER"::"INITINIT" :: inameToI.keySet.toList
    private val identitySignaturesToSolver = mkNames(inamelist)
    val solverToIdentitySignature:List[(T,String)] = identitySignaturesToSolver.map{
      case (k,v) => (v,k)
    }.toList

    // Maximum arity of arguments in encoding
    lazy val maxArgs:Int = alli.foldLeft(1){
      case (acc,OAbsMsg(_, _, lsVars)) if lsVars.size>acc => lsVars.size
      case (acc,_) => acc
    }

    // Constants
    private val constMap1 = mkConstConstraintsMap(pureValSet)
    val constMap = constMap1 +
      (BoolVal(true)-> constMap1(IntVal(1))) + (BoolVal(false) -> constMap1(IntVal(0)))
    private val constSymb = constMap.values.toSet

    def mkConstDistinct(pvMap:Map[PureVar, T], pvSet:Set[PureVar]):T =
      pvSet.foldLeft(mkBoolVal(true)){case (acc,pv) =>
        mkAnd(acc::constSymb.map(const => mkNot(mkEq(pvMap(pv),const))).toList )}


    def getConstMap():Map[PureVal,T] = constMap
    //    zCtx.mkAssert(uniqueConst)

    // Types
//    private val allTypeValues =

    private val (typesUnique, typeToSolverConst: Map[Int, T]) = mkTypeConstraints(allTypeValues)
    mkAssert(typesUnique)
    def getTypeToSolverConst:Map[Int,T] = typeToSolverConst


    // Locals
    //    private val allLocal: Set[(String, Int)] =
    val (localDistinct, localDomain) = mkLocalDomain(allLocal)
    mkAssert(localDistinct)

    def getZeroMsgName:T =
      identitySignaturesToSolver("INITINIT")
    def enumFromI(m: AbsMsg): T = {
      if(identitySignaturesToSolver.contains(m.identitySignature))
        identitySignaturesToSolver(m.identitySignature)
      else
        throw new IllegalArgumentException(s"no key ${m.identitySignature}")
    }

    def nameFun: T = mkINameFn()

    def iForMsg(e: TraceElement): Option[AbsMsg] = e match{
      case TMessage(mType, method, _, _) =>
        val possibleI = alli.filter(ci => ci.contains(mType,method.fwkSig.get))
        //assert(possibleI.size < 2)
        possibleI.headOption
      case _ => None
    }

    def iForZ3Name(z3Name: String): Set[AbsMsg] = {
      inameToI.getOrElse(z3Name, Set())
    }

  }

  def simplify(state: State,specSpace: SpecSpace, maxWitness: Option[Int] = None): Option[State] = {
    implicit val zCtx = getSolverCtx()
    // val startTime = System.nanoTime()
    // var result = "unfinished"
    try {
      zCtx.acquire()

      // get rid of equal constraints in pure constraitns by inlining
      val inlinedStateOpt = state.inlineConstEq()
      if (inlinedStateOpt.isEmpty)
        return None
      val state2 = inlinedStateOpt.get

      if (state.isSimplified){
        // state previously simplified
        // result = "sat"
        return inlinedStateOpt
      }

      // if a stored value must be created in the future, state is infeasible
      val createdInFuture = state2.sf.traceAbstraction.rightOfArrow.flatMap {
        case FreshRef(v) => Some(v)
        case _ => None
      }
      val stackVarCreatedInFuture = state2.callStack.exists{
        case CallStackFrame(_,_,locals) => locals.values.exists{createdInFuture.contains}
      }


      if(stackVarCreatedInFuture)
        return None

      if(state2.sf.callStack.exists(frame => frame.locals.getOrElse(StackVar("@this"), NPureVar(-1)) == NullVal))
        return None

      @tailrec
      def equivSet( acc:Set[PureExpr]):Set[PureExpr] = {
        val eqRefPv = state2.sf.pureFormula.flatMap{
          case PureConstraint(lhs, Equals, rhs) if acc.contains(lhs) || acc.contains(rhs) => Set(lhs,rhs)
          case _ => Set.empty
        }
        val newAcc = acc ++ eqRefPv
        if(newAcc == acc)
          acc
        else
          equivSet(eqRefPv)
      }
//      def mustNotNull(pv:PureExpr):Boolean = pv match{
//        case NullVal => false
//        case pv:PureVar =>
//          state2.sf.pureFormula.forall{ // with pv reduction we eventually get to fields pointing to null directly
//            case PureConstraint(lhs, Equals, rhs) => pv != lhs && pv != rhs
//            case _ => true
//          }
//      }
      val heapPtEdgeCreatedInFuture = state2.sf.heapConstraints.exists{
        case (FieldPtEdge(base, _) , v) =>
          val equivV = equivSet(Set(v))
          //if(!equivV.contains(NullVal) ) { //TODO: pts to null ok for val created in future?
          val equiv = equivSet(Set(base)) ++ equivV
          equiv.exists(createdInFuture.contains)
          //} else false
        case (_:StaticPtEdge, v) if !equivSet(Set(v)).contains(NullVal) =>
          val equiv = equivSet(Set(v))
          equiv.exists(createdInFuture.contains)
        case _ => false
      }

      if(heapPtEdgeCreatedInFuture)
        return None


      // Drop useless constraints
//      val state2 = state.copy(sf = state.sf.copy(pureFormula = state.pureFormula.filter {
//        case PureConstraint(v1, Equals, v2) if v1 == v2 => false
//        case _ => true
//      }))

      // empty points to set means value must be null
      val nullsFromPt = state2.typeConstraints.filter(a => a._2.isEmpty)
      val stateWithNulls = nullsFromPt.foldLeft(state2) {
        case (state, (v, _)) => state.addPureConstraint(PureConstraint(v, Equals, NullVal))
      }.inlineConstEq().getOrElse{
        return None
      }

      val sat = {
        val (reducedPtState,_) = reducePtRegions(stateWithNulls,State.topState)
        val messageTranslator = MessageTranslator(List(reducedPtState), List(specSpace))

        // Only encode types in Z3 for subsumption check due to slow-ness

        val ast =
          toASTState(reducedPtState, messageTranslator, maxWitness,
            specSpace = specSpace, negate = false, debug = maxWitness.isDefined)

        if (maxWitness.isDefined) {
          println(s"State ${System.identityHashCode(state2)} encoding: ")
          println(ast.toString)
        }
        mkAssert(ast)
        checkSAT(messageTranslator, None, false)
      }
      //      val simpleAst = solverSimplify(ast, stateWithNulls, messageTranslator, maxWitness.isDefined)

      //      if(simpleAst.isEmpty)
      if (!sat) {
        // result = "unsat"
        None
      } else {
        // result = "sat"
        val reducedState = EncodingTools.reduceStatePureVars(stateWithNulls.setSimplified())
          .map(EncodingTools.gcPureVars)
        reducedState.map(_.setSimplified())
      }
    }finally{
      zCtx.release()
      //if(shouldLogTimes)
      //  getLogger.warn(s"feasibility result: ${result} time(µs): ${(System.nanoTime() - startTime) / 1000.0}")
    }
  }

  // TODO: call stack is currently just a list of stack frames, this needs to be updated when top is added
  def stackCanSubsume(cs1: List[CallStackFrame], cs2: List[CallStackFrame]): Boolean = (cs1, cs2) match {
    case (CallStackFrame(ml1, _, locals1) :: t1, CallStackFrame(ml2, _, locals2) :: t2) if ml1 == ml2 =>
      locals1.forall { case (k, v) => locals2.get(k).contains(v) } &&
        stackCanSubsume(t1, t2)
    case (Nil, Nil) => true
    case _ => false
  }

  private def canSwap(pv1:PureVar, pv2:PureVar, t1:Map[PureVar, TypeSet], t2:Map[PureVar, TypeSet]):Boolean = {
    val ts1 = t1.getOrElse(pv1, TopTypeSet)
    val ts2 = t2.getOrElse(pv2, TopTypeSet)
    ts1.contains(ts2)
  }
  /**
   * h2 => h1
   * @return mappings from pv in h1 to pv in h2 such that the renaming proves entailment
   */
  private def canSubsumeUnifyHeap(h1:Map[HeapPtEdge, PureExpr], h2:Map[HeapPtEdge, PureExpr],
                          ts1:Map[PureVar, TypeSet], ts2:Map[PureVar,TypeSet],
                          h1Swap:Map[PureVar,PureVar]):List[Map[PureVar,PureVar]] = {
    if(h1.isEmpty)
      List(h1Swap)
    else {
      val subs = h1.head match {
        case (FieldPtEdge(p1, fieldName1), t1: PureVar) =>
          h2.toList.flatMap {
            case (e2@FieldPtEdge(p2, fieldName2), t2: PureVar) if fieldName1 == fieldName2 =>
              if ((!h1Swap.contains(p1) || h1Swap(p1) == p2)  // check if values either not swapped or swapped with same
                && (!h1Swap.contains(t1) || h1Swap(t1) == t2)
                && canSwap(p1, p2, ts1, ts2) && canSwap(t1, t2, ts1, ts2))
                Some(h1Swap ++ Map(p1 -> p2, t1 -> t2), e2)
              else None //TODO: a.f -> b * c.f->b ├ a.f->b * c.f->c
            case _ => None
          }
        case (StaticPtEdge(clazz1, fieldName1), t1: PureVar) =>
          h2.toList.flatMap {
            case (e2@StaticPtEdge(clazz2, fieldName2), t2: PureVar) if clazz1 == clazz2 && fieldName1 == fieldName2 =>
              if ((!h1Swap.contains(t1) || h1Swap(t1) == t2)&&canSwap(t1, t2, ts1, ts2))
                Some(h1Swap ++ Map(t1 -> t2), e2)
              else
                None
            case _ => None
          }
      }
      if(subs.isEmpty) {
        Nil
      } else{
        val out: List[Map[PureVar, PureVar]] = subs.flatMap{
          case (varMap, edge) =>
            val nextH1 = h1.tail
            val nextH2 = h2 - edge
            canSubsumeUnifyHeap(nextH1,nextH2, ts1, ts2, varMap)
        }
        out
      }

    }
  }

  /**
   *
   * @return None if unification not possible, Some with mapping from pv in l1 to l2
   */
  private def canSubsumeUnifyLocals(l1:Map[(String,Int), PureVar], l2:Map[(String,Int),PureVar],
                                    ts1:Map[PureVar, TypeSet], ts2:Map[PureVar,TypeSet]): Option[Map[PureVar,PureVar]] = {
    Some(l1.map{
      case (k,v) if l2.contains(k) && canSwap(v, l2(k), ts1, ts2) => v -> l2(k)
      case _ => return None
    })
  }
  private def canSubsumeUnifyFreshRef(r1:Set[PureVar], r2:Set[PureVar],
                                      ts1:Map[PureVar, TypeSet], ts2:Map[PureVar,TypeSet],
                                      r1Swap:Map[PureVar, PureVar]):List[Map[PureVar,PureVar]] = {
    if(r1.isEmpty){
      // s2 => true
      return List(r1Swap)
    }
    val c1 = r1.head
    val possibleSwaps = if (r1Swap.contains(c1)) {
        if (!r2.contains(r1Swap(c1)))
          return Nil
        else
          Set(r1Swap(c1))
    } else {
        r2.filter{c2 => canSwap(c1,c2,ts1,ts2)}
    }
    if(possibleSwaps.isEmpty)
      return Nil

    possibleSwaps.toList.flatMap{c2 =>
      canSubsumeUnifyFreshRef(r1.tail, r2 - c2, ts1, ts2, r1Swap + (c1 -> c2))}
  }

  private def canSubsumeUnifyPred(t1:AbstractTrace, t2:AbstractTrace, specSpace: SpecSpace,
                                  p1map:Map[PureVar, PureVar]):Set[Map[PureVar,PureVar]] = {
    val pred1 = EncodingTools.rhsToPred(t1.rightOfArrow, specSpace).map(EncodingTools.simplifyPred)
    val pred2: Set[LSPred] = EncodingTools.rhsToPred(t2.rightOfArrow, specSpace).map(EncodingTools.simplifyPred)
    if(pred2.isEmpty)
      return Set(p1map)
    ???
  }


  private def canSubsumeUnifyPure(ps1:Set[PureConstraint], ps2:Set[PureConstraint],
                                  r1Swap:Map[PureVar,PureVar]):Set[Map[PureVar,PureVar]] = {
    if(ps1.isEmpty)
      return Set(r1Swap)
    ???
  }

  /**
   * check if s2 => s1
   * @return true if unification successful
   */
  def canSubsumeUnify(s1:State, s2:State, specSpace:SpecSpace): Boolean = {
    val t1: Map[PureVar, TypeSet] = s1.sf.typeConstraints
    val t2 = s2.sf.typeConstraints
    val l1 = levelLocalPv(s1)
    val l2 = levelLocalPv(s2)
    val mapL = canSubsumeUnifyLocals(l1, l2, t1,t2)
    if(mapL.isEmpty)
      return false
    val h1: Map[HeapPtEdge, PureExpr] = s1.sf.heapConstraints
    val h2: Map[HeapPtEdge, PureExpr] = s2.sf.heapConstraints
    val mapsH: List[Map[PureVar, PureVar]] = canSubsumeUnifyHeap(h1,h2,t1,t2, mapL.get)

    val mapsR: Set[Map[PureVar, PureVar]] = mapsH.flatMap { mapH =>
      // Sets of pure vars that must be created in the future
      def freshRefSet(state: State): Set[PureVar] = {
        val tr = state.traceAbstraction
        tr.rightOfArrow.flatMap {
          case FreshRef(v) => Some(tr.modelVars(v).asInstanceOf[PureVar])
          case _ => None
        }.toSet
      }

      // Match up freshRefs.  s2 should have all freshRefs that s1 has
      val s1FreshRef = freshRefSet(s1)
      val s2FreshRef = freshRefSet(s2)
      // s2 should have been refuted before now if a heap cell contains a value that must be created in the future
      canSubsumeUnifyFreshRef(s1FreshRef, s2FreshRef, t1,t2, mapH)
    }.toSet //.filter(mapR => canSubsumeUnifyPure(s1.pureFormula, s2.pureFormula, mapR))

    if(mapsR.isEmpty)
      return false

    val mapsP:Set[Map[PureVar,PureVar]] = mapsR.flatMap{mapR =>
      canSubsumeUnifyPure(s1.sf.pureFormula, s2.sf.pureFormula,mapR)
    }

    val mapsT:Set[Map[PureVar,PureVar]] = mapsP.flatMap{mapP =>
      canSubsumeUnifyPred(s1.sf.traceAbstraction,s2.sf.traceAbstraction, specSpace,mapP)
    }

    mapsT.nonEmpty

  }


  protected def fastMaySubsume(s1:State, s2:State, specSpace: SpecSpace):Boolean = {
    if(s1.sf.callStack.nonEmpty && s2.sf.callStack.nonEmpty && s1.currentCallback != s2.currentCallback)
      return false
    if (s1.callStack.size > s2.callStack.size)
      return false

    val stackLocsMatch = (s1.callStack zip s2.callStack).forall {
      case (fr1, fr2) => fr1.exitLoc == fr2.exitLoc
    }
    if (!stackLocsMatch)
      return false

    // s2 must have equal or more CLInit invocations as s1
    def clInitSet(s:State):Set[CLInit] = {
      s.traceAbstraction.rightOfArrow.flatMap{
        case v:CLInit => Some(v)
        case _ => None
      }.toSet
    }
    val s1CLinit = clInitSet(s1)
    val s2CLinit = clInitSet(s2)
    if(s1CLinit.exists(s1i => !s2CLinit.contains(s1i)))
      return false

    // s2 must contain all locals that s1 contains
    val s2locals: Set[(String, Int)] = levelLocalPv(s2).toSet.map{x:((String,Int), PureExpr) => x._1}
    val s1locals: Set[(String, Int)] = levelLocalPv(s1).toSet.map{x:((String,Int), PureExpr) => x._1}
    if(!s1locals.forall(l => s2locals.contains(l))){
      return false
    }

    // s2 must contian all heap cells that s2 contains

    val s2heapCells: Map[HeapPtEdge, Map[HeapPtEdge, PureExpr]] = s2.heapConstraints.groupBy(repHeapCells)
    val s1heapCells = s1.heapConstraints.groupBy(repHeapCells)

    // For each materialized heap cell in s1, s2 must have a matching heap cell or subsumption not possible
    val s2HasMoreOfEach = s1heapCells.forall{s1Cell =>
      s2heapCells.get(s1Cell._1) match {
        case Some(s2Cells) =>
          s1Cell._2.size <= s2Cells.size
        case None => true
      }
    }
    if(!s2HasMoreOfEach){
      return false
    }

    val mustIs = EncodingTools.mustISet(s1,specSpace)
    val mayIs = EncodingTools.mayISet(s2, specSpace)
    if (mustIs.exists(v => !mayIs.contains(v))) {
      return false
    }

    true
  }

  def canSubsumeSet(s1:Set[State], s2: State, specSpace:SpecSpace,timeout:Option[Int] = None):Boolean = {
    ??? //TODO: this is broken in several unit tests, don't use until fixed
    val startTime = System.nanoTime()

    val s1Filtered = s1.filter(other => fastMaySubsume(other,s2, specSpace))

    // Check if stack sizes or locations are different
    if(s1Filtered.isEmpty){
      return false
    }

    val s2Simp = simplify(s2, specSpace)
    if(s2Simp.isEmpty) {
      return true
    }

    assert(s1.forall(s => s.isSimplified), "Subsuming states should be simplified")
    assert(s2.isSimplified, "State being subsumed should be simplified")

    //TODO: two state subsumption tries to reduce pt regions, may want to do that here as well?

    implicit val zCtx: C = getSolverCtx()

    val res = try {
      zCtx.acquire()
      val messageTranslator: MessageTranslator = MessageTranslator(s1 + s2, List(specSpace))
      s1Filtered.foreach{state =>
        val stateEncode = toASTState(state, messageTranslator, None, specSpace, negate=true)
        mkAssert(stateEncode)
      }
      val s2Encode = toASTState(s2, messageTranslator,None, specSpace, negate=false)
      mkAssert(s2Encode)
      val foundCounter =
        checkSAT(messageTranslator, None, true)
      !foundCounter
    }catch{
      case e:IllegalArgumentException if e.getLocalizedMessage.contains("timeout") =>
        // Note: this didn't seem to help things so currently disabled
        // sound to say state is not subsumed if we don't know
        // false

        println("subsumption timeout:")
        println(s"timeout: ${timeout}")
        println(s"${s1.size} states in s1.")
        println(s"  s2: ${s2}")
        println(s"  s2 ɸ_lhs: " +
          s"${EncodingTools.rhsToPred(s2.traceAbstraction.rightOfArrow,specSpace)
            .map(pred => pred.toString)
            .mkString("  &&  ")}")
        // uncomment to dump serialized timeout states
        // val s1f = File("s1_timeout.json")
        // val s2f = File("s2_timeout.json")
        //        val s1str = write(s1)
        //        val s2str = write(s2)
        //        println(s1str)
        //        println(s2str)
        // s1f.write(write(s1))
        // s2f.write(write(s2))
        // throw e
      iDefaultOnSubsumptionTimeout
    } finally {
      zCtx.release()
    }

    if(shouldLogTimes)
      getLogger.warn(s"subsumption result:${res} time(µs): ${(System.nanoTime() - startTime)/1000.0}")

    res
  }

  /**
   *
   * @param spec1 subsuming specification
   * @param spec2 subsumed specification
   * @return
   */
  def canSubsume(spec1:SpecSpace, spec2:SpecSpace):Boolean = {
    //TODO:====== test me
    def predAndFree(s:LSSpec):LSPred = Exists(s.target.lsVar.toList, s.pred)

    val preds1 = spec1.getSpecs.map(predAndFree).reduce(And)
    val preds2 = spec2.getSpecs.map(predAndFree).reduce(And)
    canSubsume(preds1,preds2)
  }

  def canSubsume(pred1:LSPred, pred2:LSPred):Boolean = {
    implicit val zCtx: C = getSolverCtx()
    try {
      zCtx.acquire()
//      if(pred1.toString.contains("NULL") || pred2.toString.contains("NULL")){
//        //TODO: need const distinct assertion here
//        ???
//      }
      val msg = MessageTranslator(List(pred1, pred2)).copy(pureValSet = pred1.lsVal ++ pred2.lsVal +
        IntVal(0) + IntVal(1) + NullVal)

      val p1E = pred1.lsVar
      val p2E = pred2.lsVar
      val pvals = msg.constMap.asInstanceOf[Map[PureExpr,T]]
      val enc1 = encodePred(Exists(p1E.toList,pred1), msg, pvals, Map.empty, Map.empty)
      val enc2 = encodePred(Exists(p2E.toList,pred2), msg, pvals, Map.empty, Map.empty)

      mkAssert(mkAnd(mkNot(enc1), enc2))
      val isSat = checkSAT(msg, None, true)

      !isSat
    } finally {
      zCtx.release()
    }
  }

  /**
   *
   *
   * @param s1 subsuming state
   * @param s2 contained state
   *           checks s2 => s1
   * @return
   */
  def canSubsume(s1: State, s2: State, specSpace: SpecSpace, maxLen: Option[Int] = None,
                 timeout:Option[Int] = None,method:SubsumptionMethod = SubsZ3): Boolean = {
//     val method = "Unify"//TODO: benchmark and see if this is actually faster: Idea run both and log times then hist
//     val method = "Debug"

    // val method = "FailOver"
    val startTime = System.nanoTime()
    // Some states can be quickly shown not to subsume before z3 call
    if(!fastMaySubsume(s1,s2,specSpace)){
      return false
    }

    //// Compute the set of required positive "I"s.  Cannot subsume if not subset
    //val s1Pred = StateSolver.rhsToPred(s1.sf.traceAbstraction.rightOfArrow, specSpace)
    //val s1MustI = s1Pred.flatMap(mustISet)
    //val s2Pred = StateSolver.rhsToPred(s2.sf.traceAbstraction.rightOfArrow, specSpace)
    //val s2MustI = s2Pred.flatMap(mustISet)
    ////TODO: is there something we could do to quickly eliminate tracepred subsumption without calling z3?


    // TODO: test if requiring subsuming state is suffix of subsumee improves speed
    // TODO: this should be done by StateSet rather than here for better performance
    // Note: sound but possibly not precise
    // if(!suffixSame(s1.sf.traceAbstraction.rightOfArrow, s2.sf.traceAbstraction.rightOfArrow))
    //   return false
    val s1Simp = simplify(s1, specSpace)
    val s2Simp = simplify(s2, specSpace)
    if(s2Simp.isEmpty)
      return true


    // note: unification pure formula subs is busted
//    if(s1Simp.get.traceAbstraction == s2Simp.get.traceAbstraction){
//      val csu = canSubsumeUnify(s1,s2, specSpace)
//      if(true){
//        // dbg code
//        val zsu = canSubsumeZ3(s1Simp.get,s2Simp.get,specSpace, maxLen, timeout)
//        assert(zsu == csu)
//      }
//      return csu
//    }

    val res = if(method == SubsZ3)
      canSubsumeZ3(s1Simp.get,s2Simp.get,specSpace, maxLen, timeout)
    else if(method == SubsUnify)
      canSubsumeUnify(s1Simp.get,s2Simp.get,specSpace)
    else if(method == SubsFailOver){
      try{canSubsumeUnify(s1Simp.get, s2Simp.get, specSpace)} catch{
        case _:IllegalStateException =>
          canSubsumeZ3(s1Simp.get, s2Simp.get, specSpace, maxLen, timeout)
      }
    } else if(method == SubsDebug) {
      val z3res = canSubsumeZ3(s1Simp.get, s2Simp.get, specSpace, maxLen, timeout)
      val unifyRes = canSubsumeUnify(s1Simp.get,s2Simp.get,specSpace)
      if(z3res != unifyRes) {
        val s1Ser = write(s1)
        val s2Ser = write(s2)
        val ctime = System.currentTimeMillis()
        val f1 = File(s"s1_diff_${ctime}.json")
        f1.write(s1Ser)
        val f2 = File(s"s2_diff_${ctime}.json")
        val s1Deser = read[State](s1Ser)
        val s2Deser = read[State](s2Ser)
        println(s1Deser)
        println(s2Deser)
        val z3res2 = canSubsumeZ3(s1Simp.get, s2Simp.get, specSpace,maxLen, timeout)
        val unifres2 = canSubsumeUnify(s1Simp.get, s2Simp.get, specSpace)
        //throw new IllegalStateException("different results")
      }
      z3res
    } else {
      println("""Expected method: "Unify" or "Z3" """)
      throw new IllegalArgumentException("""Expected method: "Unify" or "Z3" """)
    }

    if(shouldLogTimes)
      getLogger.warn(s"subsumption result:${res} time(µs): ${(System.nanoTime() - startTime)/1000.0}")
    res
  }
  // s1 subsuming state
  // s2 state being subsumed
  // TODO: May want to handle alpha renaming, but see if this works first
  private def suffixSame(s1Suffix: List[LSSingle], s2Suffix:List[LSSingle]):Boolean = (s1Suffix, s2Suffix) match{
    case (OAbsMsg(mt1,sig1,v)::t1, OAbsMsg(mt2,sig2,_)::t2) if mt1 != mt2 || sig1 != sig2 => suffixSame(AbsMsg(mt1,sig1,v)::t1, t2)
    case (OAbsMsg(mt1,sig1,_)::t1, OAbsMsg(mt2,sig2,_)::t2) if mt1 == mt2 && sig1 == sig2 => suffixSame(t1,t2)
    case (FreshRef(_)::t1, s2Suffix) => suffixSame(t1,s2Suffix)
    case (CLInit(_)::t1, s2Suffix) => suffixSame(t1,s2Suffix)
    case (s1Suffix, FreshRef(_)::t2) => suffixSame(s1Suffix,t2)
    case (s1Suffix, CLInit(_)::t2) => suffixSame(s1Suffix,t2)
    case (Nil,_) => true
    case (_::_, Nil) => false
  }
  private def suffix(state:State):List[String] = {
    state.sf.traceAbstraction.rightOfArrow.map {
      case c@CLInit(_) => c.toString
      case FreshRef(_) => "FreshRef"
      case OAbsMsg(mt, signatures, _) => s"I(${mt}, ${signatures.identifier})"
    }
  }


  def allTypes(state:State)(implicit zctx:C):Set[Int] = {
    val pvMap = state.typeConstraints
    val usedTypes = pvMap.flatMap { case (_, tc) => tc.getValues.getOrElse(Set()) }.toSet
    mkTypeConstraints(usedTypes)
    usedTypes
  }

  //TODO: this method could probably be more efficient
  /**
   * Remove points to regions that are redundant with respect to z3 subsumption check
   * This is a hack to deal with the thousands of points to regions that are produced by spark.
   * e.g. a state with pt regions such as:
   *   p-1 : 100,101,102
   *   p-2 : 50, 51, 52
   *   p-3 : 102
   *  would become:
   *   p-1 : 100,102
   *   p-2 : 50
   *   p-3 : 102
   * @param s1 subsuming state
   * @param s2 state to be subsumed
   * @return (s1,s2) where points to sets contain 1 representative element but no more
   */
  def reducePtRegions(s1:State, s2:State): (State,State) = {
    def tc(id:Int,s:State) = {
      s.typeConstraints.map{
        case (k,v) => (id,k,v)
      }
    }
    val spt = tc(1,s1) ++ tc(2,s2)

    //Get set of all regions
    val allSet = mutable.BitSet()
    spt.foreach{
      case (_,_, PrimTypeSet(_)) =>
      case (_,_, EmptyTypeSet) =>
      case (_,_, TopTypeSet) =>
      case (_, _, set) => allSet.addAll(set.getValues.getOrElse(mutable.BitSet())) // addAll uses a |= b under the hood
    }
    allSet.toImmutable

    // Iterate over each pt region and collect sets of regions including a pt value
    val setSet = allSet.foldLeft(Set[List[(Int,PureVar, TypeSet)]]()){ case (set,pt) =>
      val typeSetsContainingValue: List[(Int, PureVar, TypeSet)] = spt.filter {
        case (_, _, set) => set.contains(pt)
      }.toList
      set + typeSetsContainingValue
    }.toList.zipWithIndex // create artificial value for each set of sets and add to each associated set
    //TODO: may be better to have a representative pt element here instead of index

    // construct modified s1 and s2

    val outS1 = s1.typeConstraints.flatMap{
      case (k,_:BitTypeSet) => Some((k,mutable.BitSet()))
      case (k,ts) => None
    }
    val outS2 = s2.typeConstraints.flatMap{
      case (k,_:BitTypeSet) => Some((k,mutable.BitSet()))
      case (k,ts) => None
    }
    setSet.foreach{
      case (updList, i) =>
        updList.foreach{
          case (oldSt, pv, _) =>
            val updSt = if(oldSt == 1) outS1 else if(oldSt == 2) outS2 else throw new IllegalStateException("nostate")
            if(updSt.contains(pv)) {
              updSt(pv) += i
            }
        }
    }
    def constructSt(s:State, map: Map[PureVar, mutable.BitSet]):State = {
      map.foldLeft(s){
        case (st, (pv,bts)) => st.addTypeConstraint(pv,BitTypeSet(bts))
      }
    }
    val res = (constructSt(s1, outS1), constructSt(s2,outS2))
    res
  }

  /**
   * use the z3 encoding to test subsumption
   * @param s1i subsuming state
   * @param s2i state testing if it can be subsumed
   * @param specSpace specifications under which subsumption may occur
   * @param maxLen set to Some([num]) for dbg mode, witness will be limited to [num] length
   * @param timeout z3 timeout in milliseconds
   * @param rngTry number of attempts with different prng seeds
   * @return true if s1i can subsume s2i otherwise false
   */
  def canSubsumeZ3(s1i:State, s2i:State,specSpace:SpecSpace, maxLen:Option[Int], timeout:Option[Int],
                   rngTry:Int = 0):Boolean = {
    val (s1,s2) = reducePtRegions(s1i,s2i) //TODO: does reducing pts regions help?
//    val (s1,s2) = (s1i,s2i)
    implicit var zCtx = getSolverCtx()
    try {
      val existingSolver = getSolverCtx()
      zCtx = if(rngTry == 0) {
        existingSolver.acquire()
        existingSolver
      }else if(rngTry > 0){
        // on retry, seed RNG with try number for determinism
        val newTimeout = 520000
        val newTimeoutSolver = getSolverCtx(Some(newTimeout))
        val rngSeed = rngTry
        println(s"try again with new random seed: ${rngSeed} and timeout ${newTimeout}")
        newTimeoutSolver.acquire(Some(rngSeed))
        newTimeoutSolver
      }else{
        throw new IllegalStateException("Timeout, exceeded rng seed attempts")
      }
      val messageTranslator: MessageTranslator = MessageTranslator(List(s1, s2), List(specSpace))

      val s1Enc = toASTState(s1, messageTranslator, maxLen,
        specSpace = specSpace, negate=false, debug = maxLen.isDefined)
      mkAssert(mkNot(s1Enc))
      val s2Enc = toASTState(s2, messageTranslator, maxLen,
        specSpace = specSpace, negate=false, debug = maxLen.isDefined)
      mkAssert(s2Enc)
      val foundCounter =
        checkSAT(messageTranslator, None, true)

      if (foundCounter && maxLen.isDefined) {
        printDbgModel(messageTranslator, Set(s1.traceAbstraction,s2.traceAbstraction))
      }
      !foundCounter
    }catch{
      case e:IllegalArgumentException =>
        // Note: this didn't seem to help things so currently disabled
        // sound to say state is not subsumed if we don't know
        // false

        println("subsumption timeout, canceled or other unknown:")
        println(s"z3 message: ${e.getLocalizedMessage}")
        println(s"timeout: ${timeout}")
        println(s"  s1: ${s1}")
        println(s"  s1 ɸ_lhs: " +
          s"${EncodingTools.rhsToPred(s1.traceAbstraction.rightOfArrow,specSpace)
            .map(pred => pred.toString)
            .mkString("  &&  ")}")
        println(s"  s2: ${s2}")
        println(s"  s2 ɸ_lhs: " +
          s"${EncodingTools.rhsToPred(s2.traceAbstraction.rightOfArrow,specSpace)
            .map(pred => pred.toString)
            .mkString("  &&  ")}")
        // uncomment to dump serialized timeout states
        // val s1f = File("s1_timeout.json")
        // val s2f = File("s2_timeout.json")
        val s1str = write(s1)
        val s2str = write(s2)
        println(s1str)
        println(s2str)
        // s1f.write(write(s1))
        // s2f.write(write(s2))
        // throw e
        if (STRICT_TEST)
          throw new IllegalStateException("Timeout")

        // try 3 times with different random seeds
        if(rngTry < 2){
          zCtx.release()
          canSubsumeZ3(s1i,s2i,specSpace,maxLen,timeout, rngTry+1)
        }else {
          println("Giving up and not subsuming.")
          iDefaultOnSubsumptionTimeout
        }
    } finally {
      zCtx.release()
    }
  }

  /**
   * name locals relative to their stack position for encoding
   * @param s state
   * @return map from local and level to pointed to purevar
   */
  def levelLocalPv(s:State):Map[(String,Int), PureVar] = {
    s.callStack.zipWithIndex.flatMap{
      case (CallStackFrame(_,_,locals), level) =>
        locals.collect{case (StackVar(name),pValue:PureVar) => ((name,level),pValue)}
    }.toMap
  }

  def witnessed(pred:LSPred, specSpace:SpecSpace):Option[WitnessExplanation] = {
    val startTime = System.nanoTime()
    val res:Option[WitnessExplanation] = None
    try {
      implicit val zCtx = getSolverCtx()
      val res = traceInAbstraction(pred, specSpace, Trace.empty)
      res
    }finally{
      //if(shouldLogTimes)
      //  getLogger.warn(s"witnessed result: ${res.isDefined} time(µs): ${(System.nanoTime() - startTime) / 1000.0}")
    }
    ??? //TODO:====
  }
  /**
   * Consider rearrangments of pure vars that could result in subsumption
   *
   * @param s1 subsuming state
   * @param s2 contained state
   * @return
   */
  def witnessed(state: State, specSpace: SpecSpace, debug:Boolean = false): Option[WitnessExplanation] = {

    val startTime = System.nanoTime()
    val res:Option[WitnessExplanation] = None
    try {
      implicit val zCtx = getSolverCtx()
      if (state.heapConstraints.nonEmpty)
        return None
      if (state.callStack.nonEmpty)
        return None
      val res = traceInAbstraction(state, specSpace, Trace.empty, debug)
      res
    }finally{
      if(shouldLogTimes)
        getLogger.warn(s"witnessed result: ${res.isDefined} time(µs): ${(System.nanoTime() - startTime) / 1000.0}")
    }
  }
  def traceInAbstraction(pred:LSPred, specSpace:SpecSpace, trace:Trace)(implicit zCtx:C):Option[WitnessExplanation] ={
    ???
    //TODO:trace in abstraction for pred only
    try {
      zCtx.acquire()
      val messageTranslator = MessageTranslator(???, List(specSpace))
      initializeZeroAxioms(messageTranslator)
      val pvMap: Map[PureVar, T] = encodeTraceContained(???, trace,
        messageTranslator = messageTranslator, specSpace = specSpace)
      val sat = checkSAT(messageTranslator, None, false)

      if (sat) {
          Some(explainWitness(messageTranslator, (pvMap ++ messageTranslator.getConstMap).toMap))
      } else {
        None
      }
    }finally{
      zCtx.release()
    }
  }
  def traceInAbstraction(state: State,specSpace: SpecSpace,
                         trace: Trace,
                         debug: Boolean = false)(implicit zCtx: C): Option[WitnessExplanation] = {
    val (stateClean, _) = reducePtRegions(state.inlineConstEq().getOrElse{
      return None
    }, State.topState)
    try {
      zCtx.acquire()
      val messageTranslator = MessageTranslator(List(stateClean), List(specSpace))
      initializeZeroAxioms(messageTranslator)
      val pvMap: Map[PureVar, T] = encodeTraceContained(stateClean, trace,
        messageTranslator = messageTranslator, specSpace = specSpace)
      val sat = checkSAT(messageTranslator, None, false)
      if (sat && debug) {
        println(s"model:\n ${zCtx.asInstanceOf[Z3SolverCtx].solver.toString}")
        printDbgModel(messageTranslator, Set(stateClean.traceAbstraction))
      }
      if (sat) {
        Some(explainWitness(messageTranslator,(pvMap ++ messageTranslator.getConstMap).toMap))
      } else {
        None
      }
    }finally{
      zCtx.release()
    }
  }

  def mkMsgAtIndex(num:Int)(implicit zctx: C):(T,T) = {
    (0 until num).foldLeft((mkZeroMsg, mkBoolVal(b = true))){case (acc,_) =>
      val (ivIsInc,iv) = mkAddOneMsg(mkTraceFn, acc._1)
      (iv,mkAnd(acc._2, ivIsInc))
    }
  }
  private def encodeTraceContained(state: State, trace: Trace, specSpace: SpecSpace,
                                   messageTranslator: MessageTranslator)(implicit zCtx: C): Map[PureVar, T] = {
//    val traceFn = mkTraceFn("")
    val usedTypes = allTypes(state)
    val (typesAreUnique, _) = mkTypeConstraints(usedTypes)
    mkAssert(typesAreUnique)

//    val traceLimit = trace.indices.foldLeft(mkZeroIndex){case (acc,_) => mkAddOneIndex(acc)}
    val (traceLimit, isInc) = mkMsgAtIndex(trace.size)
    mkAssert(isInc)
    mkForallTraceMsg(mkTraceFn, m => mkLTEMsg(m,traceLimit))

    // Maximum of 10 addresses in trace contained.  This method is typically used for empty traces with no addresses.
    // Only testing has non empty traces passed to this method
    val distinctAddr: Map[Int, T] = (0 until 10).map(v => (v, mkAddrConst(v))).toMap
    val assertDistinct = mkDistinctT(distinctAddr.keySet.map(distinctAddr(_)))
    mkAssert(assertDistinct)
    val (encodedState,pvMap) = toASTStateWithPv(state, messageTranslator, None,
      specSpace = specSpace, negate=false,exposePv = true)
    val encodedTrace = encodeTrace(trace, messageTranslator, distinctAddr)

    mkAssert(encodedState)
    mkAssert(encodedTrace)

    pvMap
  }
  def encodeTrace(trace: Trace,
                  messageTranslator: MessageTranslator, argVals: Map[Int, T])(implicit zCtx: C): T = {
//    assert(trace.head == TInitial)
    val distinctMSG: List[(TraceElement,T)] = trace.t.zipWithIndex.map{
      case (message, i) => (message,  mkMsgConst(i,Some(message)))
    }

    // Each message must be in the trace function
    distinctMSG.foreach{
      case (_, msg) => mkAssert(mkTraceFnContains(mkTraceFn, msg))
    }

    val msgVars = distinctMSG.map{ case (_, t) => t}
    val (msgOrdAndArg,_) = distinctMSG.zipWithIndex.foldLeft((mkBoolVal(true),mkZeroMsg)){
      case ((acc,last),((msg:TMessage,ast),ind)) =>
        val (c0,msgA) = mkAddOneMsg(mkTraceFn(),last)
        val c1 = msgModelsTraceElement(msgA, msg, messageTranslator, argVals)
        (mkAnd(List(acc,c0,c1, mkEq(ast,msgA))), msgA)
      case ((_,last), ((_,v),0)) =>
        (mkEq(last,v),last)
      case v =>
        ???
    }
    val distinctMsg = mkDistinctT(msgVars)
    val namedMsg = mkForallTraceMsg(mkTraceFn(), m => mkOr(msgVars.map(msgVar =>
      mkEq(m,msgVar))))

    val out = mkAnd(List(distinctMsg, namedMsg, msgOrdAndArg))
    out
  }


}