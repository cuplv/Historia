package edu.colorado.plv.bounder.synthesis
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, ResultSummary, Witnessed}
import edu.colorado.plv.bounder.ir.{ApproxDir, CNode, ConcGraph, EmptyTypeSet, Exact, OverApprox, TMessage, TopTypeSet, TypeSet, UnderApprox}
import edu.colorado.plv.bounder.lifestate.LSPredAnyOrder.SpecSpaceAnyOrder
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, AnyAbsMsg, Exists, Forall, LSAnyPred, LSAtom, LSBinOp, LSConstraint, LSFalse, LSImplies, LSPred, LSSpec, LSTrue, LSUnOp, NS, Not, OAbsMsg, Or}
import edu.colorado.plv.bounder.lifestate.{LSPredAnyOrder, LifeState, SpecAssignment, SpecSpace}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, EncodingTools, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.{ApproxMode, ControlFlowResolver, DefaultAppCodeResolver, ExecutorConfig, LimitMaterializationApproxMode, PreciseApproxMode, QueryFinished}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, AllReceiversNonNull, BoolVal, CallinReturnNonNull, DirectInitialQuery, DisallowedCallin, IPathNode, InitialQuery, IntVal, MemoryOutputMode, NPureVar, NamedPureVar, NullVal, OutputMode, PrettyPrinting, PureExpr, PureVal, PureVar, Reachable, ReceiverNonNull, State, TopVal}
import edu.colorado.plv.bounder.synthesis.EnumModelGenerator.{NoStep, StepResult, StepSuccessM, StepSuccessP, approxSpec, isTerminal}

import scala.collection.concurrent.TrieMap
import scala.collection.{View, immutable, mutable}
import scala.collection.immutable.Queue
import scala.collection.mutable.ListBuffer
import scala.collection.parallel.CollectionConverters.ImmutableIterableIsParallelizable

sealed trait LearnResult

// results of model generator
case class LearnSuccess(space: SpecSpace) extends LearnResult

case object LearnFailure extends LearnResult

object EnumModelGenerator{
  def approxPred(lsPred: LSPred, approxDir: ApproxDir): LSPred = {
    val replaceAnyWith = approxDir match {
      case OverApprox => LSTrue
      case UnderApprox => LSFalse
      case Exact =>
        ???
    }
    lsPred match {
      case NS(m, AnyAbsMsg) if approxDir == OverApprox => m
      case NS(m, AnyAbsMsg) if approxDir != OverApprox => LSFalse
      case LSAnyPred => replaceAnyWith
      case Or(l1, l2) => Or(approxPred(l1, approxDir), approxPred(l2, approxDir))
      case And(l1, l2) => And(approxPred(l1, approxDir), approxPred(l2, approxDir))
      case Forall(vars, p) => Forall(vars, approxPred(p, approxDir))
      case Exists(vars, p) => Exists(vars, approxPred(p, approxDir))
      case atom: LSAtom => atom
      case v:LSConstraint => v
      case v =>
        println(v)
        ???
    }
  }


  def approxSpec(lsSpec: LSSpec, approxDir: ApproxDir): LSSpec =
    lsSpec.copy(pred = EncodingTools.simplifyPred(approxPred(lsSpec.pred, approxDir)))

  def approxSpec(spec: SpecSpace, approxDir: ApproxDir): SpecSpace = {
    val specs = spec.getSpecs.map(approxSpec(_, approxDir))
    spec.copy(enableSpecs = specs)
  }
  def isTerminal(pred:LSPred):Boolean = pred match {
    case NS(_,AnyAbsMsg) => false
    case NS(AnyAbsMsg, _) => ???
    case LifeState.LSAnyPred => false
    case Or(l1, l2) => isTerminal(l1) && isTerminal(l2)
    case And(l1, l2) => isTerminal(l1) && isTerminal(l2)
    case LSTrue => true
    case LSFalse => true
    case _:LSConstraint => true
    case Forall(_, p) => isTerminal(p)
    case Exists(_, p) => isTerminal(p)
    case _:LSImplies =>
      throw new IllegalArgumentException("Shouldn't be using implies in synthesis")
    case _:NS => true
    case _:OAbsMsg => true
//    case AnyAbsMsg => false
    case Not(p) => isTerminal(p)
  }
  def isTerminal(lsSpec: LSSpec):Boolean = lsSpec match{
    case LSSpec(_,_,pred,_,_) => isTerminal(pred)
  }
  def isTerminal(spec:SpecSpace):Boolean =
    spec.getSpecs.forall(isTerminal)

  sealed trait StepResult
  case class StepSuccessP(preds:List[(LSPred, Set[PureVar])]) extends StepResult
  case class StepSuccessM(msg:List[(OAbsMsg ,Set[PureVar])]) extends StepResult
  case object NoStep extends StepResult


}
class EnumModelGenerator[M,C](target:InitialQuery,reachable:Set[InitialQuery], initialSpec:SpecSpace
                              ,cfg:ExecutorConfig[M,C], dbg:Boolean = false, nonConnected:Boolean = false,
                              reachPkgFilter:List[String] = ".*"::Nil, unreachPkgFilter:List[String] = ".*"::Nil)
  extends ModelGenerator(cfg.w.getClassHierarchyConstraints) {
  private val historiaOverApproxTimes = mutable.ArrayBuffer[Double]()
  private val historiaUnderApproxTimes = mutable.ArrayBuffer[Double]()
  private var lastRuntime:Double = -1
  private var synthesisTotalTime:Double = 0
  private var historiaOverApproxTotalTime:Double = 0
  private var historiaUnderApproxTotalTime:Double = 0
  private var msgGraphTime:Double = 0

  def addOverApproxTime(time:Double):Unit = synchronized {
    historiaOverApproxTimes.addOne(time)
  }

  def addUnderApproxTime(time: Double): Unit = synchronized {
    historiaUnderApproxTimes.addOne(time)

  }

  def clearStats(): Unit = {
    historiaUnderApproxTimes.clear()
    historiaOverApproxTimes.clear()
    lastRuntime = -1
    historiaOverApproxTotalTime = 0
    historiaUnderApproxTotalTime = 0
    synthesisTotalTime = 0
    msgGraphTime = 0
  }

  def getStats():Map[String,Double] = {
    Map(
      "historia under approx avg time(s)" -> (historiaUnderApproxTimes.sum/historiaUnderApproxTimes.size) / 1e9,
      "historia under approx call count (n)" -> historiaUnderApproxTimes.size,
      "historia under approx thread tot time(s)" -> historiaUnderApproxTimes.sum / 1e9,
      "historia over approx avg time(s)" -> (historiaOverApproxTimes.sum/historiaOverApproxTimes.size) / 1e9,
      "historia over approx thread tot time(s)" -> historiaOverApproxTimes.sum / 1e9,
      "historia over approx call count (n)" -> historiaOverApproxTimes.size,
      "historia over approx program tot time(s)" -> historiaOverApproxTotalTime / 1e9,
      "historia under approx program tot time(s)" -> historiaUnderApproxTotalTime / 1e9,
      "synthesis program tot time(s)" -> synthesisTotalTime / 1e9,
      "runtime(s)" -> lastRuntime / 1e9,
      "message graph time(s)" -> msgGraphTime / 1e9
    )
  }

  private val cha = cfg.w.getClassHierarchyConstraints
  private val controlFlowResolver = {
    val msgGraphStartTime = System.nanoTime()
    val out = new ControlFlowResolver[M,C](cfg.w, new DefaultAppCodeResolver(cfg.w), cha,
      Some(reachPkgFilter ++ unreachPkgFilter),cfg)
    msgGraphTime = System.nanoTime() - msgGraphStartTime
    out
  }
  private val ptsMsg = controlFlowResolver.ptsToMsgs(initialSpec.getMatcherSpace)

  private val approxResMemo = TrieMap[(InitialQuery, SpecSpace, ApproxDir, ApproxMode, List[String]), Set[IPathNode]]()
  //TODO: separate over/under of spec and analysis

  /**
   *
   * @param qry initial query in the application
   * @param spec specification of framework behavior
   * @param specApprox over or under approximate specification
   * @param analysisApprox over or under approximate app behavior
   * @param pkgFilter packages to include in analysis
   * @return
   */
  def mkApproxResForQry(qry:InitialQuery, spec:SpecSpace, specApprox: ApproxDir,
                        analysisApprox:ApproxMode, pkgFilter:List[String]):Set[IPathNode] = {
//    val approxMode = specApprox match {
//      case OverApprox => LimitMaterializationApproxMode()
//      case UnderApprox => PreciseApproxMode(canWeaken = false)
//      case Exact => ???
//    }
    val startTime = System.nanoTime()
    val approxOfSpec = approxSpec(spec, specApprox)
    val key = (qry,approxOfSpec, specApprox, analysisApprox, pkgFilter)
    if(!approxResMemo.contains(key)) {
      //TODO: do something smarter than recomputing full query each time, doing this for testing right now
      // note: this is just a matter of changing the labels on individual nodes in wit tree?
      val tConfig = cfg.copy(specSpace = approxOfSpec, approxMode = analysisApprox,
        component = Some(pkgFilter))
      val ex = tConfig.getAbstractInterpreter
      val res = ex.run(qry, MemoryOutputMode).flatMap(_.terminals)
      approxResMemo.addOne(key -> res)
      val totalTime = System.nanoTime() - startTime

      // log analysis time
      analysisApprox match {
        case LimitMaterializationApproxMode(_) =>
          addOverApproxTime(totalTime)
        case PreciseApproxMode(_) =>
          addUnderApproxTime(totalTime)
        case _ => ???
      }

      res
    }else {
      approxResMemo(key)
    }
  }

  private val exploredSpecs = mutable.HashSet[SpecSpace]()

  def isProgress(from:LSPred, to:LSPred):Boolean = {
    def combProg(l1:LSPred, l2:LSPred, l1p :LSPred, l2p:LSPred):Boolean =
      isProgress(l1,l1p) && isProgress(l2,l2p)
    (from,to) match {
      case (LSAnyPred, v) if(v != LSAnyPred) =>
        true
      case (Exists(_, p1), p2) => isProgress(p1,p2)
      case (p1, Exists(_,p2)) => isProgress(p1, p2)
      case (Forall(_, p1), p2) => isProgress(p1,p2)
      case (p1, Forall(_,p2)) => isProgress(p1, p2)
      case (v1:LSBinOp, v2:LSBinOp) if v1.getClass == v2.getClass => combProg(v1.l1,v1.l2,v2.l1,v2.l2)
      case (v1:LSUnOp, v2:LSUnOp) if v1.getClass == v2.getClass => isProgress(v1.p, v2.p)
      case (_,_) =>
        false
    }
  }



  val simpleTestSet = mutable.HashSet[String]()
  /**
   * Check if this spec has been explored and remember that it has been explored
   * @param spec
   * @return
   */
  private def hasExplored(spec:SpecSpace):Boolean = {
    val specString = spec.toString
    val otherStrExists = simpleTestSet.contains(specString)

    //val otherExists = exploredSpecs.exists{other =>
    //  try {
    //    lazy val overOther = approxSpec(other, OverApprox)
    //    lazy val overSpec = approxSpec(spec, OverApprox)
    //    lazy val subs1 = stateSolver.canSubsume(overOther, overSpec)
    //    lazy val subs2 = stateSolver.canSubsume(overSpec, overOther)
    //    lazy val prog = isProgress(spec, other)
    //    prog && subs1 && subs2
    //  }catch{
    //    case e:IllegalArgumentException if e.getMessage.contains("Unknown, no") =>
    //      // timeout //TODO: figure out why this is timing out at some point
    //      false
    //  }
    //}

    if(!otherStrExists) {
      exploredSpecs.add(spec)
      simpleTestSet.add(specString)
      false
    }else{
      true
    }
  } //TODO: === be smarter to avoid redundant search


  def mergeOne(predConstruct:LSPred => LSPred, sub:LSPred, scope:Map[PureVar,TypeSet],
               freshOpt:Set[PureVar], witnesses:Set[IPathNode]):StepResult = {
    step(sub, scope, freshOpt, witnesses) match{
      case StepSuccessP(preds) => StepSuccessP(preds.map{case (p,tq) => (predConstruct(p),tq)})
      case StepSuccessM(preds) => StepSuccessP(preds.map{case (p,tq) => (predConstruct(p),tq)})
      case NoStep => NoStep
    }
  }
//  def mergeTwo(predConstruct:(LSPred,LSPred) => LSPred, p1:LSPred, p2:LSPred, scope:Map[PureVar, TypeSet]):StepResult ={
//    //TODO: this function doesn't work, predConstruct does not step!!!!!
//    ???
//    type T = LSPred
//    val (pred1Construct, other):(T=>LSPred,T) = if(!isTerminal(p1))
//      ((p:T) => predConstruct(p1,p),p2)
//    else if(!isTerminal(p2)){
//      ((p:T) => predConstruct(p,p2),p1)
//    }else
//      return StepSuccessP((predConstruct(p1,p2),Set[PureVar]())::Nil)
//    mergeOne(pred1Construct, other, scope)
//  }

  def mkRel(scope:Map[PureVar,TypeSet], freshOpt:Set[PureVar]):Set[OAbsMsg] = {
    val scope2  = scope.map{case (k,v) => k.asInstanceOf[PureExpr]-> v}
    val scopeVals: Map[PureExpr,TypeSet] = scope2 + (TopVal -> TopTypeSet)
    ptsMsg.flatMap{ case (msgFromCg, argPts) =>
      // find all possible aliasing intersection between points to set from call graphs

      // TODO: positional options should consider each case where at least one alias exists then enumerate other positional options
      val zippedCgPtsArgs = msgFromCg.lsVars.zip(argPts).zipWithIndex
      val intersectNonEmpty: Seq[(PureExpr, Int)] = zippedCgPtsArgs.flatMap {
        case ((pv: PureVar, tsFromCg), ind) =>
          scopeVals.flatMap {
            case (varName, ts2) =>
              if(tsFromCg.intersectNonEmpty(ts2)){
                Some(varName, ind)
              }else
                None
          }
        case (v, _) => None
      }
      if(intersectNonEmpty.exists{
        case (_:PureVar, _) => true // exists to ignore Top value
        case _ => false
      }) { // case some pv aliases
        // apply aliasing to each possible aliased arg
        val outOpts = intersectNonEmpty.flatMap {
          case (TopVal, _) =>
            Set.empty // ignore aliasing of non-pv
          case (aliasedVar:PureVar, aliasedIndex) =>
            //TODO: this should do enumeration of all non alias
            val positionalOptions: Seq[List[PureExpr]] = msgFromCg.lsVars.zip(argPts).zipWithIndex.map {
              case ((pv: PureVar, _), ind) if aliasedIndex == ind =>
                List(aliasedVar)
              case ((pv: PureVar, ts), ind) if aliasedIndex != ind =>
                val out = scopeVals
                  .filter {
                  case (_, ts2) =>
                    ts.intersectNonEmpty(ts2)
                }
                (out.keys ++ freshOpt).toList
              case ((v, _), ind) if aliasedIndex != ind =>
                List(v)
              case ((_, _), ind) if aliasedIndex == ind =>
                List()
            }

            val combinations = BounderUtil.repeatingPerm(positionalOptions, msgFromCg.lsVars.size)
            // filter for things that don't have one part of scope
            val reasonableCombinations = combinations.filter { comb =>
              comb.exists {
                case pureVar: PureVar => scope.contains(pureVar)
                case _ => false
              }
            }

            // TODO: substitute and return abstract messages
            val out = reasonableCombinations.map { comb => msgFromCg.copy(lsVars = comb) }
            out
        }
        outOpts
      }else{ // case no single pv aliases
        Set.empty
      }
    }
  }

  def stepBinop(l1: LSPred, l2: LSPred, op:(LSPred,LSPred) => LSPred,
                scope:Map[PureVar, TypeSet], freshOpt:Set[PureVar], hasAnd:Boolean, witnesses:Set[IPathNode]): StepResult = {
    val l1_step = if (LSPredAnyOrder.depthToAny(l1) < LSPredAnyOrder.depthToAny(l2)) {
      step(l1, scope, freshOpt, witnesses, hasAnd)
    } else NoStep
    l1_step match {
      case NoStep =>
        step(l2, scope,freshOpt, witnesses, hasAnd) match {
          case StepSuccessP(preds) => StepSuccessP(preds.map(p => (op(l1, p._1), p._2 ++ scope.keySet)))
          case StepSuccessM(msg) => ???
          case NoStep => NoStep
        }
      case StepSuccessP(preds) => StepSuccessP(preds.map(p => (op(p._1, l2), p._2 ++ scope.keySet)))
    }
  }

  def scopedMsgExistsInWit(witness:IPathNode, scope:Map[PureVar,TypeSet], absMsg: AbsMsg):Boolean = {
    assert(witness.qry.isWitnessed || witness.qry.isLive, "witness must be live/timeout or include initial state")
    val alarmState = witness.qry.state
    val out = alarmState.sf.traceAbstraction.rightOfArrow.exists{msgFromWit =>
      if(msgFromWit.identitySignature != absMsg.identitySignature){
        false
      }else {
        val zippedArgs = msgFromWit.lsVars.zip(absMsg.lsVars)
        val res = zippedArgs.find { a => !(a match { // all args must match scoped vars
          case (v1: PureVar, v2: PureVar) =>
            val ruleTs = scope.getOrElse(v2, TopTypeSet)
            val absStateTs = alarmState.typeConstraints.getOrElse(v1, TopTypeSet)
            ruleTs.intersectNonEmpty(absStateTs)
          case (TopVal, _) => true
          case (_, TopVal) => true
          case (IntVal(0), BoolVal(false)) => true
          case (BoolVal(false), IntVal(0)) => true
          case (IntVal(v), BoolVal(true)) if v != 0 => true
          case (BoolVal(true), IntVal(v)) if v != 0 => true
          case (v1: PureVal, v2: PureVal) => v1 == v2
          case (_: IntVal, _: BoolVal) =>
            false
          case (_: BoolVal, _: IntVal) =>
            false
          case (v1: PureVar, NullVal) =>
            alarmState.mayBeNull(v1)
          case (NullVal, _) => true
          case (v1, v2) =>
            println(v1) // const vals, should they match?
            println(v2) // const vals, should they match?
            ???
        })}
        res.isEmpty
      }
    }
    out
  }

  /**
   * Expands LSAnyPred into candidate formula.
   * Note that hasAnd enforces Conjunctive Normal Form and is set to true if and occurs higher in the AST.
   *
   * @param pred
   * @param scope
   * @param hasAnd
   * @return stepped specification with new logic variables to be quantified
   */
  def step(pred:LSPred, scope:Map[PureVar,TypeSet], freshOpt:Set[PureVar], witnesses:Set[IPathNode],
           hasAnd:Boolean = false):StepResult = pred match{
    case LifeState.LSAnyPred =>{
      val relMsg: immutable.Iterable[OAbsMsg] = mkRel(scope, freshOpt)//scope.flatMap{case(pv,ts) => mkRel(pv,ts, scope.keySet)}

//      val relNS = relMsg.flatMap{m =>
//        absMsgToNs(m,scope).map(ns =>
//          (ns:LSPred, ns.lsVar.filter(v => !scope.contains(v))))
//      }.filter{
//        case (NS(m1,m2), _) =>
//          val m1Var = m1.lsVar
//          m1Var.exists(v => scope.contains(v)) &&
//            m2.lsVar.forall(v => m1Var.contains(v))
//      }
      val relNS = relMsg.map{m =>
        (NS(m, AnyAbsMsg), m.lsVar)
      }


      val relMsgToAdd = relMsg.map{m => (m.asInstanceOf[LSPred], m.lsVar.filter(!scope.contains(_)))}

      val mutList = new ListBuffer[(LSPred, Set[PureVar])]()
      mutList.addAll(relNS)
      mutList.addAll(relMsgToAdd)
//      val TODORM_oldNotList = relMsg.flatMap { m =>  //TODO: remove at some point
//          Some(Not(m.copyMsg(m.lsVars.map {
//            case v: PureVar if scope.contains(v) => v
//            case _ => TopVal
//          })), Set[PureVar]())
//      }

      mutList.addAll(relMsg.flatMap{ m =>
        if(witnesses.exists{w => scopedMsgExistsInWit(w, scope, m)}) { //no reason to have not if no instance in hist
          Some(Not(m.copyMsg(m.lsVars.map {
            case v:PureVal =>
              v
            case v: PureVar if scope.contains(v) => v
            case _ => TopVal
          })), Set[PureVar]())
        }else
          None
      })

      val binOps = if(hasAnd) List(Or) else List(Or,And)
      binOps.foreach { op =>
        mutList.addOne((op(LSAnyPred, LSAnyPred), Set[PureVar]()))
      }
      StepSuccessP(mutList.toList)
    }
    case NS(m, AnyAbsMsg) =>
      val relMsg: immutable.Iterable[OAbsMsg] = mkRel(scope, freshOpt)
      val stepNS = relMsg.map(m2 => NS(m,m2))
      val out = stepNS.filter {
          case NS(m1,m2) =>
            val m1Var = m1.lsVar
            witnesses.exists{w => scopedMsgExistsInWit(w, scope, m2)} && //no reason to have not if no instance in hist
              m1Var.exists(v => scope.contains(v)) &&
              m2.lsVar.forall(v => m1Var.contains(v))
      }.map{
        case ns@NS(_,m2) => (ns, scope.keySet ++ m2.lsVar)
      }
      StepSuccessP(out.toList)
    case Or(l1, l2) =>
      stepBinop(l1,l2,Or, scope,freshOpt, hasAnd, witnesses)
    case And(l1, l2) =>
      stepBinop(l1,l2,And, scope,freshOpt, hasAnd = true, witnesses)
    case Forall(x, s) => mergeOne(v => Forall(x,v), s, scope ++ x.map(_ -> TopTypeSet), freshOpt, witnesses)
    case Exists(x, p) => mergeOne(Exists(x,_), p, scope ++ x.map(_ -> TopTypeSet), freshOpt, witnesses)
    case _:NS => NoStep
//    case NS(m1, m2) => mergeTwo((a:AbsMsg,b:AbsMsg) => NS(b,a),m2,m1,scope)
    case _:OAbsMsg => NoStep
    case Not(_:OAbsMsg) => NoStep
    case Not(p) => throw new IllegalArgumentException(s"bad step: ${Not(p)}")
    case _:LSImplies =>
      throw new IllegalArgumentException("Shouldn't be using implies in synthesis")
    case _ => NoStep
  }


  def pathExists(boundVars:Set[PureVar], msg:OAbsMsg, allMsg:Set[OAbsMsg]):Boolean = {
    // Note: this relies on formula being in prenix normal form, it will break on things like (∃x.P(x)) /\ (∃x.Q(x))
    //TODO: optimize by making this one pass if it slows things down
    // models are small enough it probably doesn't matter
    val expandedVars = mutable.HashSet[PureVar]()
    expandedVars.addAll(boundVars)
    var size:Int = -1

    while(size != expandedVars.size) {
      size = expandedVars.size
      if(msg.lsVar.exists(boundVars.contains))
        return true
      allMsg.foreach{otherMsg =>
        val otherMsgVars = otherMsg.lsVar
        if(otherMsgVars.exists(boundVars.contains)){
          expandedVars.addAll(otherMsgVars)
        }
      }
    }
    false
  }
  def connectedSpec(rule:LSSpec):Boolean = rule match {
    case LSSpec(univQuant, existQuant, pred, target, _) =>
      val boundVars = univQuant.toSet ++ existQuant
      val allMsg = pred.allMsg
      //      connectedPred(pred, boundVars)
      allMsg.forall{msg => pathExists(boundVars, msg, allMsg) }
  }


  /**
   * Ignore candidate rules that existentially quantify a variable that can only be in a negative position.
   * @param rule
   * @return
   */
  def hasNegOnly(rule:LSSpec):Boolean = { //TODO: finish this
    def getNegOnly(pred:LSPred):Set[PureVar] = pred match {
      case LifeState.LSAnyPred => ???
      case bexp: LifeState.LSBexp => ???
      case op: LSBinOp => ???
      case op: LSUnOp => ???
      case Forall(vars, p) => ???
      case Exists(vars, p) => ???
      case LSImplies(l1, l2) => ???
      case LifeState.HNOE(v, m, extV) => ???
      case atom: LSAtom => ???
    }
    rule match{
      case s@LSSpec(un,ex,pred,tgt,_) =>
        ???
    }
  }

  /**
   *
   * @param rule to fill a hole
   * @param scope all variables that have been instantiated in the verification task and associated points to
   * @return next spec, whether spec was stepped
   */
  def stepSpec(rule:LSSpec, scope:Map[PureVar,TypeSet], witnesses:Set[IPathNode]):(List[LSSpec],Boolean) = rule match{
    case s@LSSpec(un,ex,pred,tgt,_) =>
      val allFv: Set[PureVar] = un.toSet ++ ex.toSet ++ pred.lsVar ++ tgt.lsVar
      var fv = 0
      while(allFv.contains(NamedPureVar(s"synth_${fv}"))){
        fv = fv + 1
      }
      val freshOpt:Set[PureVar] = Set(NamedPureVar(s"synth_${fv}"))
      val stepped: (List[LSSpec], Boolean) = step(pred, scope, freshOpt, witnesses) match {
        case StepSuccessP(preds) =>
          val simplifiedPreds = preds.map { case (p, quant) =>
            EncodingTools.simplifyPred( p)}
          val outS = simplifiedPreds.map{pred =>
            val freeVars: Set[PureVar] = pred.lsVar
            val newQuant = freeVars.removedAll(un).removedAll(ex)
            s.copy(pred = pred, existQuant = ex.appendedAll(newQuant).distinct)
          }
          val filteredConnected = outS.filter{p => connectedSpec(p) || nonConnected}
          (filteredConnected,true)
        case NoStep => (List(s),false)
      }
      //TODO: this isn't enough for the call call problem, seems to be a problem with reachable
      (stepped._1.filter{
//        v => v.pred != v.target
        case LSSpec(_,_,pred:OAbsMsg,tgt:OAbsMsg,_) => pred.identitySignature != tgt.identitySignature
        case _ => true
      }, stepped._2) // Note that `x.foo() -[]-> O x.foo()` spec can never match finite history
  }

  /**
   *
   * @param rule
   * @param state
   * @return
   */
  def mkScope(rule:LSSpec, witnesses:Set[IPathNode]):Map[PureVar,TypeSet] = {
    val allAbsMsg:Set[OAbsMsg] = SpecSpace.allI(rule.pred) + rule.target
    val allVars = allAbsMsg.flatMap{m => m.lsVar}

    witnesses.foldLeft(allVars.map{v => v->EmptyTypeSet}.toMap: Map[PureVar,TypeSet]){
      case (acc,wit) =>
        val cState = wit.state
        cState.sf.traceAbstraction.rightOfArrow.foldLeft(acc){
          case (acc, msg) =>
            val individualMaps:Set[Map[PureVar,TypeSet]] = allAbsMsg.map{ absMsgFromRule =>
              if(absMsgFromRule.identitySignature == msg.identitySignature){
                assert(absMsgFromRule.lsVars.size == msg.lsVars.size,
                  s"msg arity must be the same.\n rule msg: $absMsgFromRule \n state msg: $msg")
                (absMsgFromRule.lsVars zip msg.lsVars).flatMap{
                  case (ruleVar:PureVar, stateVar:PureVar) =>
                    Some(ruleVar -> cState.sf.typeConstraints.getOrElse(stateVar, TopTypeSet))
                  case _ =>
                    None
                }
              }.toMap else acc
            }
            individualMaps.reduce{ // merge all individual maps unioning ts
              (map1, map2) =>
                  (map1.keySet ++ map2.keySet)
                    .map { key => key -> map1.getOrElse(key, EmptyTypeSet).union(map2.getOrElse(key, EmptyTypeSet)) }.toMap
              }
        }
    }
  }



  /**
   *
   * @param spec spec to expand an AST hole
   * @return next spec, whether spec was stepped
   */
  def stepSpecSpace(specSpace:SpecSpace, witnesses:Set[IPathNode]):(Set[SpecSpace],Boolean) = { //TODO: figure out why I did this boolean thing and not just empty set
    val specToStep = specSpace.getSpecs.filter(s => LSPredAnyOrder.hasAny(s.pred))
      .toList.sorted(LSPredAnyOrder.SpecStepOrder).headOption
    if(specToStep.isEmpty)
      return (Set(specSpace),false)
    val (next:List[LSSpec],changed) =
      stepSpec(specToStep.get,mkScope(specToStep.get, witnesses), witnesses)

    val base: Set[LSSpec] = specSpace.getSpecs.filter { s => s != specToStep.get }
    (next.map { n => new SpecSpace(base + n, disallowSpecs = specSpace.getDisallowSpecs,
      matcherSpace = specSpace.getMatcherSpace) }.toSet, true)
  }

  def run():LearnResult = {
    val startTime = System.nanoTime()

    val queue = mutable.PriorityQueue[SpecSpace]()(SpecSpaceAnyOrder)
    queue.addOne(initialSpec)
    var specsTested = 0
    while(queue.nonEmpty) {
      specsTested +=1
      val cSpec = queue.dequeue()
      println(s"---\nTesting spec:${cSpec}")
      println(s"\n spec number: ${specsTested}")

      // false if no expansion of this spec can succeed at making all reach locations reachable
      val reachNotRefuted:() => Boolean = () => reachable.par.forall(qry => {
        val res = mkApproxResForQry(qry,cSpec, OverApprox, PreciseApproxMode(false), pkgFilter = reachPkgFilter)
        BounderUtil.interpretResult(res, QueryFinished) match{
          case Witnessed =>
            //println(" reach refuted: false")
            true
          case _ => //proven/timeout
            //println(" reach refuted: true")
            if(dbg){
              println(s"qry:${qry} ")
              println(s"spec:\n  ${cSpec}")
            }
            false
        }})

      // false if no expansion of this spec can prove the target location
      val historiaOverApproxStartTime = System.nanoTime()
      val unreachCanProve = {
        val tgtRes = mkApproxResForQry(target, cSpec, UnderApprox, LimitMaterializationApproxMode(2), unreachPkgFilter)
        BounderUtil.interpretResult(tgtRes, QueryFinished) match {
          case Proven =>
            true
          case Witnessed =>
            false
          case otherRes =>
            //false // dump spec on timeout
            println(s"Attempt to prove unreach resulted in: ${otherRes}")
            !isTerminal(cSpec) // keep spec if it contains holes and timed out
        }
      }
      historiaOverApproxTotalTime += (System.nanoTime() - historiaOverApproxStartTime)

      // maintain lazy and while recording time of second operand
      val unreachCanProveAndReachNotRefuted = if(!unreachCanProve) false else {
        val historiaUnderApproxStartTime = System.nanoTime()
        val out = reachNotRefuted()
        historiaUnderApproxTotalTime += (System.nanoTime() - historiaUnderApproxStartTime)
        out
      }

      if (unreachCanProveAndReachNotRefuted && isTerminal(cSpec)) {
        lastRuntime = System.nanoTime() - startTime
        return LearnSuccess(cSpec)
      }else if( unreachCanProveAndReachNotRefuted ) {
        //TODO: figure out what I was talking about with next comment
        // TODO: should call excludes initial on all witnesses for candidate before adding it to the queue to go throught the loop again
        // take full advantage of past alarms on assertion
        // can we utilize the past results of reachable locations?

        // if we have a candidate spec that includes a past alarm for a reach, we don't need to rerun
        //
        // Get alarm for current spec and target
        // standard approach: I have some function, synthesize something that satisfies property.  We are a little different, not function?
        // ingredients: reachable locations, utilizing message history witness cex, utilizing points to analysis, we have a universe of objects to consider
        // initial universe of objects is materialized abstract state, can existentially quantify one more per step
        // perhaps synthesis for datastructures may be related?
        // "data structure specification synthesis" - synthesizing relation on data structures - internal representation that does not involve quantifiers
        val historiaOverApprox2StartTime = System.nanoTime()
        val overApproxAlarm: Set[IPathNode] = mkApproxResForQry(target, cSpec, OverApprox,
          LimitMaterializationApproxMode(2), pkgFilter = unreachPkgFilter)
        historiaOverApproxTotalTime += (System.nanoTime() - historiaOverApprox2StartTime)

        val synthesisStepStartTime = System.nanoTime()
        val liveAndWit:Set[IPathNode] = overApproxAlarm.filter(pn => pn.qry.isWitnessed || pn.qry.isLive)
        if (liveAndWit.nonEmpty) {
          val nextSpecs = stepSpecSpace(cSpec, liveAndWit)
//          println(s"next specs\n===========\n${nextSpecs._1.mkString("\n---\n")}")
          val filtered = nextSpecs._1.filter { spec => !hasExplored(spec) }
          queue.addAll(filtered)
        }
        synthesisTotalTime += (System.nanoTime() - synthesisStepStartTime)
      }
    }

    lastRuntime = System.nanoTime() - startTime
    LearnFailure //no more spec expansions to try
  }


}
