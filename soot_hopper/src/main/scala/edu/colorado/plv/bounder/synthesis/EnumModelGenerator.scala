package edu.colorado.plv.bounder.synthesis
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, ResultSummary, Witnessed}
import edu.colorado.plv.bounder.ir.{ApproxDir, CNode, ConcGraph, EmptyTypeSet, Exact, OverApprox, TMessage, TopTypeSet, TypeSet, UnderApprox}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, Exists, Forall, LSAnyPred, LSAtom, LSBinOp, LSConstraint, LSFalse, LSImplies, LSPred, LSSpec, LSTrue, LSUnOp, NS, Not, OAbsMsg, Or}
import edu.colorado.plv.bounder.lifestate.{LSPredAnyOrder, LifeState, SpecAssignment, SpecSpace, SpecSpaceAnyOrder}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, EncodingTools, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, ExecutorConfig, QueryFinished}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, IPathNode, InitialQuery, MemoryOutputMode, NullVal, OutputMode, PureExpr, PureVar, State, TopVal}
import edu.colorado.plv.bounder.synthesis.EnumModelGenerator.{NoStep, StepResult, StepSuccessM, StepSuccessP, isTerminal}

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
  def isTerminal(pred:LSPred):Boolean = pred match {
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
//    case NS(AnyAbsMsg, _) => false
//    case NS(_,AnyAbsMsg) => false
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
                              ,cfg:ExecutorConfig[M,C])
  extends ModelGenerator(cfg.w.getClassHierarchyConstraints) {
  private val cha = cfg.w.getClassHierarchyConstraints
  private val controlFlowResolver =
    new ControlFlowResolver[M,C](cfg.w, new DefaultAppCodeResolver(cfg.w), cha, cfg.component.map(_.toList),cfg)
  private val ptsMsg = controlFlowResolver.ptsToMsgs(initialSpec.allI)

  private val approxResMemo = TrieMap[(InitialQuery, SpecSpace, ApproxDir), Set[IPathNode]]()
  def mkApproxResForQry(qry:InitialQuery, spec:SpecSpace, approxDir: ApproxDir):Set[IPathNode] = {
    val approxOfSpec = approxSpec(spec, approxDir)
    val key = (qry,approxOfSpec, approxDir)
    if(!approxResMemo.contains(key)) {
      //TODO: do something smarter than recomputing full query each time, doing this for testing right now
      // note: this is just a matter of changing the labels on individual nodes in wit tree?
      val tConfig = cfg.copy(specSpace = approxOfSpec)
      val ex = tConfig.getAbstractInterpreter
      val res = ex.run(qry, MemoryOutputMode).flatMap(_.terminals)
      approxResMemo.addOne(key -> res)
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

  def isProgress(from:SpecSpace, to:SpecSpace): Boolean ={
    val specs: Set[(LSSpec, LSSpec)] = from.zip(to)
    specs.forall{ pair => isProgress(pair._1.pred, pair._2.pred) }
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


  def mergeOne(predConstruct:LSPred => LSPred, sub:LSPred, scope:Map[PureVar,TypeSet]):StepResult = {
    step(sub, scope) match{
      case StepSuccessP(preds) => StepSuccessP(preds.map{case (p,tq) => (predConstruct(p),tq)})
      case StepSuccessM(preds) => StepSuccessP(preds.map{case (p,tq) => (predConstruct(p),tq)})
      case NoStep => NoStep
    }
  }
  def mergeTwo(predConstruct:(LSPred,LSPred) => LSPred, p1:LSPred, p2:LSPred, scope:Map[PureVar, TypeSet]):StepResult ={
    //TODO: this function doesn't work, predConstruct does not step!!!!!===============================
    type T = LSPred
    val (pred1Construct, other):(T=>LSPred,T) = if(!isTerminal(p1))
      ((p:T) => predConstruct(p1,p),p2)
    else if(!isTerminal(p2)){
      ((p:T) => predConstruct(p,p2),p1)
    }else
      return StepSuccessP((predConstruct(p1,p2),Set[PureVar]())::Nil)
    mergeOne(pred1Construct, other, scope)
  }

  def mkRel(scope:Map[PureVar,TypeSet]):Set[OAbsMsg] = {
    val scope2  = scope.map{case (k,v) => k.asInstanceOf[PureExpr]-> v}
    val scopeVals: Map[PureExpr,TypeSet] = scope2 + (TopVal -> TopTypeSet)
    ptsMsg.flatMap{ case (msgFromCg, argPts) =>
      // find all possible aliasing intersection between points to set from call graphs
      val positionalOptions: Seq[List[PureExpr]] = msgFromCg.lsVars.zip(argPts).map{
        case (pv:PureVar, ts) =>
          scope.filter{case (_, ts2) => ts.intersectNonEmpty(ts2)}
        case (v, _) => Map(v -> TopTypeSet)
      }.map{_.keys.toList}

      val combinations = BounderUtil.repeatingPerm(positionalOptions, msgFromCg.lsVars.size)
      // filter for things that don't have one part of scope
      val reasonableCombinations = combinations.filter{comb => comb.exists{
        case pureVar: PureVar => scope.contains(pureVar)
        case _ => false
      }}

      // TODO: substitute and return abstract messages
      val out = reasonableCombinations.map{comb => msgFromCg.copy(lsVars = comb)}
      out
    }
  }
  def mkRel(pv:PureVar, ts:TypeSet, avoid:Set[PureVar]):Set[OAbsMsg] = {
    ptsMsg.flatMap{
      case (msg,argPoints) =>
        val argSwaps = argPoints.map{ // preserve index of None locations
          case argPt if argPt.intersectNonEmpty(ts) => Some(pv)
          case _ => None
        }
        argSwaps.zipWithIndex.flatMap{
          case (Some(v), ind) => Some(msg.cloneWithVar(v,ind,avoid))
          case _ => None
        }.toSet
    }
  }
  def absMsgToNs(m:OAbsMsg,scope:Map[PureVar,TypeSet]):Set[NS] ={
    val res = m.lsVar.flatMap{
      case v if scope.contains(v) => mkRel(v, scope(v), scope.keySet).flatMap{om =>
        Set(NS(m, om)) ++ (if(om.lsVars.size > 2){
          Set(NS(m,om.copyMsg(om.lsVars.zipWithIndex.map{
            case (k,v) if v == 2 =>
              NullVal
            case (k,v) => k
          })))
        }else {
          Set.empty
        })
      }
      case _ => None
    }
    res
  }

  def stepBinop(l1: LSPred, l2: LSPred, op:(LSPred,LSPred) => LSPred,
                scope:Map[PureVar, TypeSet], hasAnd:Boolean): StepResult = {
    val l1_step = if (LSPredAnyOrder.depthToAny(l1) < LSPredAnyOrder.depthToAny(l2)) {
      step(l1, scope, hasAnd)
    } else NoStep
    l1_step match {
      case NoStep =>
        step(l2, scope, hasAnd) match {
          case StepSuccessP(preds) => StepSuccessP(preds.map(p => (op(l1, p._1), p._2 ++ scope.keySet)))
          case StepSuccessM(msg) => ???
          case NoStep => NoStep
        }
      case StepSuccessP(preds) => StepSuccessP(preds.map(p => (op(p._1, l2), p._2 ++ scope.keySet)))
    }
  }

  /**
   * Expands LSAnyPred into candidate formula.
   * Note that hasAnd enforces Conjunctive Normal Form and is set to true if and occurs higher in the AST.
   *
   * @param pred
   * @param scope
   * @param hasAnd
   * @return
   */
  def step(pred:LSPred, scope:Map[PureVar,TypeSet], hasAnd:Boolean = false):StepResult = pred match{
    case LifeState.LSAnyPred =>{
      val relMsg: immutable.Iterable[OAbsMsg] = mkRel(scope)//scope.flatMap{case(pv,ts) => mkRel(pv,ts, scope.keySet)}

      val relNS = relMsg.flatMap{m =>
        absMsgToNs(m,scope).map(ns =>
          (ns:LSPred, ns.lsVar.filter(v => !scope.contains(v))))
      }
      val relMsgToAdd = relMsg.map{m => (m.asInstanceOf[LSPred], m.lsVar.filter(!scope.contains(_)))}

      val mutList = new ListBuffer[(LSPred, Set[PureVar])]()
      mutList.addAll(relNS)
      mutList.addAll(relMsgToAdd)
      mutList.addAll(relMsg.map{ m => (Not(m.copyMsg(m.lsVars.map{
        case v:PureVar if scope.contains(v) => v
        case _ => TopVal
      })), Set[PureVar]())})

      val binOps = if(hasAnd) List(Or) else List(Or,And)
      binOps.foreach { op =>
        mutList.addOne((op(LSAnyPred, LSAnyPred), Set[PureVar]()))
      }
      StepSuccessP(mutList.toList)
    }
//    case AnyAbsMsg =>
//      StepSuccessM(???) //TODO: remove AnyAbsMsg or change prev case
    case Or(l1, l2) =>
      stepBinop(l1,l2,Or, scope, hasAnd)
    case And(l1, l2) =>
      stepBinop(l1,l2,And, scope, hasAnd = true)
    case Forall(x, s) => mergeOne(v => Forall(x,v), s, scope ++ x.map(_ -> TopTypeSet))
    case Exists(x, p) => mergeOne(Exists(x,_), p, scope ++ x.map(_ -> TopTypeSet))
    case _:NS => NoStep
//    case NS(m1, m2) => mergeTwo((a:AbsMsg,b:AbsMsg) => NS(b,a),m2,m1,scope)
    case _:OAbsMsg => NoStep
    case Not(_:OAbsMsg) => NoStep
    case Not(p) => throw new IllegalArgumentException(s"bad step: ${Not(p)}")
    case _:LSImplies =>
      throw new IllegalArgumentException("Shouldn't be using implies in synthesis")
    case _ => NoStep
  }

  private def mkQuant(v:Iterable[PureVar],pred:LSPred):LSPred = {
    if(v.isEmpty) pred else Exists(v.toList, pred)
  }
  /**
   *
   * @param rule to fill a hole
   * @return next spec, whether spec was stepped
   */
  def stepSpec(rule:LSSpec, scope:Map[PureVar,TypeSet]):(List[LSSpec],Boolean) = rule match{
    case s@LSSpec(_,_,pred,_,_) =>
      step(pred,scope) match {
        case StepSuccessP(preds) =>
          (preds.map{case (p,quant) => s.copy(pred = mkQuant((quant -- rule.target.lsVar), p))},true)
        case NoStep => (List(s),false)
      }
  }

  /**
   *
   * @param rule
   * @param state
   * @return
   */
  def mkScope(rule:LSSpec, witnesses:Set[IPathNode]):Map[PureVar,TypeSet] = {
    val tr = witnesses.flatMap{w => w.state.sf.traceAbstraction.rightOfArrow}.toSeq
    def unionTC(pv:PureVar):TypeSet = {
      val allTs = witnesses.map{node => node.state.sf.typeConstraints.getOrElse(pv, EmptyTypeSet)}
      allTs.reduceOption((tc1, tc2) => tc1.union(tc2)).getOrElse(EmptyTypeSet)
    }

    val directM:Map[PureVar,TypeSet] = tr.flatMap{m =>
      if(rule.target.identitySignature == m.identitySignature){
        rule.target.lsVars.zip(m.lsVars).flatMap{
          case (pv1:PureVar, pv2:PureVar) =>
            Map(pv1 -> unionTC(pv2) )//state.sf.typeConstraints.getOrElse(pv2,TopTypeSet))
          case _ => Map.empty
        }
      }else None}.toMap
    val enc = EncodingTools.rhsToPred(tr, new SpecSpace(Set(rule))).flatMap(SpecSpace.allI)

    val lsVars = enc.flatMap{m => m.lsVar}
    lsVars.map{v => (v -> unionTC(v))/*state.sf.typeConstraints.getOrElse(v,TopTypeSet))*/}.foldLeft(directM){
      case (acc,(k,v)) if acc.contains(k) => acc + (k -> acc(k).intersect(v))
      case (acc, (k,v)) => acc + (k -> v)
    }
  }

  def approxPred(lsPred: LSPred, approxDir: ApproxDir):LSPred = {
    val replaceAnyWith = approxDir match {
      case OverApprox => LSTrue
      case UnderApprox => LSFalse
      case Exact =>
        ???
    }
    lsPred match {
      case LSAnyPred => replaceAnyWith
      case Or(l1,l2) => Or(approxPred(l1,approxDir), approxPred(l2,approxDir))
      case And(l1,l2) => And(approxPred(l1,approxDir), approxPred(l2,approxDir))
      case Forall(vars, p) => Forall(vars, approxPred(p,approxDir))
      case Exists(vars, p) => Exists(vars,approxPred(p,approxDir))
      case atom: LSAtom => atom
      case v =>
        println(v)
        ???
    }
  }


  def approxSpec(lsSpec: LSSpec, approxDir: ApproxDir):LSSpec =
    lsSpec.copy(pred = EncodingTools.simplifyPred(approxPred(lsSpec.pred, approxDir)))

  def approxSpec(spec:SpecSpace, approxDir: ApproxDir):SpecSpace = {
    val specs = spec.getSpecs.map(approxSpec(_,approxDir))
    spec.copy(enableSpecs = specs)
  }

  /**
   *
   * @param spec spec to expand an AST hole
   * @return next spec, whether spec was stepped
   */
  def step(specSpace:SpecSpace, witnesses:Set[IPathNode]):(Set[SpecSpace],Boolean) = {
    val specToStep = specSpace.sortedEnableSpecs.map(a => (a._1, LSPredAnyOrder.depthToAny(a._1.pred)))
      .sortBy(a => a._2).headOption.map(_._1)
    if(specToStep.isEmpty)
      return (Set(specSpace),false)
    val (next:List[LSSpec],changed) =
      stepSpec(specToStep.get,mkScope(specToStep.get, witnesses))

    val base: Set[LSSpec] = specSpace.getSpecs.filter { s => s != specToStep.get }
    (next.map { n => new SpecSpace(base + n) }.toSet, true)
  }

  def run():LearnResult = {

    val queue = mutable.PriorityQueue[SpecSpace]()(SpecSpaceAnyOrder)
    queue.addOne(initialSpec)
    var specsTested = 0
    while(queue.nonEmpty) {
      specsTested +=1
      val cSpec = queue.dequeue()
      println(s"---\nTesting spec:${cSpec}")
      println(s"\n spec number: ${specsTested}")

      // false if no expansion of this spec can succeed at making all reach locations reachable
      lazy val reachNotRefuted:Boolean = reachable.par.forall(qry => {
        val res = mkApproxResForQry(qry,cSpec, OverApprox)
        BounderUtil.interpretResult(res, QueryFinished) match{
          case Witnessed =>
            //println(" reach refuted: false")
            true
          case Proven =>
            //println(" reach refuted: true")
            false
          case otherRes =>
            //throw new IllegalStateException(s"Failed to finish reachable query. Result: $otherRes Query:$qry")
            false // dump spec on timeout
        }})

      // false if no expansion of this spec can prove the target location
      val unreachCanProve = {
        val tgtRes = mkApproxResForQry(target, cSpec, UnderApprox)
        BounderUtil.interpretResult(tgtRes, QueryFinished) match {
          case Proven =>
            true
          case Witnessed =>
            false
          case otherRes =>
            //throw new IllegalStateException(s"Failure to generate abstract witness or prove target: ${otherRes}")
            false // dump spec on timeout
        }
      }

      if (unreachCanProve && reachNotRefuted && isTerminal(cSpec)) {
        return LearnSuccess(cSpec)
      }else if(reachNotRefuted && unreachCanProve) {
        // Get alarm for current spec and target
        val overApproxAlarm: Set[IPathNode] = mkApproxResForQry(target, cSpec, OverApprox)
        val someAlarm:Set[IPathNode] = overApproxAlarm.filter(pn => pn.qry.isWitnessed)
        if (!someAlarm.isEmpty) {
          val nextSpecs = step(cSpec, someAlarm)
          //println(s"next specs\n===========\n${nextSpecs._1.mkString("\n---\n")}")
          val filtered = nextSpecs._1.filter { spec => !hasExplored(spec) }
          queue.addAll(filtered)
        }
      }
    }

    LearnFailure //no more spec expansions to try
  }


  /**
   *
   * @param posExamples set of traces representing reachable points (List in reverse execution order)
   * @param negExamples
   * @param rulesFor    learn rules restricting the back messages in this set
   * @return an automata represented by transition tuples (source state, transition symbol, target state)
   */
  override def learnRulesFromExamples(target: Set[IPathNode],
                                      reachable: Set[IPathNode],
                                      space: SpecSpace)(implicit outputMode: OutputMode): Option[SpecAssignment] = {
    val targetTraces = target.flatMap(makeTraces(_,space) )
    val reachTraces = target.flatMap(makeTraces(_,space) )
    ???
  }

}
