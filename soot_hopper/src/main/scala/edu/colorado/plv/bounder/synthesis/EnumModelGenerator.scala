package edu.colorado.plv.bounder.synthesis
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.{Proven, ResultSummary, Witnessed}
import edu.colorado.plv.bounder.ir.{ApproxDir, CNode, ConcGraph, Exact, OverApprox, TMessage, TopTypeSet, TypeSet, UnderApprox}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, Exists, Forall, LSAnyPred, LSAtom, LSBinOp, LSConstraint, LSFalse, LSImplies, LSPred, LSSpec, LSTrue, LSUnOp, NS, Not, OAbsMsg, Or}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecAssignment, SpecSpace, SpecSpaceAnyOrder}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, EncodingTools, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, QueryFinished, SymbolicExecutorConfig}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, IPathNode, InitialQuery, MemoryOutputMode, NullVal, OutputMode, PureVar, State, TopVal}
import edu.colorado.plv.bounder.synthesis.EnumModelGenerator.{NoStep, StepResult, StepSuccessM, StepSuccessP, isTerminal}

import scala.collection.{View, immutable, mutable}
import scala.collection.immutable.Queue
import scala.collection.mutable.ListBuffer

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
                              ,cfg:SymbolicExecutorConfig[M,C])
  extends ModelGenerator(cfg.w.getClassHierarchyConstraints) {
  private val cha = cfg.w.getClassHierarchyConstraints
  private val controlFlowResolver =
    new ControlFlowResolver[M,C](cfg.w, new DefaultAppCodeResolver(cfg.w), cha, cfg.component.map(_.toList),cfg)
  private val ptsMsg = controlFlowResolver.ptsToMsgs(initialSpec.allI)

  def mkApproxResForQry(qry:InitialQuery, spec:SpecSpace, approxDir: ApproxDir):Set[IPathNode] = {
    //TODO:=== do something smarter than recomputing full query each time, doing this for testing right now
    // note: this is just a matter of changing the labels on individual nodes in wit tree
    val approxOfSpec = approxSpec(spec,approxDir)
    val tConfig = cfg.copy(specSpace = approxOfSpec)
    val ex = tConfig.getSymbolicExecutor
    ex.run(qry,MemoryOutputMode).flatMap(_.terminals)
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
    type T = LSPred
    val (pred1Construct, other):(T=>LSPred,T) = if(!isTerminal(p1))
      ((p:T) => predConstruct(p1,p),p2)
    else if(!isTerminal(p2)){
      ((p:T) => predConstruct(p,p2),p1)
    }else
      return StepSuccessP((predConstruct(p1,p2),Set[PureVar]())::Nil)
    mergeOne(pred1Construct, other, scope)
  }

  def mkRel(pv:PureVar, ts:TypeSet, avoid:Set[PureVar]):Set[OAbsMsg] = {
    ptsMsg.flatMap{
      case (msg,argPoints) =>
        val argSwaps = argPoints.map{
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
  def step(pred:LSPred, scope:Map[PureVar,TypeSet]):StepResult = pred match{
    case LifeState.LSAnyPred =>{
      val relMsg: immutable.Iterable[OAbsMsg] = scope.flatMap{case(pv,ts) => mkRel(pv,ts, scope.keySet)}

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

      List(Or,And).foreach { op =>
        mutList.addOne((op(LSAnyPred, LSAnyPred), Set[PureVar]()))
      }
      StepSuccessP(mutList.toList)
    }
//    case AnyAbsMsg =>
//      StepSuccessM(???) //TODO: remove AnyAbsMsg or change prev case
    case Or(l1, l2) => mergeTwo(Or, l1, l2, scope)
    case And(l1, l2) => mergeTwo(And, l1,l2, scope)
    case Forall(x, s) => mergeOne(v => Forall(x,v), s, scope ++ x.map(_ -> TopTypeSet))
    case Exists(x, p) => mergeOne(Exists(x,_), p, scope ++ x.map(_ -> TopTypeSet))
    case n:NS => NoStep
//    case NS(m1, m2) => mergeTwo((a:AbsMsg,b:AbsMsg) => NS(b,a),m2,m1,scope)
    case _:OAbsMsg => NoStep
    case Not(p) => mergeOne(Not,p,scope)
    case _:LSImplies =>
      throw new IllegalArgumentException("Shouldn't be using implies in synthesis")
    case v => NoStep
  }

  private def mkQuant(v:Iterable[PureVar],pred:LSPred):LSPred = {
    if(v.isEmpty) pred else Exists(v.toList, pred)
  }
  /**
   *
   * @param rule to fill a hole
   * @return next spec, whether spec was stepped
   */
  def step(rule:LSSpec, scope:Map[PureVar,TypeSet]):(List[LSSpec],Boolean) = rule match{
    case s@LSSpec(_,_,pred,_,_) =>
      step(pred,scope) match {
        case StepSuccessP(preds) => (preds.map{case (p,quant) => s.copy(pred = mkQuant(quant,p))},true)
        case NoStep => (List(s),false)
      }
  }

  /**
   *
   * @param rule
   * @param state
   * @return
   */
  def mkScope(rule:LSSpec, state:State):Map[PureVar,TypeSet] = {
    val tr = state.sf.traceAbstraction.rightOfArrow
    val directM:Map[PureVar,TypeSet] = tr.flatMap{m =>
      if(rule.target.identitySignature == m.identitySignature){
        rule.target.lsVars.zip(m.lsVars).flatMap{
          case (pv1:PureVar, pv2:PureVar) =>
            Map(pv1 -> state.sf.typeConstraints.getOrElse(pv2,TopTypeSet))
          case _ => Map.empty
        }
      }else None}.toMap
    val enc = EncodingTools.rhsToPred(tr, new SpecSpace(Set(rule))).flatMap(SpecSpace.allI)

    val lsVars = enc.flatMap{m => m.lsVar}
    lsVars.map{v => (v -> state.sf.typeConstraints.getOrElse(v,TopTypeSet))}.foldLeft(directM){
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


  def approxSpec(lsSpec: LSSpec, approxDir: ApproxDir):LSSpec = lsSpec.copy(pred = approxPred(lsSpec.pred, approxDir))

  def approxSpec(spec:SpecSpace, approxDir: ApproxDir):SpecSpace = {
    val specs = spec.getSpecs.map(approxSpec(_,approxDir))
    spec.copy(enableSpecs = specs)
  }

  /**
   *
   * @param spec spec to expand an AST hole
   * @return next spec, whether spec was stepped
   */
  def step(specSpace:SpecSpace, state:State):(Set[SpecSpace],Boolean) = {
    val specToStep = specSpace.sortedEnableSpecs.collectFirst{case (s,_) => s}
    if(specToStep.isEmpty)
      return (Set(specSpace),false)
    val (next:List[LSSpec],changed) =
      step(specToStep.get,mkScope(specToStep.get, state))
    if(!changed) {
      //assert(false) //TODO: probably figure out why this happens...
    }
    val base: Set[LSSpec] = specSpace.getSpecs.filter { s => s != specToStep.get }
    (next.map { n => new SpecSpace(base + n) }.toSet, true)
  }

  def run():LearnResult = {
    // TODO: multiple holes which one is filled first - exploring down in the lattice - want to explore most complete spec first
    // if you consider the alarms - intuition is that we want to consider messages in both alarms for reach/unreach
    // "conflict clause" - used in sat solvers - conjunction that says "don't go there" - ask solver sequence of queries
    //   to ask what holes to fill - key contribution guide search 1) data dependency and 2) conflict clause between reach/unreach
    //   conflict between the reach and unreach that
    //   under approx abstract interp -- somehow minimize materialized footprint in depth first search
    //      - thresher - backwards in concrete and backwards in the abstract
    //      - explicit state model checking backwards - backwards in concrete
    //      - explicit state model checking tries to compile transition system up front to handle unboundedness, loses orig prog
    //      - what we care about is when we include initial (w/ comp) we know we include initial
    // oopsla apr or popl jul
    //   confusion about correctness/incorrectness sound over sound under...  need to precisely define terms.
    //   component thinking - what do you think with respect to the framework/application
    //   what we care about at the end of the day is the classification of the data points and how the over/under approx affects
    //TODO: remove test set thing here
    val queue = mutable.PriorityQueue[SpecSpace]()(SpecSpaceAnyOrder)
    queue.addOne(initialSpec)
    while(queue.nonEmpty) {
      val cSpec = queue.dequeue()
      println(s"---\nTesting spec:${cSpec}")

      // false if no expansion of this spec can succeed at making all reach locations reachable
      val reachNotRefuted:Boolean = reachable.forall(qry => {
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

      if (reachNotRefuted && unreachCanProve && isTerminal(cSpec)) {
        return LearnSuccess(cSpec)
      }else if(reachNotRefuted && unreachCanProve) {
        // Get alarm for current spec and target
        val overApproxAlarm: Set[IPathNode] = mkApproxResForQry(target, cSpec, OverApprox)
        val someAlarm = overApproxAlarm.find(pn => pn.qry.isWitnessed)
        if (!someAlarm.isEmpty) {
          val nextSpecs = step(cSpec, someAlarm.get.state)
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
