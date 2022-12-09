package edu.colorado.plv.bounder.synthesis
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.ResultSummary
import edu.colorado.plv.bounder.ir.{CNode, ConcGraph, OverApprox, TMessage, TopTypeSet, TypeSet}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, AnyAbsMsg, Exists, Forall, LSConstraint, LSFalse, LSImplies, LSPred, LSSpec, LSTrue, NS, Not, OAbsMsg, Or}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecAssignment, SpecSpace}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, QueryFinished, SymbolicExecutorConfig}
import edu.colorado.plv.bounder.symbolicexecutor.state.{IPathNode, InitialQuery, MemoryOutputMode, OutputMode}
import edu.colorado.plv.bounder.synthesis.EnumModelGenerator.{NoStep, StepResult, StepSuccessM, StepSuccessP, isTerminal}
import edu.colorado.plv.bounder.symbolicexecutor.state.PureVar

import scala.collection.mutable
import scala.collection.immutable.Queue

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
    case NS(AnyAbsMsg, _) => false
    case NS(_,AnyAbsMsg) => false
    case _:NS => true
    case _:OAbsMsg => true
    case AnyAbsMsg => false
    case Not(p) => isTerminal(p)
  }
  def isTerminal(lsSpec: LSSpec):Boolean = lsSpec match{
    case LSSpec(_,_,pred,_,_) => isTerminal(pred)
  }
  def isTerminal(spec:SpecSpace):Boolean =
    spec.getSpecs.forall(isTerminal)

  sealed trait StepResult
  case class StepSuccessP(preds:List[LSPred], toQuant:Set[PureVar]) extends StepResult
  case class StepSuccessM(msg:List[OAbsMsg], toQuant:Set[PureVar]) extends StepResult
  case object NoStep extends StepResult


}
class EnumModelGenerator[M,C](target:InitialQuery,reachable:Set[InitialQuery], initialSpec:SpecSpace
                              ,cfg:SymbolicExecutorConfig[M,C])
  extends ModelGenerator(cfg.w.getClassHierarchyConstraints) {
  private val cha = cfg.w.getClassHierarchyConstraints
  private val controlFlowResolver =
    new ControlFlowResolver[M,C](cfg.w, new DefaultAppCodeResolver(cfg.w), cha, cfg.component.map(_.toList),cfg)
  private val ptsMsg = controlFlowResolver.ptsToMsgs(initialSpec.allI)

  def mkOverApproxResForQry(qry:InitialQuery, spec:SpecSpace):Set[IPathNode] = {
    //TODO:=== do something smarter than recomputing full query each time, doing this for testing right now
    // note: this is just a matter of changing the labels on individual nodes in wit tree
    val tConfig = cfg.copy(specSpace = spec)
    val ex = tConfig.getSymbolicExecutor
    ex.run(qry,MemoryOutputMode).flatMap(_.terminals)
  }

  private val exploredSpecs = mutable.HashSet[SpecSpace]()
  private def hasExplored(spec:SpecSpace):Boolean = {
    if(exploredSpecs.contains(spec)){
      true
    }else {
      exploredSpecs.add(spec)
      false
    }
  } //TODO: be smarter to avoid redundant search


  def mergeOne(predConstruct:LSPred => LSPred, sub:LSPred, scope:Map[PureVar,TypeSet]):StepResult = {
    step(sub, scope) match{
      case StepSuccessP(preds,tq) => StepSuccessP(preds.map(predConstruct),tq)
      case StepSuccessM(preds,tq) => StepSuccessP(preds.map(predConstruct),tq)
      case NoStep => NoStep
    }
  }
  def mergeTwo[T<:LSPred](predConstruct:(T,T) => LSPred, p1:T, p2:T, scope:Map[PureVar, TypeSet]):StepResult ={
    ???
  }

  def step(pred:LSPred, scope:Map[PureVar,TypeSet]):StepResult = pred match{
    case LifeState.LSAnyPred =>
      StepSuccessP(???,???)
    case AnyAbsMsg =>
      StepSuccessM(???,???)
    case Or(l1, l2) => mergeTwo(Or, l1, l2, scope)
    case And(l1, l2) => mergeTwo(And, l1,l2, scope)
    case Forall(x, s) => mergeOne(v => Forall(x,v), s, scope ++ x.map(_ -> TopTypeSet))
    case Exists(x, p) => mergeOne(Exists(x,_), p, scope ++ x.map(_ -> TopTypeSet))
    case NS(m1, m2) => mergeTwo((a:AbsMsg,b:AbsMsg) => NS(b,a),m2,m1,scope)
    case _:OAbsMsg => NoStep
    case Not(p) => mergeOne(Not,p,scope)
    case _:LSImplies =>
      throw new IllegalArgumentException("Shouldn't be using implies in synthesis")
    case v => NoStep
  }
  def step(rule:LSSpec):LSSpec = {
    ???
  }

  def step(spec:SpecSpace):SpecSpace = {
    ???
  }

  def run():LearnResult = {
    def iRun(queue: Queue[SpecSpace]):LearnResult = {
      val cSpec = queue.head
      val rest = queue.tail

      if(isTerminal(cSpec)){
        val tgtRes = mkOverApproxResForQry(target,cSpec)
        val reachRes = reachable.map(mkOverApproxResForQry(_,cSpec))
        //BounderUtil.interpretResult(res, QueryFinished)
        ??? //TODO ===
      }else{
        val nextSpecs = step(cSpec)
        ???
      }
    }
    iRun(Queue(initialSpec))
  }


  //TODO: ====
  sealed trait LearnResult

  /**
   * Exact
   * * @param space
   */
  case class LearnSuccess(space:SpecSpace) extends LearnResult
  case class LearnCont(target:Set[(TMessage, LSPred)], reachable: Set[(TMessage, LSPred)]) extends LearnResult

  def learnRulesFromConcGraph(target:Set[ConcGraph], reachable:Set[ConcGraph], space:SpecSpace)
                             (implicit cha:ClassHierarchyConstraints, solver:Z3StateSolver):Option[SpecSpace] = {
    def iLearn(target:Set[ConcGraph], reachable:Set[ConcGraph],
               workList:List[SpecSpace], visited:Set[SpecSpace]): Option[SpecSpace]={
      if(workList.isEmpty)
        return None
      val currentSpace = workList.head
      lazy val tgtLive:Boolean = target.exists{c =>
        //TODO: skip if a path must exist to the target
        val res: Set[(CNode, LSPred)] = c.filter(space)
        ???
      }
      lazy val reachLive = reachable.exists{c =>
        //TODO: skip if no path exists to a reachable location
        val res = c.filter(space)
        ???
      }
      if(tgtLive && reachLive) {
        if(isTerminal(currentSpace))
          Some(currentSpace)
        else if(!visited.contains(currentSpace)) {
          val nextSpace = step(currentSpace)
          iLearn(target, reachable, nextSpace::workList.tail, visited + currentSpace)
        }else{
          ???
        }
      }else{
        ???
      }
    }
    iLearn(target, reachable, List(space), Set())
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
