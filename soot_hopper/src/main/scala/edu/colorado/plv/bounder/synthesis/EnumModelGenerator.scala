package edu.colorado.plv.bounder.synthesis
import edu.colorado.plv.bounder.ir.{ConcGraph, OverApprox, TMessage}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, LSFalse, LSPred, LSSpec, LSTrue, OAbsMsg}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecAssignment, SpecSpace}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{IPathNode, OutputMode}

class EnumModelGenerator(implicit cha: ClassHierarchyConstraints) extends ModelGenerator(cha) {


//  def mkTemporalFormula(pred: LSPred, approxDir: ApproxDir):LSPred = pred match {
//    case LifeState.LSAnyPred => approxDir match {
//      case OverApprox => LSTrue
//      case UnderApprox => LSFalse
//    }
//    case And(l1,l2) => And(mkTemporalFormula(l1, approxDir), mkTemporalFormula(l2, approxDir))
//    case LifeState.Forall(vars, p) => LifeState.Forall(vars, mkTemporalFormula(p, approxDir))
//    case LifeState.Exists(vars, p) => LifeState.Exists(vars, mkTemporalFormula(p, approxDir))
//    case LifeState.LSImplies(l1, l2) => LifeState.LSImplies(mkTemporalFormula(l1, approxDir), mkTemporalFormula(l2, approxDir))
//    case atom: LifeState.LSAtom => atom
//    case o:OAbsMsg => o
//    case _ =>
//      ???
//  }
//
//  def mkApproxSpace(space:SpecSpace, approxDir:ApproxDir):SpecSpace = {
//    val overSpecs = space.getSpecs.map{
//      case LSSpec(univQuant, existQuant, pred, target, rhsConstraints) =>
//        LSSpec(univQuant, existQuant, mkTemporalFormula(pred, approxDir), target, rhsConstraints)
//    }
//    //disallowSpecs:Set[LSSpec] = Set(), matcherSpace:Set[Once] = Set()) {
//    new SpecSpace(overSpecs, space.getDisallowSpecs, space.getMatcherSpace)
//  }
  sealed trait LearnResult

  /**
   * Exact
   * * @param space
   */
  case class LearnSuccess(space:SpecSpace) extends LearnResult
  case class LearnCont(target:Set[(TMessage, LSPred)], reachable: Set[(TMessage, LSPred)]) extends LearnResult


  def learnRulesFromConcGraph(target:Set[ConcGraph], reachable:Set[ConcGraph], space:SpecSpace):Option[SpecSpace] = {
    def iLearn(target:Set[ConcGraph], reachable:Set[ConcGraph],
               worklist:List[SpecSpace], visited:Set[SpecSpace]): Option[SpecSpace]={
      val over = target.map(c => c.filter(space))
      ???
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
