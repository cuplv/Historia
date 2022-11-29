package edu.colorado.plv.bounder.synthesis
import edu.colorado.plv.bounder.ir.{CNode, ConcGraph, OverApprox, TMessage}
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

  def isTerminal(spec:SpecSpace):Boolean = {
    ???
  }

  def step(rule:LSSpec):LSSpec = {
    ???
  }

  def step(spec:SpecSpace):SpecSpace = {
    ???
  }

  def learnRulesFromConcGraph(target:Set[ConcGraph], reachable:Set[ConcGraph], space:SpecSpace)
                             (implicit cha:ClassHierarchyConstraints):Option[SpecSpace] = {
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
