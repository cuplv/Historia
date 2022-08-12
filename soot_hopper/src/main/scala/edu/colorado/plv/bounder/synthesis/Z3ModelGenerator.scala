package edu.colorado.plv.bounder.synthesis

import com.microsoft.z3.{AST, BoolExpr, Context, Expr, IntExpr, IntNum}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecAssignment, SpecSpace}
import edu.colorado.plv.bounder.lifestate.LifeState.{LSAtom, PredicateSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{LiveQry, PureVar, Qry, State}

import scala.annotation.tailrec

class Z3ModelGenerator extends ModelGenerator {
  val ctx : Context = new Context

  /**
   *
   * @param posExamples set of traces representing reachable points (List in reverse execution order)
   * @param negExamples
   * @param rulesFor    learn rules restricting the back messages in this set
   * @return an automata represented by transition tuples (source state, transition symbol, target state)
   */
  override def learnRulesFromExamples(target: ReachingGraph, reachable: ReachingGraph,
                                      space: SpecSpace): SpecAssignment = {
    ???
  }
}

