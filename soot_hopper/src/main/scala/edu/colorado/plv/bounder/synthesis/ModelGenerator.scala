package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.lifestate.{SpecAssignment, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{IPathNode, OutputMode}


trait ModelGenerator {
  this: Z3ModelGenerator =>

  /**
   *
   * @param posExamples set of traces representing reachable points (List in reverse execution order)
   * @param negExamples
   * @param rulesFor    learn rules restricting the back messages in this set
   * @return an automata represented by transition tuples (source state, transition symbol, target state)
   */
  def learnRulesFromExamples(target: Set[IPathNode],
                             reachable: Set[IPathNode],
                             space:SpecSpace)(implicit outputMode: OutputMode): Option[SpecAssignment]

}