package edu.colorado.plv.bounder.synthesis


trait ModelGenerator {
  this: Z3ModelGenerator =>

  /**
   *
   * @param posExamples set of traces representing reachable points (List in reverse execution order)
   * @param negExamples
   * @param rulesFor    learn rules restricting the back messages in this set
   * @return an automata represented by transition tuples (source state, transition symbol, target state)
   */
  def learnRulesFromExamples(posExamples: Set[List[TraceMessage]],
                             negExamples: Set[List[TraceMessage]],
                             rulesFor: List[TraceMessage]): Unit //TODO: Return type

}
sealed case class TraceMessage(ident:String, v:Int, isBackMessage:Boolean)