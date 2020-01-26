package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.state.{Path, Qry}

trait SymbolicExecutor {
  /**
   *
   * @param qry - a source location and an assertion to prove
   * @return None if the assertion at that location is unreachable, Some(Path) if it is reachable.
   *         Path is the witness path
   */
  def executeBackward(qry : Qry) : Option[Path]
}
