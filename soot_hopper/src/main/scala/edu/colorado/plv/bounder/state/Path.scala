package edu.colorado.plv.bounder.state

import edu.colorado.plv.bounder.ir.Loc

// Result from symbolic executor
//case class Path(trace: Trace)

// Trace explains the proof with either all backward paths or a counter example
trait Trace
case class FullTrace(paths: PathNode) extends Trace
case class CounterexampleTrace(witness: PathNode) extends Trace

case class PathNode(qry: Qry, predecessor : Set[PathNode]) {
  override def toString:String = qry.toString
}