package edu.colorado.plv.bounder.state

import edu.colorado.plv.bounder.ir.Loc

// Result from symbolic executor
//case class Path(trace: Trace)

// Trace explains the proof with either all backward paths or a counter example
trait Trace
case class FullTrace(paths: TraceNode) extends Trace
case class CounterexampleTrace(witness: TraceNode) extends Trace

case class TraceNode(qry: Qry, predecessor : Set[TraceNode])