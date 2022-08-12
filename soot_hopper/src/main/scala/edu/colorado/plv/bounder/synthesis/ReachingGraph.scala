package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.ir.{Loc, TMessage}

trait Node
case class Reachable(loc:Loc) extends Node
case class Unreachable(loc:Loc) extends Node
case class MessageNode(loc:Loc, message:TMessage) extends Node

case class ReachingGraph(edges:Map[Node,Set[Node]]) {
  def add(from:Node, to:Node):ReachingGraph = {
    val existingTarget = edges.getOrElse(from, Set.empty)
    this.copy(edges + (from -> (existingTarget + to)))
  }

}
