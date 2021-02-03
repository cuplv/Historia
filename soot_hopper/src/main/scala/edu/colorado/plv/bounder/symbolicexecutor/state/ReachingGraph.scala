package edu.colorado.plv.bounder.symbolicexecutor.state

import scalaz.Memo

trait ReachingGraph {
  def getPredecessors(qry:Qry) : Iterable[Qry]
  def getSuccessors(qry:Qry) : Iterable[Qry]
}

object PathNode{
  def memDepth = Memo.mutableHashMapMemo((p:PathNode) => p.iDepth)
}
case class PathNode(qry: Qry, succ : Option[PathNode], subsumed: Option[PathNode]) {
  override def toString:String = {
    val qrystr = qry.toString
    val succstr = succ.map((a: PathNode) =>
      a.toString).getOrElse("")
    qrystr + "\n" + succstr
  }
  private def iDepth:Int = succ match{
    case None => 1
    case Some(node) => node.iDepth + 1
  }
  def depth = PathNode.memDepth(this)
}