package edu.colorado.plv.bounder.symbolicexecutor.state

trait ReachingGraph {
  def getPredecessors(qry:Qry) : Iterable[Qry]
  def getSuccessors(qry:Qry) : Iterable[Qry]
}
case class PathNode(qry: Qry, succ : Option[PathNode], subsumed: Option[PathNode]) {
  override def toString:String = {
    val qrystr = qry.toString
    val succstr = succ.map((a: PathNode) =>
      a.toString).getOrElse("")
    qrystr + "\n" + succstr
  }
}