package edu.colorado.plv.bounder.symbolicexecutor.state
import javax.naming.InitialContext
import slick.jdbc.SQLiteProfile.api._

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.{Await, Future}
import scala.concurrent.duration._
import upickle.default.{macroRW, ReadWriter => RW}
import upickle.default.{read, write}

import scala.language.postfixOps

trait ReachingGraph {
  def getPredecessors(qry:Qry) : Iterable[Qry]
  def getSuccessors(qry:Qry) : Iterable[Qry]
}

sealed trait PathMode
case object MemoryPathMode extends PathMode

case class DBPathMode(dbfile:String) extends PathMode{
  private val qry = TableQuery[WitnessTable]
  val db = Database.forURL(s"jdbc:sqlite:$dbfile",driver="org.sqlite.JDBC")
  val setup = DBIO.seq(qry.schema.create)
  Await.result(db.run(setup), 20 seconds)
  private var id = 0
  def nextId:Int = {
    val oId = id
    id = id + 1
    oId
  }
  def writeNode(node: DBPathNode): Unit = {
    val writeFuture = db.run(qry += (node.thisID, write(node)))
    Await.result(writeFuture, 20 seconds)
  }
  def readNode(id: Int):IPathNode = {
    val q = qry.filter(_.id === id)
    val qFuture = db.run(q.result)
    val res: Seq[(Int, String)] = Await.result(qFuture, 20 seconds)
    assert(res.size == 1, s"Failed to find unique node id: $id actual size: ${res.size}")
    read[DBPathNode](res.head._2)
  }
}
object DBPathMode{
  implicit val rw:RW[DBPathMode] = macroRW
}

class WitnessTable(tag:Tag) extends Table[(Int,String)](tag,"PATH"){
  def id = column[Int]("NODE_ID", O.PrimaryKey)
  def nodevalue = column[String]("NODE_VALUE")
  def * = (id,nodevalue)
}

object PathNode{
  def apply(qry:Qry, succ: Option[IPathNode], subsumed: Option[IPathNode])
           (implicit mode: PathMode = MemoryPathMode):IPathNode = {
    val depth = succ.map(_.depth + 1).getOrElse(1)
    mode match {
      case MemoryPathMode =>
        MemoryPathNode(qry, succ, subsumed, depth)
      case m@DBPathMode(_) =>
        val id = m.nextId
        val succID = succ.map(n => n.asInstanceOf[DBPathNode].thisID)
        val subsumedID = subsumed.map(n => n.asInstanceOf[DBPathNode].thisID)
        val thisNode = DBPathNode(qry, id, succID, subsumedID,depth)
        m.writeNode(thisNode)
        thisNode
    }
  }
  def unapply(node : IPathNode): Option[(Qry, Boolean)] = node match{
    case MemoryPathNode(qry,_,subsumed,_) => Some((qry,subsumed.isDefined))
    case DBPathNode(qry,_, _,subsumedID,_) =>
      Some((qry,subsumedID.isDefined))
  }
}
sealed trait IPathNode{
  def depth:Int
  def qry:Qry
  def succ(implicit mode : PathMode):Option[IPathNode]
  def subsumed(implicit mode : PathMode): Option[IPathNode]
  def setSubsumed(v: Option[IPathNode]):IPathNode
}

case class MemoryPathNode(qry: Qry, succV : Option[IPathNode], subsumedV: Option[IPathNode], depth:Int) extends IPathNode {
  override def toString:String = {
    val qrystr = qry.toString
    val succstr = succV.map((a: IPathNode) =>
      a.toString).getOrElse("")
    qrystr + "\n" + succstr
  }

  override def setSubsumed(v: Option[IPathNode]): IPathNode = this.copy(subsumedV = v)

  override def succ(implicit mode: PathMode): Option[IPathNode] = succV

  override def subsumed(implicit mode: PathMode): Option[IPathNode] = subsumedV
}

case class DBPathNode(qry:Qry, thisID:Int,
                      succID:Option[Int],
                      subsumedID: Option[Int], depth:Int) extends IPathNode {
  override def succ(implicit db:PathMode): Option[IPathNode] = succID.map(db.asInstanceOf[DBPathMode].readNode)

  override def subsumed(implicit db:PathMode): Option[IPathNode] = subsumedID.map(db.asInstanceOf[DBPathMode].readNode)

  override def setSubsumed(v: Option[IPathNode]): IPathNode =
    this.copy(subsumedID = v.map(v2 => v2.asInstanceOf[DBPathNode].thisID))
}
object DBPathNode{
  implicit val rw:RW[DBPathNode] = macroRW
}