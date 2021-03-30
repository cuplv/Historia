package edu.colorado.plv.bounder.symbolicexecutor.state
import edu.colorado.plv.bounder.ir.{Loc, MethodLoc}
import javax.naming.InitialContext
import slick.dbio.Effect
import slick.jdbc.SQLiteProfile.api._
import slick.sql.FixedSqlStreamingAction
import soot.jimple.parser.node.AEmptyMethodBody

import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.{Await, Future}
import scala.concurrent.duration._
import upickle.default.{macroRW, ReadWriter => RW}
import upickle.default.{read, write}
import java.util.concurrent.atomic.AtomicInteger

import scala.language.postfixOps
import better.files.File

import scala.collection.immutable

trait ReachingGraph {
  def getPredecessors(qry:Qry) : Iterable[Qry]
  def getSuccessors(qry:Qry) : Iterable[Qry]
}

sealed trait OutputMode

case object MemoryOutputMode extends OutputMode

case class DBOutputMode(dbfile:String) extends OutputMode{

  val dbf = File(dbfile)
  private val witnessQry = TableQuery[WitnessTable]
  private val methodQry = TableQuery[MethodTable]
  private val callEdgeQry = TableQuery[CallEdgeTable]
  private val liveAtEnd = TableQuery[LiveAtEnd]

  val db = Database.forURL(s"jdbc:sqlite:$dbfile",driver="org.sqlite.JDBC")
  if(!dbf.exists()) {
    val setup = DBIO.seq(witnessQry.schema.create,
      methodQry.schema.create,
      callEdgeQry.schema.create,
      liveAtEnd.schema.create)
    Await.result(db.run(setup), 20 seconds)
  }
  private val id = new AtomicInteger(0)
  def nextId:Int = {
    id.getAndAdd(1)
  }

  private val longTimeout = 600 seconds

  /**
   * Get all states grouped by location
   * @return
   */
  def statesBeforeLoc(locLike:String):Map[Loc,Set[(Loc,State,Int, Option[Int])]] = {
    val q = for{
      n <- witnessQry
      nsucc <- witnessQry if (n.pred === nsucc.id) && (nsucc.nodeLoc like locLike)
    } yield (nsucc.nodeLoc, n.nodeLoc, n.nodeState,n.id, n.subsumingState)
    val res: Seq[(String, String,String,Int, Option[Int])] = Await.result(db.run(q.result), longTimeout)
    val grouped: Map[String, Seq[(String, String, String,Int, Option[Int])]] = res.groupBy(_._1)
    val out = grouped.map{case (tgtLoc,predset) => (read[Loc](tgtLoc),
        predset.map{ case (_,stateLoc, state,id, optInt) =>
          (read[Loc](stateLoc), read[State](state), id, optInt) }.toSet )}
    out
  }
  def statesAtLoc(locLike:String):Map[Loc,Set[(State,Int, Option[Int])]] = {
    val q = for{
      n <- witnessQry if (n.nodeLoc like locLike)
    } yield (n.nodeLoc, n.nodeState,n.id, n.subsumingState)
    val res: Seq[(String, String, Int, Option[Int])] = Await.result(db.run(q.result), longTimeout)
    val grouped: Map[String, Seq[(String, String,Int, Option[Int])]] = res.groupBy(_._1)
    val out = grouped.map{case (tgtLoc,predset) => (read[Loc](tgtLoc),
      predset.map{ case (_, state,id, optInt) =>
        (read[State](state), id, optInt) }.toSet )}
    out
  }

  def getTerminal():Set[DBPathNode] = {
    val qLive = for{
      liveId <- liveAtEnd
      n <- witnessQry if(liveId.nodeID === n.id)
    } yield n
//    val qRef = for{
//      n <- witnessQry if(n.queryState === "refuted")
//    } yield n
    val qRef = witnessQry.filter(_.queryState === "refuted")
    val qWit = witnessQry.filter(_.queryState === "witnessed")
    val qSubs = witnessQry.filter(_.subsumingState.isDefined)
    val live = db.run(qLive.result)
    val resLive = Await.result(live, longTimeout).map(rowToNode).toSet
    val resRef = Await.result(db.run(qRef.result),longTimeout).map(rowToNode).toSet
    val resWit = Await.result(db.run(qWit.result),longTimeout).map(rowToNode).toSet
    val resSubs = Await.result(db.run(qSubs.result),longTimeout).map(rowToNode).toSet
    resLive.union(resRef).union(resWit).union(resSubs)
  }

  def writeLiveAtEnd(witness: Set[IPathNode]):Unit = {
    val ids = witness.map(n => n.asInstanceOf[DBPathNode].thisID)
    val writeFuture = db.run(liveAtEnd ++= ids)
    Await.result(writeFuture, 30 seconds)
  }

  def writeNode(node: DBPathNode): Unit = {
    val qryState = node.qry match {
      case SomeQry(_, _) => "live"
      case BottomQry(_, _) => "refuted"
      case WitnessedQry(_, _) => "witnessed"
    }
    val loc = write(node.qry.loc)
    val writeFuture = db.run(witnessQry +=
      (node.thisID, qryState, write(node.qry.state), loc, node.subsumedID, node.succID, node.depth))
    Await.result(writeFuture, 30 seconds)
  }

  def setSubsumed(node: DBPathNode, subsuming:Option[DBPathNode]) = {
    val id = node.thisID
    val q = for(n <- witnessQry if n.id === id) yield n.subsumingState
    val q2 = q.update(subsuming.map(_.thisID))
    Await.result(db.run(q2), 30 seconds)
  }
  def readNode(id: Int):DBPathNode = {
    val q = witnessQry.filter(_.id === id)
    val qFuture = db.run(q.result)
    val res: Seq[(Int, String, String, String, Option[Int], Option[Int], Int)] = Await.result(qFuture, 30 seconds)
    assert(res.size == 1, s"Failed to find unique node id: $id actual size: ${res.size}")
    rowToNode(res.head)
  }

  private def rowToNode(res: (Int, String, String, String, Option[Int], Option[Int], Int)) = {
    val id = res._1
    val queryState: String = res._2
    val loc: Loc = read[Loc](res._4)
    val subsumingId: Option[Int] = res._5
    val pred: Option[Int] = res._6
    val state: State = read[State](res._3)
    val qry = queryState match {
      case "live" => SomeQry(state, loc)
      case "refuted" => BottomQry(state, loc)
      case "witnessed" => WitnessedQry(state, loc)
    }
    val depth = res._7
    DBPathNode(qry, id, pred, subsumingId, depth)
  }

  def writeMethod(method: MethodLoc, isCallback:Boolean):Unit ={
    val writeFuture = db.run(methodQry +=
      (nextId, method.simpleName, method.classType, method.bodyToString,isCallback))
    Await.result(writeFuture, 30 seconds)
  }
  def writeCallEdge(srcName:String, srcClass:String, tgtName:String,tgtClass:String, isCallin:Boolean):Unit = {
    val wf = db.run(callEdgeQry += (nextId, srcName,srcClass,tgtName,tgtClass,isCallin))
    Await.result(wf, 30 seconds)
  }

}
object DBOutputMode{
  implicit val rw:RW[DBOutputMode] = macroRW
}

class LiveAtEnd(tag:Tag) extends Table[(Int)](tag,"LIVEATEND"){
  def nodeID = column[Int]("NODE_ID", O.PrimaryKey)
  def * = (nodeID)
}

class WitnessTable(tag:Tag) extends Table[(Int,String,String,String,Option[Int],Option[Int],Int)](tag,"PATH"){
  def id = column[Int]("NODE_ID", O.PrimaryKey)
  def queryState = column[String]("QUERY_STATE")
  def nodeState = column[String]("NODE_STATE")
  def nodeLoc = column[String]("NODE_LOC")
  def subsumingState = column[Option[Int]]("SUBSUMING_STATE")
  def pred = column[Option[Int]]("PRED")
  def depth = column[Int]("DEPTH")
  def * = (id,queryState,nodeState,nodeLoc,subsumingState,pred,depth)
}
class MethodTable(tag:Tag) extends Table[(Int,String,String,String,Boolean)](tag, "Methods"){
  def id = column[Int]("METHOD_ID", O.PrimaryKey)
  def methodName = column[String]("NAME")
  def declaringClass = column[String]("DECLARING_CLASS")
  def methodBody = column[String]("BODY")
  def isCallback = column[Boolean]("IS_CALLBACK")
  def * = (id,methodName,declaringClass,methodBody, isCallback)
}

class CallEdgeTable(tag:Tag) extends Table[(Int,String,String,String,String,Boolean)](tag,"CALL_EDGES"){
  def id = column[Int]("EDGE_ID", O.PrimaryKey)
  def srcName = column[String]("SRC_NAME")
  def srcClass = column[String]("SRC_CLASS")
  def tgtName = column[String]("TGT_NAME")
  def tgtClass = column[String]("TGT_CLASS")
  def isCallin = column[Boolean]("IS_CALLIN")
  def * = (id,srcName,srcClass,tgtName,tgtClass,isCallin)
}

object PathNode{
  def apply(qry:Qry, succ: Option[IPathNode], subsumed: Option[IPathNode])
           (implicit mode: OutputMode = MemoryOutputMode):IPathNode = {
    val depth = succ.map(_.depth + 1).getOrElse(1)
    mode match {
      case MemoryOutputMode =>
        MemoryPathNode(qry, succ, subsumed, depth)
      case m@DBOutputMode(_) =>
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
  def succ(implicit mode : OutputMode):Option[IPathNode]
  def subsumed(implicit mode : OutputMode): Option[IPathNode]
  def setSubsumed(v: Option[IPathNode])(implicit mode: OutputMode):IPathNode
}

case class MemoryPathNode(qry: Qry, succV : Option[IPathNode], subsumedV: Option[IPathNode], depth:Int) extends IPathNode {
  override def toString:String = {
    val qrystr = qry.toString
    val succstr = succV.map((a: IPathNode) =>
      a.toString).getOrElse("")
    qrystr + "\n" + succstr
  }

  override def setSubsumed(v: Option[IPathNode])(implicit mode: OutputMode): IPathNode = this.copy(subsumedV = v)

  override def succ(implicit mode: OutputMode): Option[IPathNode] = succV

  override def subsumed(implicit mode: OutputMode): Option[IPathNode] = subsumedV
}

case class DBPathNode(qry:Qry, thisID:Int,
                      succID:Option[Int],
                      subsumedID: Option[Int], depth:Int) extends IPathNode {
  override def succ(implicit db:OutputMode): Option[IPathNode] = succID.map(db.asInstanceOf[DBOutputMode].readNode)

  override def subsumed(implicit db:OutputMode): Option[IPathNode] =
    subsumedID.map(db.asInstanceOf[DBOutputMode].readNode)

  override def setSubsumed(v: Option[IPathNode])(implicit db:OutputMode): IPathNode = {
    db.asInstanceOf[DBOutputMode].setSubsumed(this,v.asInstanceOf[Option[DBPathNode]])
    this.copy(subsumedID = v.map(v2 => v2.asInstanceOf[DBPathNode].thisID))
  }
}
object DBPathNode{
  implicit val rw:RW[DBPathNode] = macroRW
}