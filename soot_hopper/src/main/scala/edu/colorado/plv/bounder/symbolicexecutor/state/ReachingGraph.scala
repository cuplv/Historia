package edu.colorado.plv.bounder.symbolicexecutor.state
import java.util.Objects

import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, InternalMethodInvoke, InternalMethodReturn, Loc, MethodLoc, SkippedInternalMethodInvoke, SkippedInternalMethodReturn}
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
import edu.colorado.plv.bounder.RunConfig
import ujson.{Obj, Value}

import scala.annotation.tailrec
import scala.collection.mutable

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
  private val graphQuery = TableQuery[WitnessGraph]
  private val initialQueries = TableQuery[InitialQueryTable]
  import slick.jdbc.SQLiteProfile.api._

//  val db = Database.forURL(s"jdbc:sqlite:$dbfile",driver="org.sqlite.JDBC")
  Class.forName("org.sqlite.JDBC") // force resolution of sqlite driver
  val db = Database.forURL(s"jdbc:sqlite:$dbfile",Map("maxConnections" -> "1"))
  if(!dbf.exists()) {
    val setup = DBIO.seq(witnessQry.schema.create,
      methodQry.schema.create,
      callEdgeQry.schema.create,
      graphQuery.schema.create,
      liveAtEnd.schema.create,
      initialQueries.schema.create
    )
    Await.result(db.run(setup), 20 seconds)
  }
  private val id = new AtomicInteger(0)
  def nextId:Int = {
    id.getAndAdd(1)
  }

  private val longTimeout = 600 seconds

  def startMeta():String = {
    import java.time.Instant
    val startTime = Instant.now.getEpochSecond
    val res = ujson.Obj("StartTime" -> startTime, "Status" -> "Started").toString
    res
  }
  def finishMeta(oldMeta:String, status:String):String = {
    import java.time.Instant
    val endTime = Instant.now.getEpochSecond
    val oldMetaParsed = ujson.read(oldMeta)
    val newMeta = oldMetaParsed match{
      case Obj(v) =>
        v + ("EndTime" -> ujson.Num(endTime)) + ("Status" -> ujson.Str(status))
    }
    ujson.write(ujson.Obj.from(newMeta))
  }

  /**
   *
   * @param initial path node initially explored
   * @param config run configuration
   * @param initialQuery location and type of query
   * @return id for query
   */
  def initializeQuery(initial:Set[IPathNode], config:RunConfig, initialQuery: InitialQuery):Int = {
    val initialDBNodes = initial.map(_.asInstanceOf[DBPathNode])
    val maxID: Option[Int] = Await.result(db.run(initialQueries.map(_.id).max.result), 30 seconds)
    val currentID = maxID.getOrElse(0) + 1
    val meta = startMeta()
    initialDBNodes.foreach { initialDB =>
      val initialQueryRow = (currentID, initialDB.thisID,
        write[InitialQuery](initialQuery), write[RunConfig](config), meta)
      Await.result(db.run(initialQueries += initialQueryRow), 30 seconds)
    }
    currentID
  }
  def markDeadend():Unit = {
    ???
  }

  /**
   * Get all states grouped by location
   * @return
   */
  def liveTraces():List[List[DBPathNode]] = {
//    val liveq = liveAtEnd.map(_.nodeID) //.map(_.nodeID)
    val liveq = for{
      liveId <- liveAtEnd
      n <- witnessQry if n.id === liveId.nodeID
    } yield n
    val nodePaths = Await.result(db.run(liveq.result), 30 seconds)
      .map(v => rowToNode(v)::Nil).toList
    @tailrec
    def traceBack(paths: List[List[DBPathNode]],
                  completed: List[List[DBPathNode]]):List[List[DBPathNode]] = paths match{
      case (h::t1)::t2 =>
        val succs = h.succ(this)
        if(succs.isEmpty)
          traceBack(t2, (h::t1)::completed)
        else
          traceBack((succs.head.asInstanceOf[DBPathNode] :: h :: t1)::t2, completed)
      case Nil => completed
    }
    traceBack(nodePaths, Nil).map(t => t.reverse)
  }
  def printObsMessages(nodes:List[DBPathNode]):List[String] = {
    nodes.flatMap{n =>
      n.qry.loc match {
        case c @ CallinMethodReturn(fmwClazz, fmwName) => Some(c.toString)
        case c @ CallinMethodInvoke(fmwClazz, fmwName) => Some(c.toString)
        case c @ GroupedCallinMethodInvoke(targetClasses, fmwName) => Some(c.toString)
        case c @ GroupedCallinMethodReturn(targetClasses, fmwName) => Some(c.toString)
        case c @ CallbackMethodInvoke(fmwClazz, fmwName, loc) => Some(c.toString)
        case c @ CallbackMethodReturn(fmwClazz, fmwName, loc, line) => Some(c.toString)
        case _ => None
      }}
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

  def getNoPred():Set[DBPathNode] = {
    // TODO: there is probably a more efficient way to do this
    // get edges
    val qAllEdge = for {
      n <- graphQuery
    } yield (n.src,n.tgt)
    val allEdge = Await.result(db.run(qAllEdge.result), 900 seconds)
    val isTgt: Map[Int, Seq[(Int, Int)]] = allEdge.groupBy{
      case (_,tgt) => tgt
    }
    val isSrc = allEdge.groupBy{
      case(src,_) => src
    }
    val tgtButNotSrc: Set[Int] = isTgt.keySet.removedAll(isSrc.keySet)

    tgtButNotSrc.flatMap((nodeId: Int) => {
      val q = for {
        n <- witnessQry if (n.id === nodeId)
      } yield n
      Await.result(db.run(q.result), 30 seconds)
    }).map(rowToNode)
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

  def writeLiveAtEnd(witness: Set[IPathNode], finalizeQryId:Int, status:String):Unit = {
    val ids = witness.map(n => n.asInstanceOf[DBPathNode].thisID)
    val writeFuture = db.run(liveAtEnd ++= ids)
    Await.result(writeFuture, 30 seconds)
    val updateMetadata = for(q <- initialQueries if q.id === finalizeQryId)yield q.metadata
    val meta = Await.result(db.run(updateMetadata.result), 600 seconds)
    assert(meta.size == 1)
    val updatedMeta = finishMeta(meta.head, status)
    Await.result(db.run(updateMetadata.update(updatedMeta)), 600 seconds)
  }

  def writeNode(node: DBPathNode): Unit = {
    val qryState = node.qry match {
      case SomeQry(_, _) => "live"
      case BottomQry(_, _) => "refuted"
      case WitnessedQry(_, _) => "witnessed"
    }
    val loc = write(node.qry.loc)
    val writeFuture = db.run(witnessQry +=
      (node.thisID, qryState, write(node.qry.state), loc, node.subsumedID, node.depth))
    Await.result(writeFuture, 30 seconds)
    val edges: Seq[(Int, Int)] = node.succ(this).map(sid => (node.thisID,sid.asInstanceOf[DBPathNode].thisID))
    val writeGraphFuture = db.run(graphQuery ++= edges)
    Await.result(writeGraphFuture,30 seconds)
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
    val res: Seq[(Int, String, String, String, Option[Int], Int)] = Await.result(qFuture, 30 seconds)
    assert(res.size == 1, s"Failed to find unique node id: $id actual size: ${res.size}")
    rowToNode(res.head)
  }

  private def rowToNode(res: (Int, String, String, String, Option[Int], Int)) = {
    val id = res._1
    val queryState: String = res._2
    val loc: Loc = read[Loc](res._4)
    val subsumingId: Option[Int] = res._5

    val succQry = for (edge <- graphQuery if edge.src === id) yield edge.tgt

    val pred: List[Int] = Await.result(db.run(succQry.result), 30 seconds).toList
    val state: State = read[State](res._3)
    val qry = queryState match {
      case "live" => SomeQry(state, loc)
      case "refuted" => BottomQry(state, loc)
      case "witnessed" => WitnessedQry(state, loc)
    }
    val depth = res._6
    DBPathNode(qry, id, pred, subsumingId, depth,-1)
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

class WitnessGraph(tag:Tag) extends Table[(Int,Int)](tag, "GRAPH"){
  def src = column[Int]("SRC", O.PrimaryKey)
  def tgt = column[Int]("TGT")
  def * = (src,tgt)
}
class InitialQueryTable(tag:Tag) extends Table[(Int, Int, String, String, String)](tag, "INITIAL_QUERY"){
  def id = column[Int]("QUERY_ID", O.PrimaryKey)
  def startingNodeID = column[Int]("STARTING_NODE_ID")
  def initialQuery = column[String]("INITIAL_QUERY")
  def config = column[String]("CONFIG")
  def metadata = column[String]("META")
  def * = (id,startingNodeID, initialQuery, config, metadata)
}

class WitnessTable(tag:Tag) extends Table[(Int,String,String,String,Option[Int],Int)](tag,"PATH"){
  def id = column[Int]("NODE_ID", O.PrimaryKey)
  def queryState = column[String]("QUERY_STATE")
  def nodeState = column[String]("NODE_STATE")
  def nodeLoc = column[String]("NODE_LOC")
  def subsumingState = column[Option[Int]]("SUBSUMING_STATE")
  def depth = column[Int]("DEPTH")
  def * = (id,queryState,nodeState,nodeLoc,subsumingState,depth)
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
trait OrdCount extends Ordering[IPathNode]{
  def delta(current:Qry):Int
}
object PathNode{
  def apply(qry:Qry, succ: List[IPathNode], subsumed: Option[IPathNode])
           (implicit ord: OrdCount, mode: OutputMode = MemoryOutputMode):IPathNode = {
    val depth = if (succ.isEmpty) 0 else succ.map(_.depth).max + 1
    val ordDepth =  if (succ.isEmpty) 0 else succ.map(_.ordDepth).max + ord.delta(qry)
    mode match {
      case MemoryOutputMode =>
        MemoryPathNode(qry, succ, subsumed, depth,ordDepth)
      case m@DBOutputMode(_) =>
        val id = m.nextId
        val succID = succ.map(n => n.asInstanceOf[DBPathNode].thisID)
        val subsumedID = subsumed.map(n => n.asInstanceOf[DBPathNode].thisID)
        val thisNode = DBPathNode(qry, id, succID, subsumedID,depth,ordDepth)
        m.writeNode(thisNode)
        thisNode
    }
  }
  def unapply(node : IPathNode): Option[(Qry, Boolean)] = node match{
    case MemoryPathNode(qry,_,subsumed,_,_) => Some((qry,subsumed.isDefined))
    case DBPathNode(qry,_, _,subsumedID,_,_) =>
      Some((qry,subsumedID.isDefined))
  }
}

sealed trait IPathNode{

  def depth:Int
  def ordDepth:Int
  def qry:Qry
  def succ(implicit mode : OutputMode):List[IPathNode]
  def subsumed(implicit mode : OutputMode): Option[IPathNode]
  def setSubsumed(v: Option[IPathNode])(implicit mode: OutputMode):IPathNode
  def copyWithNewLoc(upd: Loc=>Loc):IPathNode
  def mergeEquiv(other:IPathNode):IPathNode
  def copyWithNewQry(newQry:Qry):IPathNode
  final def addAlternate(alternatePath: IPathNode): IPathNode = {
    val alternates = qry.state.alternateCmd
    val newState = qry.state.copy(alternateCmd = alternatePath.qry.state.nextCmd ++ alternates)
    this.copyWithNewQry(qry.copyWithNewState(newState))
  }
}

case class MemoryPathNode(qry: Qry, succV : List[IPathNode], subsumedV: Option[IPathNode], depth:Int,
                          ordDepth:Int) extends IPathNode {
  override def toString:String = {
    val qrystr = qry.toString
    val succstr = succV.headOption.map((a: IPathNode) =>
      a.toString).getOrElse("")
    qrystr + "\n" + succstr
  }

  override def hashCode(): Int = {
    // Exclude successors from hash code
    Objects.hash(qry,depth,ordDepth)
  }

  override def setSubsumed(v: Option[IPathNode])(implicit mode: OutputMode): IPathNode = this.copy(subsumedV = v)

  override def succ(implicit mode: OutputMode): List[IPathNode] = succV

  override def subsumed(implicit mode: OutputMode): Option[IPathNode] = subsumedV

  override def copyWithNewLoc(upd:Loc=>Loc): IPathNode = this.copy(qry.copyWithNewLoc(upd))

  override def mergeEquiv(other: IPathNode): IPathNode = {
    val newNextCmd = qry.state.nextCmd.toSet ++ other.qry.state.nextCmd.toSet
    val newState = qry.state.copy(nextCmd = newNextCmd.toList)
    val newQry = qry.copyWithNewState(newState)
    val newSuccV = succV ++ other.asInstanceOf[MemoryPathNode].succV
    this.copy(qry = newQry, succV = newSuccV)
  }

  override def copyWithNewQry(newQry: Qry): IPathNode = this.copy(qry=newQry)
}

case class DBPathNode(qry:Qry, thisID:Int,
                      succID:List[Int],
                      subsumedID: Option[Int], depth:Int, ordDepth:Int) extends IPathNode {
  override def succ(implicit db:OutputMode): List[IPathNode] = succID.map(db.asInstanceOf[DBOutputMode].readNode)

  override def subsumed(implicit db:OutputMode): Option[IPathNode] =
    subsumedID.map(db.asInstanceOf[DBOutputMode].readNode)

  override def setSubsumed(v: Option[IPathNode])(implicit db:OutputMode): IPathNode = {
    db.asInstanceOf[DBOutputMode].setSubsumed(this,v.asInstanceOf[Option[DBPathNode]])
    this.copy(subsumedID = v.map(v2 => v2.asInstanceOf[DBPathNode].thisID))
  }

  //TODO: Delete later
  override def copyWithNewLoc(upd:Loc=>Loc): IPathNode = this.copy(qry.copyWithNewLoc(upd))

  override def copyWithNewQry(newQry: Qry): IPathNode = this.copy(qry=newQry)

  override def mergeEquiv(other: IPathNode): IPathNode = {
    val newNextCmd = qry.state.nextCmd.toSet ++ other.qry.state.nextCmd.toSet
    val newState = qry.state.copy(nextCmd = newNextCmd.toList)
    val newQry = qry.copyWithNewState(newState)
    val newSuccID = succID ++ other.asInstanceOf[DBPathNode].succID
    this.copy(qry = newQry, succID = newSuccID)
  }
}
object DBPathNode{
  implicit val rw:RW[DBPathNode] = macroRW
}