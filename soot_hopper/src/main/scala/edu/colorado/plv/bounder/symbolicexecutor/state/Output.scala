package edu.colorado.plv.bounder.symbolicexecutor.state
import java.util.{Objects, Properties}
import java.util.concurrent.{ArrayBlockingQueue, ConcurrentLinkedQueue, Executors}
import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, InternalMethodInvoke, InternalMethodReturn, Loc, MethodLoc, SkippedInternalMethodInvoke, SkippedInternalMethodReturn, WitnessExplanation}
import slick.jdbc.SQLiteProfile.api._

import scala.concurrent.Await
import scala.concurrent.duration._
import upickle.default.{macroRW, ReadWriter => RW}
import upickle.default.{read, write}

import java.util.concurrent.atomic.AtomicInteger
import scala.language.postfixOps
import better.files.File
import com.microsoft.z3.Z3Exception
import edu.colorado.plv.bounder.BounderUtil.{MaxPathCharacterization, ResultSummary}
import edu.colorado.plv.bounder.RunConfig
import edu.colorado.plv.bounder.symbolicexecutor.state.DBOutputMode.nextId
import slick.jdbc
import slick.jdbc.SQLiteProfile
import ujson.Obj

import scala.annotation.tailrec
import scala.collection.mutable
import scala.jdk.CollectionConverters.SeqHasAsJava



sealed trait OutputMode{
  def initializeQuery(startingNodes:Loc, cfg:RunConfig, initialQuery:InitialQuery):Int
  def writeLiveAtEnd(witness: Set[IPathNode], finalizeQryId:Int, status:String,result:ResultSummary,
                     maxPathCharacterization: MaxPathCharacterization, runTime:Long):Unit
}

case object NoOutputMode extends OutputMode {
  override def initializeQuery(startingNodes: Loc, cfg: RunConfig, initialQuery: InitialQuery): Int = -1

  override def writeLiveAtEnd(witness: Set[IPathNode], finalizeQryId: Int, status: String,
                              result: ResultSummary,
                              maxPathCharacterization: MaxPathCharacterization, runTime: Long): Unit = ()
}

case object MemoryOutputMode extends OutputMode {
  override def initializeQuery(startingNodes: Loc, cfg: RunConfig, initialQuery: InitialQuery): Int= -1

  override def writeLiveAtEnd(witness: Set[IPathNode], finalizeQryId: Int, status: String,
                              result: ResultSummary,
                              maxPathCharacterization: MaxPathCharacterization, runTime: Long): Unit = ()
}

/**
 *
 * @param dbfile sqlite file to write detailed results
 */
case class DBOutputMode(dbfile:String) extends OutputMode{
  assert(dbfile.endsWith(".db"), s"Bad db file name $dbfile must end with '.db'")

  private val witnessQry = TableQuery[WitnessTable]
  private val methodQry = TableQuery[MethodTable]
  private val callEdgeQry = TableQuery[CallEdgeTable]
  private val liveAtEnd = TableQuery[LiveAtEnd]
  private val graphQuery = TableQuery[WitnessGraph]
  private val initialQueries = TableQuery[InitialQueryTable]
  import slick.jdbc.SQLiteProfile.api._

  val setupTables = (idb:jdbc.SQLiteProfile.backend.DatabaseDef) => {if(!File(dbfile).exists()) {
    val setup = DBIO.seq(witnessQry.schema.create,
      methodQry.schema.create,
      callEdgeQry.schema.create,
      graphQuery.schema.create,
      liveAtEnd.schema.create,
      initialQueries.schema.create
    )
    Await.result(idb.run(setup), 20 seconds)
  }}

//  private val db = DBOutputMode.getDBForF(dbfile, setupTables)
  private val db = DBOutputMode.getDBForF(dbfile,setupTables)


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
  override def initializeQuery(initial:Loc, config:RunConfig, initialQuery: InitialQuery):Int = {
//    val initialDBNodes = initial.map(_.asInstanceOf[DBPathNode])
    val maxID: Option[Int] = Await.result(db.run(initialQueries.map(_.id).max.result), 30 seconds)
//    val maxID: Option[Int] = initialQueries.map(_.id).max
    val currentID = maxID.getOrElse(0) + 1
    val meta = startMeta()
    val initialQueryStr = write[InitialQuery](initialQuery)
    val initialQueryRow = (currentID, write[Loc](initial),
      initialQueryStr, write[RunConfig](config), meta, "","")
    Await.result(db.run(initialQueries += initialQueryRow), 30 seconds)
    currentID
  }

  /**
   * Get all states grouped by location
   * note: relies on liveAtEnd so won't work if timeout or killed
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
        case c : CallinMethodReturn => Some(c.toString)
        case c : CallinMethodInvoke => Some(c.toString)
        case c : GroupedCallinMethodInvoke => Some(c.toString)
        case c : GroupedCallinMethodReturn => Some(c.toString)
        case c : CallbackMethodInvoke => Some(c.toString)
        case c : CallbackMethodReturn => Some(c.toString)
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

  /**
   * Get the initial queries from the database
   * @return set of path nodes
   */
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

  /**
   * Get all final nodes (earliest in execution) regardless of label
   *
   * @return set of path nodes
   */
  def getNoSucc(): Set[DBPathNode] = {
    // TODO: there is probably a more efficient way to do this
    // get edges
    val qAllEdge = for {
      n <- graphQuery
    } yield (n.src, n.tgt)
    val allEdge = Await.result(db.run(qAllEdge.result), 900 seconds)
    val isTgt: Map[Int, Seq[(Int, Int)]] = allEdge.groupBy {
      case (_, tgt) => tgt
    }
    val isSrc = allEdge.groupBy {
      case (src, _) => src
    }
    val srcButNotTgt: Set[Int] = isSrc.keySet.removedAll(isTgt.keySet)

    srcButNotTgt.flatMap((nodeId: Int) => {
      val q = for {
        n <- witnessQry if (n.id === nodeId)
      } yield n
      Await.result(db.run(q.result), 30 seconds)
    }).map(rowToNode)
  }



  /**
   * Get nodes that are/were in the queue to be processed by the symbex
   * Note: this method is the opposite of the one above
   * @return
   */
  def getLive():Set[DBPathNode] = {
    // get edges
    val qAllEdge = for {
      n <- graphQuery
    } yield (n.src,n.tgt)
    val allEdge = Await.result(db.run(qAllEdge.result), 900 seconds)
    val isTgt: Map[Int, Seq[(Int, Int)]] = allEdge.groupBy{
      case (_,tgt) => tgt
    }
    val isSrc: Map[Int, Seq[(Int, Int)]] = allEdge.groupBy{
      case(src,_) => src
    }
    val srcNotTgt: Set[Int] = isSrc.keySet.removedAll(isTgt.keySet)

    srcNotTgt.flatMap((nodeId: Int) => {
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

  def writeLiveAtEnd(witness: Set[IPathNode], finalizeQryId:Int, status:String,result:ResultSummary,
                     maxPathCharacterization: MaxPathCharacterization, runtime:Long):Unit = {
    flushQueues()
    witness.foreach{n =>
      val dbn = n.asInstanceOf[DBPathNode]
      if(!isNodeWritten(dbn)){
        writeNode(dbn)
      }
    }
    flushQueues()
    val ids = witness.map(n => n.asInstanceOf[DBPathNode].thisID)
    val writeFuture = db.run(liveAtEnd ++= ids)
    Await.result(writeFuture, 600 seconds)
    val updateMetadata = for(q <- initialQueries if q.id === finalizeQryId)yield (q.metadata,q.result,q.interp)
    val meta = Await.result(db.run(updateMetadata.result), 600 seconds)
    assert(meta.size == 1, "No metadata, be sure to call startMeta() on DBOutputMode")
    val updatedMeta = finishMeta(meta.head._1, status)
    Await.result(db.run(updateMetadata.update(updatedMeta, write(result),
      write(maxPathCharacterization))), 600 seconds)
//    ex.shutdown()
  }



//  private val writeNodeQueue = new ConcurrentLinkedQueue[WitTableRow]()
//  private val graphQueue = new ConcurrentLinkedQueue[(Int,Int)]()
  private val writeNodeQueue = new ArrayBlockingQueue[WitTableRow](10000)
  private val graphQueue = new ArrayBlockingQueue[(Int,Int)](10000)
  def flushQueues() = {

    println(s"write node size ${writeNodeQueue.size()}")
    println(s"graph queue size ${graphQueue.size()}")
    val startTime = System.nanoTime()
    this.synchronized {
      if(!writeNodeQueue.isEmpty) {
        val writeNodes = mutable.ListBuffer[WitTableRow]()
        while (!writeNodeQueue.isEmpty) {
          writeNodes.addOne(writeNodeQueue.poll())
        }
        val writeFuture = db.run(witnessQry ++= writeNodes)

        Await.result(writeFuture, 600 seconds)
      }
      if(!graphQueue.isEmpty) {
        val writeGraph = mutable.ListBuffer[(Int, Int)]()
        while (!graphQueue.isEmpty) {
          writeGraph.addOne(graphQueue.poll())
        }
        val graphFuture = db.run(graphQuery ++= writeGraph)
        Await.result(graphFuture, 600 seconds)
      }
    }
    val runtime = (System.nanoTime() - startTime)/1000.0
    println(s"runtime(ms): $runtime")
  }
  def queueNodeWrite(v:WitTableRow, v2:Seq[(Int,Int)]) = {
    // batch together sqlite queries to reduce fsync
    if(!writeNodeQueue.offer(v)){
      flushQueues()
      writeNodeQueue.add(v)
    }
    v2.foreach{v =>
      if(!graphQueue.offer(v)){
        flushQueues()
        graphQueue.add(v)
      }
    }
//    graphQueue.addAll(v2.asJava)
//    if(writeNodeQueue.size() > 1000000 || graphQueue.size() > 1000000){
//      flushQueues()
//    }
  }

  def isNodeWritten(node:DBPathNode):Boolean = {
    val q = for (
      n <- witnessQry if n.id === node.thisID
    ) yield n.id
    Await.result(db.run(q.result), 30 seconds).nonEmpty
  }
  def writeNode(node: DBPathNode): Unit = {
    val qryState = node.qry.searchState.toString
    val loc = node.qry.loc.serialized
    val stateStr = write[State](node.qry.state)
    //TODO: For batch subsumption, "head" element is recorded, this may be confusing
    val row = WitTableRow(node.thisID, qryState, stateStr, loc, node.subsumedID.headOption, node.depth,node.ordDepth)
    val edges:Seq[(Int,Int)] = node.succID.map(sid => (node.thisID, sid))
    queueNodeWrite(row,edges)
  }

  def setSubsumed(node: DBPathNode, subsuming:Option[DBPathNode]) = {
    flushQueues()
    val id = node.thisID
    val q = for(n <- witnessQry if n.id === id) yield n.subsumingState
    val q2 = q.update(subsuming.map(_.thisID))
    val future = db.run(q2)
    Await.result(future, 30 seconds)
  }
  def getAllNodes():Set[DBPathNode] = {
    val q = witnessQry
    val res: Seq[WitTableRow] = Await.result(db.run(q.result), 600 seconds)
    res.map{row =>
      rowToNode(row)
    }.toSet
  }
  def getAllLiveNodes():Set[DBPathNode] = {
    val q = witnessQry
    val res: Seq[WitTableRow] = Await.result(db.run(q.result), 600 seconds)
    res.flatMap{row =>
      val node: DBPathNode = rowToNode(row)
      if(node.subsumedID.isEmpty)
        node.qry.searchState match {
          case Live => Some(node)
          case WitnessedQry(_) => Some(node)
          case Unknown => Some(node)
          case BottomQry => None
        }
      else None
    }.toSet
  }
  def getAllSubsumedStates():Set[(State, State)] = {
    val q = witnessQry
    val res: Seq[WitTableRow] = Await.result(db.run(q.result), 600 seconds)
    res.flatMap{row =>
      val node: DBPathNode = rowToNode(row)
      if(node.subsumedID.nonEmpty) {
        Some((node.state,readNode(node.subsumedID.head).qry.state))
      }
      else None
    }.toSet
  }
  def readNode(id: Int):DBPathNode = {
    val q = witnessQry.filter(_.id === id)
    var res: Seq[WitTableRow] = Await.result(db.run(q.result), 30 seconds)
    if(res.size < 1){
      flushQueues()
      res = Await.result(db.run(q.result), 30 seconds)
    }
    assert(res.size == 1, s"Failed to find unique node id: $id actual size: ${res.size}")

    rowToNode(res.head)
  }

  private def rowToNode(res:WitTableRow) = {
    val id = res.id
    val queryState: String = res.queryState
    val loc: Loc = read[Loc](res.nodeLoc)
    val subsumingId: Option[Int] = res.subsumingState

    val succQry = for (edge <- graphQuery if edge.src === id) yield edge.tgt

    val pred: List[Int] = Await.result(db.run(succQry.result), 30 seconds).toList
    val stateOpt: Option[State] = if(res.nodeState == "") None else Some( read[State](res.nodeState) )
    val qry = (queryState,stateOpt) match {
      case (searchState, Some(state)) => Qry(state, loc, SearchState(searchState))
      case (queryState,_) => throw new IllegalStateException(s"Missing serialized state: $id with state $queryState")
    }
    val depth = res.depth
    val ordDepth = res.ordDepth
    DBPathNode(qry, id, pred, subsumingId.toSet, depth, ordDepth)
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

  import slick.jdbc.GetResult
  import slick.jdbc.SQLActionBuilder

  private val id = new AtomicInteger(0)
  def nextId:Int = {
    id.getAndAdd(1)
  }
  case class StrRes(s: String)
  implicit val getStrResult = GetResult(r => StrRes(r.<<))

  implicit val rw:RW[DBOutputMode] = macroRW
  private val dbs = mutable.HashMap[String, jdbc.SQLiteProfile.backend.DatabaseDef]()
  def getDBForF(dbfile:String,
                setupTables: jdbc.SQLiteProfile.backend.DatabaseDef => Any): jdbc.SQLiteProfile.backend.DatabaseDef = {
    if (!dbs.contains(dbfile)) {
      val db: jdbc.SQLiteProfile.backend.DatabaseDef = {
        Class.forName("org.sqlite.JDBC") // force resolution of sqlite driver
        val prop = new Properties
        prop.setProperty("maxConnections", "1")
//        prop.setProperty("connectionPool" ,"disabled")
        prop.setProperty("keepAliveConnection","true")
//        Database.forURL(url = s"jdbc:sqlite:$dbfile", prop = prop, driver = "org.sqlite.JDBC")

        Database.forURL(url = s"jdbc:sqlite:$dbfile", prop = prop, driver = "org.sqlite.JDBC",
          keepAliveConnection = true)
      }
      setupTables(db)

      //  // TODO turn off synchronous mode sqlite
      //  // PRAGMA schema.synchronous = OFF
      def turnOffFSync(): Unit = {

        import slick.driver.H2Driver.api._
        val res = Await.result(db.run(sql"""PRAGMA synchronous = OFF;""".as[StrRes]), 30 seconds)
        //TODO: === was journal_mode=WAL the issue?
//        val res2 = Await.result(db.run(sql"""PRAGMA journal_mode=WAL;""".as[StrRes]), 30 seconds)
        val res2 = Await.result(db.run(sql"""PRAGMA journal_mode=MEMORY;""".as[StrRes]), 30 seconds)

        //    println(res)
        //    println(res2)
      }

      turnOffFSync()
      dbs.addOne((dbfile,db))
    }
    dbs(dbfile)
  }
//  def closeDB() = {
////    import slick.driver.H2Driver.api._
////    dbs.zipWithIndex.foreach { case ((name, db),ind) =>
////      println(s"Closing database $name $ind")
////      Await.result(db.run(sql""".backup ${name}""".as[StrRes]), 1200 seconds)
////    }
//  }
}

class LiveAtEnd(tag:Tag) extends Table[(Int)](tag,"LIVEATEND"){
  def nodeID = column[Int]("NODE_ID", O.PrimaryKey)
  def * = (nodeID)
}

class WitnessGraph(tag:Tag) extends Table[(Int,Int)](tag, "GRAPH"){
  def src = column[Int]("SRC") //, O.PrimaryKey)
  def tgt = column[Int]("TGT")
  def * = (src,tgt)
}
class InitialQueryTable(tag:Tag) extends Table[(Int, String, String, String, String, String,String)](tag, "INITIAL_QUERY"){
  def id = column[Int]("QUERY_ID", O.PrimaryKey)
  def startingLoc = column[String]("STARTING_LOC")
  def initialQuery = column[String]("INITIAL_QUERY")
  def config = column[String]("CONFIG")
  def metadata = column[String]("META")
  def result = column[String]("RESULT")
  def interp = column[String]("INTERP")
  def * = (id,startingLoc, initialQuery, config, metadata,result,interp)
}

case class WitTableRow(id:Int, queryState:String, nodeState:String, nodeLoc:String,
                       subsumingState:Option[Int],
                       depth:Int, ordDepth:Int
                      ){
  val dummy = try{SearchState(queryState)} catch {
    case t:Throwable =>
      throw t
  }
}
class WitnessTable(tag:Tag) extends Table[WitTableRow](tag,"PATH"){
  def id = column[Int]("NODE_ID", O.PrimaryKey)
  def queryState = column[String]("QUERY_STATE")
  def nodeState = column[String]("NODE_STATE")
  def nodeLoc = column[String]("NODE_LOC")
  def subsumingState = column[Option[Int]]("SUBSUMING_STATE")
  def depth = column[Int]("DEPTH")
  def ordDepth = column[Int]("ORD_DEPTH")
  def * = (id,queryState,nodeState,nodeLoc,subsumingState,depth, ordDepth) <> (WitTableRow.tupled, WitTableRow.unapply)
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

  private def shouldTruncate(loc:Loc):Boolean = false
//    loc match {
//      case _:CallbackMethodReturn => false
//      case _:CallbackMethodInvoke => false
//      case AppLoc(method,line,isPre) =>
//        !line.isFirstLocInMethod || !isPre
//      case _:SkippedInternalMethodInvoke => true
//      case _:SkippedInternalMethodReturn => true
//      case _:InternalMethodInvoke => false
//      case _:InternalMethodReturn => false
//      case _:CallbackMethodReturn => false
//      case _:CallbackMethodInvoke => false
//
//      case _ => true
//    }

  @tailrec
  private def nextNonTrunc(node:IPathNode)(implicit om:OutputMode):IPathNode = {
    val successors = node.succ
    if(successors.isEmpty)
      node // node with no successors should be initial
    else if(shouldTruncate(node.qry.loc)) {
      nextNonTrunc(node.succ.head)
    } else{
      node
    }
  }
  def apply(qry:Qry, succ: List[IPathNode], subsumed: Option[IPathNode])
           (implicit ord: OrdCount, mode: OutputMode = MemoryOutputMode):IPathNode = {
    val depth = if (succ.isEmpty) 0 else succ.map(_.depth).max + 1
    val ordDepth =  if (succ.isEmpty) 0 else succ.map(_.ordDepth).max + ord.delta(qry)
    mode match {
      case NoOutputMode =>
        MemoryPathNode(qry, List.empty, subsumed.toSet, depth, ordDepth)
      case MemoryOutputMode =>
        MemoryPathNode(qry, succ, subsumed.toSet, depth,ordDepth)
      case m@DBOutputMode(_) =>
        val id = nextId

        val succNotSkipped = succ.map(nextNonTrunc)
        val succID = succNotSkipped.map(n => n.asInstanceOf[DBPathNode].thisID)
        val subsumedID = subsumed.map(n => n.asInstanceOf[DBPathNode].thisID)
        val thisNode = DBPathNode(qry, id, succID, subsumedID.toSet,depth,ordDepth)
        if(!shouldTruncate(qry.loc) || succ.isEmpty) {
          m.writeNode(thisNode)
        }
        thisNode
    }
  }
  def unapply(node : IPathNode): Option[(Qry, Boolean)] = node match{
    case MemoryPathNode(qry,_,subsumed,_,_) => Some((qry,subsumed.nonEmpty))
    case DBPathNode(qry,_, _,subsumedID,_,_) =>
      Some((qry,subsumedID.nonEmpty))
  }
}

sealed trait IPathNode {

  /**
   * Get state if you know it is defined
   * @return contained state or throw exception if it does not exist
   */
  def state:State = this.qry.state
  def setError(ze: Throwable)
  def getError: Option[Throwable]

  def methodsInPath(implicit mode : OutputMode): List[Loc] = {
    def getMethod(qry:Qry):Option[Loc] = qry.loc match {
      case AppLoc(_, _, _) => None
      case _ => Some(qry.loc)
    }
    import scala.collection.mutable.ListBuffer

    var out = new ListBuffer[Loc]()
    var currentNode:Option[IPathNode] = Some(this)
    while(currentNode.nonEmpty) {
      out ++= getMethod(currentNode.get.qry)
      currentNode = currentNode.get.succ.headOption
    }
    out.toList
  }


  def depth:Int
  def ordDepth:Int
  def qry:Qry
  def succ(implicit mode : OutputMode):List[IPathNode]
  def subsumed(implicit mode : OutputMode): Set[IPathNode]
  def setSubsumed(v: Set[IPathNode])(implicit mode: OutputMode):IPathNode
  def mergeEquiv(other:IPathNode):IPathNode
  def copyWithNewQry(newQry:Qry):IPathNode
  final def addAlternate(alternatePath: IPathNode): IPathNode = {
    val alternates = qry.state.alternateCmd
    val newState = qry.state.copy(alternateCmd = alternatePath.qry.state.nextCmd ++ alternates)
    this.copyWithNewQry(qry.copy(state = newState))
  }
}

case class MemoryPathNode(qry: Qry, succV : List[IPathNode], subsumedV: Set[IPathNode], depth:Int,
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

  override def setSubsumed(v: Set[IPathNode])(implicit mode: OutputMode): IPathNode = {
    assert(v.nonEmpty, "Value must not be empty for subsuming")
    this.copy(subsumedV = v, qry = qry.copy(state = qry.state.copy(isSimplified = qry.state.isSimplified)))
  }

  override def succ(implicit mode: OutputMode): List[IPathNode] = succV

  override def subsumed(implicit mode: OutputMode): Set[IPathNode] = subsumedV

  override def mergeEquiv(other: IPathNode): IPathNode = {
    val newNextCmd = qry.state.nextCmd.toSet ++ other.qry.state.nextCmd.toSet
    val newState = qry.state.copy(nextCmd = newNextCmd.toList)
    val newQry = qry.copy(state = newState)
    val newSuccV = succV ++ other.asInstanceOf[MemoryPathNode].succV
    this.copy(qry = newQry, succV = newSuccV)
  }

  override def copyWithNewQry(newQry: Qry): IPathNode = this.copy(qry=newQry)

  private var error :Option[Throwable] = None
  override def setError(ze: Throwable): Unit = {
    error = Some(ze)
  }
  override def getError: Option[Throwable] = error
}

case class DBPathNode(qry:Qry, thisID:Int,
                      succID:List[Int],
                      subsumedID: Set[Int], depth:Int, ordDepth:Int) extends IPathNode {
  /**
   * @return string representation of messages in abstract trace
   */
  def dbgTrace:List[String] = qry.state.traceKey
  def dbgHeap:List[String] = qry.state.heapKey
  override def succ(implicit db:OutputMode): List[IPathNode] =
    succID.map(db.asInstanceOf[DBOutputMode].readNode)

  override def subsumed(implicit db:OutputMode): Set[IPathNode] =
    subsumedID.map(db.asInstanceOf[DBOutputMode].readNode)

  override def setSubsumed(v: Set[IPathNode])(implicit db:OutputMode): IPathNode = {
    db.asInstanceOf[DBOutputMode].setSubsumed(this,v.headOption.asInstanceOf[Option[DBPathNode]])
    this.copy(subsumedID = v.map(v2 => v2.asInstanceOf[DBPathNode].thisID),
      qry = qry.copy(state = qry.state.copy(isSimplified = qry.state.isSimplified)))
  }

  override def copyWithNewQry(newQry: Qry): IPathNode = this.copy(qry=newQry)

  override def mergeEquiv(other: IPathNode): IPathNode = {
    val newNextCmd = qry.state.nextCmd.toSet ++ other.qry.state.nextCmd.toSet
    val newState = qry.state.copy(nextCmd = newNextCmd.toList)
    val newQry = qry.copy(state = newState)
    val newSuccID = succID ++ other.asInstanceOf[DBPathNode].succID
    this.copy(qry = newQry, succID = newSuccID)
  }

  //TODO: add error to db output
  private var error :Option[Throwable] = None
  override def setError(ze: Throwable): Unit = {
    error = Some(ze)
  }
  override def getError: Option[Throwable] = error
}
object DBPathNode{
  implicit val rw:RW[DBPathNode] = macroRW
}