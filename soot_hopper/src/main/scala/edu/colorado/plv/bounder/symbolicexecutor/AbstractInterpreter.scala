package edu.colorado.plv.bounder.symbolicexecutor

import java.time.Instant
import com.microsoft.z3.Z3Exception
import edu.colorado.plv.bounder.{BounderUtil, RunConfig}
import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, IRWrapper, If, InternalMethodInvoke, InternalMethodReturn, InvokeCmd, Loc, NopCmd, ReturnCmd, SkippedInternalMethodInvoke, SkippedInternalMethodReturn, SwitchCmd, ThrowCmd, VirtualInvoke}
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.solver.Z3StateSolver
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, DBOutputMode, FrameworkLocation, IPathNode, InitialQuery, Live, MemoryOutputMode, OrdCount, OutputMode, PathNode, Qry, State, SubsumableLocation, SwapLoc, WitnessedQry}

import scala.annotation.tailrec
import upickle.default._

import scala.collection.mutable

sealed trait CallGraphSource
case object CHACallGraph extends CallGraphSource
case object SparkCallGraph extends CallGraphSource
case object AppOnlyCallGraph extends CallGraphSource

sealed trait SubsumptionMode

/**
 * Encode each possible subsuming state one at a time
 */
case object SubsumptionModeIndividual extends SubsumptionMode

/**
 * Encode all possibly subsuming states at once
 */
case object SubsumptionModeBatch extends SubsumptionMode

/**
 * Run both batch and individual comparing results
 */
case object SubsumptionModeTest extends SubsumptionMode

/**
 * //TODO: ugly lambda due to wanting to configure transfer functions externally but still need cha
 * @param stepLimit Number of back steps to take from assertion before timeout (-1 for no limit)
 * @param w  IR representation defined by IRWrapper interface
 * @param specSpace CFTL specifications
 * @param printProgress print steps taken
 * @param z3Timeout seconds that z3 can take on a query before timeout
 * @param component restrict analysis to callbacks that match the listed regular expressions
 * @tparam M Method type (IR wrapper)
 * @tparam C Command type (IR wrapper)
 */
case class SymbolicExecutorConfig[M,C](stepLimit: Int,
                                       w :  IRWrapper[M,C],
                                       specSpace:SpecSpace,
                                       printProgress : Boolean = sys.env.getOrElse("DEBUG","false").toBoolean,
                                       z3Timeout : Option[Int] = None,
                                       component : Option[Seq[String]] = None,
                                       outputMode : OutputMode = MemoryOutputMode,
//                                       timeLimit : Int = 7200,
                                      timeLimit:Int = 1800, // Note: connectbot click finish does not seem to go any further with 2h vs 0.5hr
                                       subsumptionMode:SubsumptionMode = SubsumptionModeIndividual //Note: seems to be faster without batch mode subsumption
                                      ){
  def getSymbolicExecutor =
    new AbstractInterpreter[M, C](this)
}

class LexicalStackThenTopo[M,C](w:IRWrapper[M,C]) extends OrdCount{
  override def delta(current: Qry): Int = current.loc match {
    case _:CallbackMethodInvoke => 1
    case _:CallbackMethodReturn => 1
    case _ => 0
  }
  private def compareLocAtSameStack(l1:Loc, l2:Loc):Int = (l1,l2) match {
    case (AppLoc(m1,l1,isPre1), AppLoc(m2,l2,isPre2)) if m1 == m2 && l1 == l2 =>
      if(isPre1 == isPre2) {
        //            println(s"no ord:   p1: ${p1.qry.loc} p2: ${p2.qry.loc}")
        0
      }
      else if(isPre1)
        -1 // p2 is post line and should go first
      else {
        1 // p1 is post line and should go first
      }
    case (a1@AppLoc(m1,_,_), a2@AppLoc(m2,_,_)) if m1 == m2 =>
      val c1 = w.commandTopologicalOrder(w.cmdAtLocation(a1))
      val c2 = w.commandTopologicalOrder(w.cmdAtLocation(a2))
      c1 - c2 // reversed because topological order increases from beginning of function
    case (entry, AppLoc(_, _, _)) if entry.isEntry.contains(true) => -1
    case (AppLoc(_,_,_), entry) if entry.isEntry.contains(true) => 1
    case (exit, AppLoc(_,_,_)) if exit.isEntry.contains(false) => 1
    case (AppLoc(_,_,_), exit) if exit.isEntry.contains(false) => -1
    case (entry, exit) if exit.isEntry.contains(false) && entry.isEntry.contains(true) => -1
    case (exit, entry) if exit.isEntry.contains(false) && entry.isEntry.contains(true) => 1
    case (msg1,msg2) if msg1 == msg2 => 0
    case (msg1, msg2) if msg1.isEntry.isDefined && msg2.isEntry.isDefined =>
      if(msg1.toString < msg2.toString) 1 else -1
    case (AppLoc(m1,_,_), AppLoc(m2,_,_)) => if(m1.toString < m2.toString) 1 else -1
    case (v1,v2) =>
      println(v1)
      println(v2)
      ???
  }
  // return positive if p1 should be first
  // return negative if p2 should be first
  override def compare(p1: IPathNode, p2: IPathNode): Int = {
    if(p1.ordDepth != p2.ordDepth){
      // Prefer smaller number of callbacks
      return p2.ordDepth - p1.ordDepth
    }

    // comparing things from the base of the stack up, reversing for convenience
    val stack1 = ((None,Some(p1.qry.loc)):: p1.state.callStack.map(sf => (Some(sf.exitLoc),sf.retLoc))).reverse
    val stack2 = ((None,Some(p2.qry.loc)):: p2.state.callStack.map(sf => (Some(sf.exitLoc),sf.retLoc))).reverse

    @tailrec
    def iCompare(s1: List[(Option[Loc], Option[Loc])], s2:List[(Option[Loc], Option[Loc])]):Int = (s1,s2) match{
      case (Nil,Nil) =>
        p2.depth - p1.depth
      case (h1::t1, h2::t2) if h1 == h2 => iCompare(t1,t2)
      case (h1::t1, h2::t2) if h1._2.isDefined && h2._2.isDefined=>
        val res = compareLocAtSameStack(h1._2.get, h2._2.get)
        if(res == 0)
          iCompare(t1,t2)
        else res
      case (Nil,_) => -1
      case (_,Nil) => 1
      case (h1::t1, h2::t2) if h1._1 != h2._1 =>
        if(h1._1.toString < h2._1.toString) 1 else -1
    }
    iCompare(stack1,stack2)
  }
}
sealed trait QueryResult
case object QueryFinished extends QueryResult
case class QueryInterrupted(reason:String) extends QueryResult

case class QueryInterruptedException(terminals:Set[IPathNode], reason:String) extends Exception
class AbstractInterpreter[M,C](config: SymbolicExecutorConfig[M,C]) {

  implicit val pathMode: OutputMode = config.outputMode
  implicit val w = config.w
  implicit val ord = new LexicalStackThenTopo[M,C](w)
  private val cha = w.getClassHierarchyConstraints

  private val invarMap = mutable.HashMap[SubsumableLocation, Set[IPathNode]]()



  def getClassHierarchy = cha
  val transfer = new TransferFunctions[M, C](w, config.specSpace, cha)

  val appCodeResolver = new DefaultAppCodeResolver[M,C](config.w)
  def getAppCodeResolver = appCodeResolver
  val controlFlowResolver =
    new ControlFlowResolver[M,C](config.w,appCodeResolver, cha, config.component.map(_.toList), config)
  def writeIR():Unit = {
    val callbacks = appCodeResolver.getCallbacks
    config.outputMode match {
      case db:DBOutputMode =>
        appCodeResolver.appMethods.foreach{m =>
          db.writeMethod(m,callbacks.contains(m))
          val directCalls = controlFlowResolver.directCallsGraph(m).map{
            case InternalMethodReturn(clazz,name,m) => (name,clazz,false)
            case CallinMethodReturn(sig) => (sig.methodSignature,sig.base,true)
            case _ => throw new IllegalStateException()
          }
          directCalls.foreach{callee => db.writeCallEdge(m.simpleName,m.classType, callee._1,callee._2,callee._3)}
        }
      case _ =>
    }
  }
  // Dump debug info from soot analysis to sqlite
//  writeIR() //TODO: add debug flag to toggle this

  def getControlFlowResolver: ControlFlowResolver[M, C] = controlFlowResolver
  lazy val stateSolver = new Z3StateSolver(cha)


  case class QueryData(queryId:Int, location:Loc, terminals: Set[IPathNode], runTime:Long, result : QueryResult)

  /**
   *
   * @return  (id, Terminal path nodes)
   */
  def run(initialQuery: InitialQuery, outputMode:OutputMode = MemoryOutputMode,
          cfg:RunConfig = RunConfig()) : Set[QueryData] = {
    val qry = initialQuery.make(this)
    qry.groupBy(_.loc).map{ case(loc,qs) =>
      val startTime = Instant.now.getEpochSecond
      var id = -1
      try {
        val pathNodes = qs.map(PathNode(_, Nil, None))
        id = outputMode.initializeQuery(loc,cfg,initialQuery)
        val queue = new GrouperQ
        queue.addAll(pathNodes)
        val deadline = if(config.timeLimit > -1) Instant.now.getEpochSecond + config.timeLimit else -1
        invarMap.clear()
        val res: Set[IPathNode] = executeBackward(queue, config.stepLimit, deadline)

        val interpretedRes = BounderUtil.interpretResult(res, QueryFinished)
        val char = BounderUtil.characterizeMaxPath(res)
        val endTime: Long = Instant.now.getEpochSecond - startTime
        outputMode.writeLiveAtEnd(res, id, interpretedRes.toString,interpretedRes,char,endTime)
        QueryData(id, loc, res,
          endTime, QueryFinished)
      }catch{
        case QueryInterruptedException(terminals, reason) =>
          QueryData(id, loc, terminals, Instant.now.getEpochSecond - startTime, QueryInterrupted(reason))
        case t:Throwable =>
          // print stack trace to stderr and continue
          t.printStackTrace(System.err)
          QueryData(id, loc, Set(), Instant.now.getEpochSecond - startTime, QueryInterrupted(t.getClass.toString))
      }
    }.toSet
  }

  def isSubsumed(pathNode:IPathNode, checkTimeout: ()=>Unit):Set[IPathNode] = pathNode match{
    case SwapLoc(loc) if pathNode.qry.isInstanceOf[Qry] && invarMap.contains(loc) => {
      val nodes:Set[IPathNode] = invarMap(loc)
      val states = nodes.map(_.state)
      val res = config.subsumptionMode match {
        case SubsumptionModeIndividual =>
          nodes.find(p => {
            checkTimeout()
            stateSolver.canSubsume(p.state,pathNode.state, transfer.getSpec)
          }).toSet
        case SubsumptionModeBatch =>
          if(stateSolver.canSubsumeSet(states, pathNode.state, transfer.getSpec)) nodes else Set[IPathNode]()
        case SubsumptionModeTest =>{
          val singleResult = nodes.find(p => stateSolver.canSubsume(p.state,pathNode.state, transfer.getSpec)).toSet
          val batchResult = stateSolver.canSubsumeSet(states, pathNode.state, transfer.getSpec)
          if(singleResult.nonEmpty != batchResult){
            println(s"current state:\n    ${pathNode.state}")
            println("subsuming states:")
            states.foreach(s => println(s"    ${s.toString}"))
            val batchResult2 = stateSolver.canSubsumeSet(states, pathNode.state, transfer.getSpec)
            println()
          }
          singleResult
        }
      }
      res
    }
    case _ => Set.empty
  }

  private def equivStates(s1:State, s2:State):Boolean = {
//    stateSolver.canSubsume(s1,s2) && stateSolver.canSubsume(s1,s2)
    s1.callStack == s2.callStack &&
      s1.heapConstraints == s2.heapConstraints &&
      s1.pureFormula == s2.pureFormula &&
      s1.traceAbstraction == s2.traceAbstraction
  }
  sealed trait GroupType
  case class IfGroup(loc:AppLoc) extends GroupType
  case class InvokeGroup(loc:Option[Loc]) extends GroupType

  private def nodeGroup(pn:IPathNode):Option[(GroupType, List[(Loc, Option[Loc])], Int)] = {
    val stack = pn.state.callStack
    val groupStack = stack.map(sf => (sf.exitLoc, sf.retLoc))
    lazy val retLoc = InvokeGroup(stack.head.retLoc)
    pn.qry.loc match {
      case l@AppLoc(_,_,false) =>
        val cmd = w.cmdAtLocation(l)
        cmd match{
          case If(_,_,_) => Some((IfGroup(l),groupStack,pn.ordDepth))
          case _ => None
        }
      case _:InternalMethodInvoke =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case _:CallinMethodInvoke =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case _:GroupedCallinMethodInvoke =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case _:SkippedInternalMethodInvoke =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case _ => None
    }
  }
  class GrouperQ {
    val qrySet = new mutable.PriorityQueue[IPathNode]()
    val groupedQrySet = new mutable.PriorityQueue[IPathNode]()
    def isEmpty:Boolean = qrySet.isEmpty && groupedQrySet.isEmpty
    def size():Int = qrySet.size + groupedQrySet.size
    def toSet:Set[IPathNode] = qrySet.toSet ++ groupedQrySet.toSet
    def addAll(pathNodes:Set[IPathNode]):Unit =
      qrySet.addAll(pathNodes)
    private def group(qryList: List[IPathNode]): List[IPathNode] = {
      // Group states by next command to process, stack (excluding locals), and trace length
      val groups: Map[Option[(GroupType, List[(Loc, Option[Loc])], Int)], List[IPathNode]] = qryList.groupBy(nodeGroup)
      groups.flatMap {
        case (None, v) => v
        case (Some(group), v) =>
          val nodeSet = v.toSet
          val groupedNodes: Set[IPathNode] = nodeSet.foldLeft(Set[IPathNode]()) { case (acc, pathNode) =>
            acc.find(otherPathNode => equivStates(otherPathNode.qry.state, pathNode.qry.state)) match {
              case Some(other) =>
                (acc - other) + other.mergeEquiv(pathNode)
              case None => acc + pathNode
            }
          }
          val groupedWithAlt: Set[IPathNode] = groupedNodes.map { n =>
            val otherNodes = nodeSet - n
            otherNodes.foldLeft(n) { case (acc, v) => acc.addAlternate(v) }
          }
          groupedWithAlt
      }.toList
    }
    def nextWithGrouping():IPathNode = {
      if(groupedQrySet.nonEmpty){
        groupedQrySet.dequeue()
      }else {
        val next = qrySet.dequeue()
        val currentGroup = nodeGroup(next)
        if (currentGroup.isDefined) {
          val toGroup = mutable.ListBuffer[IPathNode]()
          toGroup += next
          while (qrySet.nonEmpty && nodeGroup(qrySet.head) == currentGroup) {
            toGroup += qrySet.dequeue()
          }
          val grouped = group(toGroup.toList)
          groupedQrySet.addAll(grouped)
          groupedQrySet.dequeue()
        } else {
          next
        }
      }
    }
  }


  def checkDeadline(deadline:Long, qrySet:GrouperQ, refutedSubsumedOrWitnessed: Set[IPathNode]):Unit = {
    if(deadline > -1 && Instant.now.getEpochSecond > deadline){
      throw QueryInterruptedException(qrySet.toSet ++ refutedSubsumedOrWitnessed, "timeout")
    }
  }
  /**
   *
   * @param qrySet Work list of locations and states to process
   * @param limit Step limit to terminate at (set to -1 for no limit)
   * @param deadline unix time to terminate if verification not complete (-1 for no limit)
   * @param refutedSubsumedOrWitnessed Terminal nodes
   * @param visited Map of visited states StackSize -> Location -> Set[State]
   * @return
   */
  @tailrec
  final def executeBackward(qrySet: GrouperQ, limit:Int, deadline:Long,
                            refutedSubsumedOrWitnessed: Set[IPathNode] = Set()):Set[IPathNode] = {
    checkDeadline(deadline,qrySet, refutedSubsumedOrWitnessed)
    if(qrySet.isEmpty){
      return refutedSubsumedOrWitnessed
    }

    val current = qrySet.nextWithGrouping()

    if(config.printProgress) {
      current match {
        case SwapLoc(FrameworkLocation) =>
          println("Framework location query")
          println(s"    State: ${current.qry.state}")
          println(s"    Loc  : ${current.qry.loc}")
          println(s"    depth: ${current.depth}")
          println(s"    size of worklist: ${qrySet.size}")
          println(s"    ord depth: ${current.ordDepth}")
        case _ =>
      }
    }
    current match {
      case p@PathNode(Qry(_,_,Live), true) =>
        // current node is subsumed
        // TODO: this branch is probably unreachable
        executeBackward(qrySet, limit, deadline, refutedSubsumedOrWitnessed + p)
      case p@PathNode(Qry(_,_,BottomQry), _) =>
        // current node is refuted
        executeBackward(qrySet, limit, deadline, refutedSubsumedOrWitnessed + p)
      case p@PathNode(Qry(_,_,WitnessedQry(_)), _) =>
        // current node is witnessed
        refutedSubsumedOrWitnessed.union(qrySet.toSet) + p
      case p: IPathNode if limit > 0 && p.depth > limit =>
        // max steps reached
        refutedSubsumedOrWitnessed.union(qrySet.toSet) + p
      case p@PathNode(qry@Qry(_,_,Live), false) =>
        // live path node
        val subsuming = //try{
            isSubsumed(p, ()=> checkDeadline(deadline, qrySet,refutedSubsumedOrWitnessed))
//            }catch {
//              case ze:Throwable =>
//                // Get sequence trace to error when it occurs
//                current.setError(ze)
//                ze.printStackTrace()
//                throw QueryInterruptedException(refutedSubsumedOrWitnessed + current, ze.getMessage)
//          }
        subsuming match {
          case v if v.nonEmpty =>
            // Path node discovered to be subsumed
            executeBackward(qrySet, limit, deadline, refutedSubsumedOrWitnessed + p.setSubsumed(v))
          case v if v.isEmpty =>
            // Add to invariant map if invariant location is tracked
            current match {
              case SwapLoc(v) => {
                val nodeSetAtLoc = invarMap.getOrElse(v, Set.empty)
                invarMap.addOne(v-> (nodeSetAtLoc + current))
              }
              case _ =>
            }
            val nextQry = try{
              executeStep(qry).map(q => PathNode(q, List(p), None))
            }catch{
              case ze:Throwable =>
                // Get sequence trace to error when it occurs
                current.setError(ze)
                ze.printStackTrace()
                throw QueryInterruptedException(refutedSubsumedOrWitnessed + current, ze.getMessage)
            }
            qrySet.addAll(nextQry)
            executeBackward(qrySet, limit, deadline, refutedSubsumedOrWitnessed)
        }
    }
  }

  /**
   * Call methods to choose where to go with symbolic execution and apply transfer functions
   * @param qry location and state combination
   * @return
   */
  def executeStep(qry:Qry):Set[Qry] = qry match{
    case Qry(state, loc, Live) =>
      val predecessorLocations = controlFlowResolver.resolvePredicessors(loc,state)
      //predecessorLocations.par.flatMap(l => {
      predecessorLocations.flatMap(l => {
        val newStates = transfer.transfer(state,l,loc)
        newStates.map(state => stateSolver.simplify(state, transfer.getSpec) match {
          case Some(state) if stateSolver.witnessed(state, transfer.getSpec).isDefined =>
            Qry(state, l, WitnessedQry(stateSolver.witnessed(state, transfer.getSpec)))
          case Some(state) => Qry(state, l, Live)
          case None =>
            Qry(state,l, BottomQry)
        })
      }).toSet
    case Qry(_,_, BottomQry) => Set()
    case Qry(_,_,WitnessedQry(_)) =>
      //TODO: this was "Set()". Is there a reason we may want to step here?
      throw new IllegalStateException("Useless to take abstract step on witnessed query")
  }
}
