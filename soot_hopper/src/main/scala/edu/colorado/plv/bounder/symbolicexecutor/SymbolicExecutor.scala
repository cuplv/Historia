package edu.colorado.plv.bounder.symbolicexecutor

import java.time.Instant

import edu.colorado.plv.bounder.{BounderUtil, RunConfig}
import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, IRWrapper, If, InternalMethodInvoke, InternalMethodReturn, InvokeCmd, Loc, NopCmd, ReturnCmd, SkippedInternalMethodInvoke, SkippedInternalMethodReturn, SwitchCmd, ThrowCmd, VirtualInvoke}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, SetInclusionTypeSolving, SolverTypeSolving, StateTypeSolving, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, DBOutputMode, DBPathNode, FrameworkLocation, IPathNode, InitialQuery, LiveQry, LiveTruncatedQry, MemoryOutputMode, OrdCount, OutputMode, PathNode, Qry, State, StateSet, SubsumableLocation, SwapLoc, WitnessedQry}

import scala.annotation.tailrec
import scala.collection.parallel.CollectionConverters.{ImmutableSetIsParallelizable, IterableIsParallelizable}
import upickle.default._

import collection.mutable.PriorityQueue
import scala.collection.mutable

sealed trait CallGraphSource
case object FlowdroidCallGraph extends CallGraphSource
case object PatchedFlowdroidCallGraph extends CallGraphSource
case object CHACallGraph extends CallGraphSource
case object SparkCallGraph extends CallGraphSource
case object AppOnlyCallGraph extends CallGraphSource

/**
 * //TODO: ugly lambda due to wanting to configure transfer functions externally but still need cha
 * @param stepLimit Number of back steps to take from assertion before timeout (-1 for no limit)
 * @param w  IR representation defined by IRWrapper interface
 * @param transfer transfer functions over app transitions including callin/callback boundaries
 * @param printProgress print steps taken
 * @param z3Timeout seconds that z3 can take on a query before timeout
 * @param component restrict analysis to callbacks that match the listed regular expressions
 * @tparam M
 * @tparam C
 */
case class SymbolicExecutorConfig[M,C](stepLimit: Int,
                                       w :  IRWrapper[M,C],
                                       transfer : ClassHierarchyConstraints => TransferFunctions[M,C],
                                       printProgress : Boolean = sys.env.getOrElse("DEBUG","false").toBoolean,
                                       z3Timeout : Option[Int] = None,
                                       component : Option[Seq[String]] = None,
//                                       stateTypeSolving: StateTypeSolving = SetInclusionTypeSolving,
//                                       stateTypeSolving: StateTypeSolving = SolverTypeSolving,
                                       outputMode : OutputMode = MemoryOutputMode,
                                       timeLimit : Int = 6000,
                                       subsumptionEnabled:Boolean = true // Won't prove anything without subsumption but can find witnesses
                                      ){
  def getSymbolicExecutor =
    new SymbolicExecutor[M, C](this)}
sealed trait QueryResult
case object QueryFinished extends QueryResult
case class QueryInterrupted(reason:String) extends QueryResult

case class QueryInterruptedException(terminals:Set[IPathNode], reason:String) extends Exception
class SymbolicExecutor[M,C](config: SymbolicExecutorConfig[M,C]) {

  implicit val pathMode: OutputMode = config.outputMode
  implicit val w = config.w
  private val cha = w.getClassHierarchyConstraints



  def getClassHierarchy = cha
  val transfer = config.transfer(cha)

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
            case CallinMethodReturn(clazz,name) => (name,clazz,true)
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
  val stateSolver = new Z3StateSolver(cha)

  implicit object LexicalStackThenTopo extends OrdCount{
    override def delta(current: Qry): Int = current.loc match {
      case CallbackMethodInvoke(_, _, _) => 1
      case CallbackMethodReturn(_, _, _, _) => 1
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
      val stack1 = ((None,Some(p1.qry.loc)):: p1.qry.getState.get.callStack.map(sf => (Some(sf.exitLoc),sf.retLoc))).reverse
      val stack2 = ((None,Some(p2.qry.loc)):: p2.qry.getState.get.callStack.map(sf => (Some(sf.exitLoc),sf.retLoc))).reverse

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
        val deadline = if(config.timeLimit > -1)startTime + config.timeLimit else -1
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


  def isSubsumed(pathNode:IPathNode,
                 nVisited: Map[SubsumableLocation,Map[Int,StateSet]]):Option[IPathNode] = pathNode match{
    case SwapLoc(loc) if pathNode.qry.isInstanceOf[LiveQry] && nVisited.contains(loc) =>
      val root = nVisited(loc).getOrElse(pathNode.qry.getState.get.callStack.size, StateSet.init)
      val res = StateSet.findSubsuming(pathNode, root,(s1,s2) =>{
        if(config.subsumptionEnabled) {
          stateSolver.canSubsume(s1,s2)
        } else if(s1.sf.traceAbstraction.size == s2.sf.traceAbstraction.size &&
          s1.heapConstraints.size == s2.heapConstraints.size) {
          stateSolver.canSubsume(s1,s2) && stateSolver.canSubsume(s2,s1)
        } else
          false
      })

      //=== test code ===
      // Note this was to test if state set is working correctly, it appears to be
      //val allState = root.allStates
      //val resOld = allState.find(old => stateSolver.canSubsume(old.qry.state,pathNode.qry.state))

      //if(resOld.isDefined != res.isDefined){
      //  println("diff")
      //}
      // === end test code ==

      res
    case _ => None
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
    val stack = pn.qry.getState.get.callStack
    val groupStack = stack.map(sf => (sf.exitLoc, sf.retLoc))
    lazy val retLoc = InvokeGroup(stack.head.retLoc)
    pn.qry.loc match {
      case l@AppLoc(_,_,false) =>
        val cmd = w.cmdAtLocation(l)
        cmd match{
          case If(_,_,_) => Some((IfGroup(l),groupStack,pn.ordDepth))
          case _ => None
        }
      case InternalMethodInvoke(_, _, _) =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case CallinMethodInvoke(_, _) =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case GroupedCallinMethodInvoke(_, _) =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case SkippedInternalMethodInvoke(_, _, _) =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case _ => None
    }
  }
  class GrouperQ {
    val qrySet = new mutable.PriorityQueue[IPathNode]()(LexicalStackThenTopo)
    val groupedQrySet = new mutable.PriorityQueue[IPathNode]()(LexicalStackThenTopo)
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
            acc.find(otherPathNode => equivStates(otherPathNode.qry.getState.get, pathNode.qry.getState.get)) match {
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
                            refutedSubsumedOrWitnessed: Set[IPathNode] = Set(),
                            visited:Map[SubsumableLocation, Map[Int,StateSet]] = Map()):Set[IPathNode] = {

    if(deadline > -1 && Instant.now.getEpochSecond > deadline){
      throw QueryInterruptedException(qrySet.toSet ++ refutedSubsumedOrWitnessed, "timeout")
    }
    if(qrySet.isEmpty){
      return refutedSubsumedOrWitnessed
    }

    val current = qrySet.nextWithGrouping()

    current match{
      case SwapLoc(FrameworkLocation) =>
        println("Framework location query")
        println(s"    State: ${current.qry.getState}")
        println(s"    Loc  : ${current.qry.loc}")
        println(s"    depth: ${current.depth}")
        println(s"    size of worklist: ${qrySet.size}")
        println(s"    ord depth: ${current.ordDepth}")
      case _ =>
    }

    current match {
      case p@PathNode(_:LiveQry, true) =>
        // current node is subsumed
        // TODO: this branch is probably unreachable
        executeBackward(qrySet, limit,deadline, refutedSubsumedOrWitnessed + p, visited)
      case p@PathNode(_:BottomQry,_) =>
        // current node is refuted
        executeBackward(qrySet, limit, deadline, refutedSubsumedOrWitnessed + p, visited)
      case p@PathNode(_:WitnessedQry,_) =>
        // current node is witnessed
        refutedSubsumedOrWitnessed.union(qrySet.toSet) + p
      case p:IPathNode if limit > 0 && p.depth > limit =>
        // max steps reached
        refutedSubsumedOrWitnessed.union(qrySet.toSet)
      case p@PathNode(qry:LiveQry,false) =>
        // live path node
        isSubsumed(p, visited) match{
          case v@Some(_) =>
            // Path node discovered to be subsumed
            executeBackward(qrySet, limit,deadline, refutedSubsumedOrWitnessed + p.setSubsumed(v), visited)
          case None =>
            val stackSize = p.qry.getState.get.callStack.size
            // Add to invariant map if invariant location is tracked
            val newVisited = current match{
              case SwapLoc(v) =>
                val stackSizeToNode: Map[Int, StateSet] = visited.getOrElse(v,Map[Int,StateSet]())
                val nodeSetAtLoc: StateSet = stackSizeToNode.getOrElse(stackSize, StateSet.init)
                val nodeSet = StateSet.add(p, nodeSetAtLoc)
                val newStackSizeToNode = stackSizeToNode + (stackSize -> nodeSet)
                visited + (v -> newStackSizeToNode)
              case _ => visited
            }
            val nextQry = executeStep(qry).map(q => PathNode(q, List(p), None))
            qrySet.addAll(nextQry)
            executeBackward(qrySet, limit,deadline, refutedSubsumedOrWitnessed, newVisited)
        }
    }
  }

  /**
   * Call methods to choose where to go with symbolic execution and apply transfer functions
   * @param qry location and state combination
   * @return
   */
  def executeStep(qry:Qry):Set[Qry] = qry match{
    case LiveQry(state, loc) =>
      val predecessorLocations = controlFlowResolver.resolvePredicessors(loc,state)
      //predecessorLocations.par.flatMap(l => {
      predecessorLocations.flatMap(l => {
        val newStates = transfer.transfer(state,l,loc)
        newStates.map(state => stateSolver.simplify(state) match {
          case Some(state) if stateSolver.witnessed(state) =>
            WitnessedQry(state, l)
          case Some(state) => LiveQry(state, l)
          case None =>
            BottomQry(state,l)
        })
      }).seq.toSet
    case BottomQry(_,_) => Set()
    case WitnessedQry(_,_) => Set()
    case LiveTruncatedQry(loc) => throw new IllegalStateException("Cannot execute step on truncated query")
  }
}
