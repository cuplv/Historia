package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, IRWrapper, If, InternalMethodInvoke, InternalMethodReturn, InvokeCmd, Loc, NopCmd, ReturnCmd, SkippedInternalMethodInvoke, SkippedInternalMethodReturn, SwitchCmd, ThrowCmd, VirtualInvoke}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, SetInclusionTypeSolving, SolverTypeSolving, StateTypeSolving, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, DBOutputMode, DBPathNode, FrameworkLocation, IPathNode, MemoryOutputMode, OrdCount, OutputMode, PathNode, Qry, SomeQry, State, StateSet, SubsumableLocation, SwapLoc, WitnessedQry}

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
 * @param stepLimit Number of back steps to take from assertion before timeout
 * @param w  IR representation defined by IRWrapper interface
 * @param transfer transfer functions over app transitions including callin/callback boundaries
 * @param printProgress print steps taken
 * @param z3Timeout seconds that z3 can take on a query before timeout
 * @param component restrict analysis to callbacks that match the listed regular expressions
 * @tparam M
 * @tparam C
 */
case class SymbolicExecutorConfig[M,C](stepLimit: Option[Int],
                                       w :  IRWrapper[M,C],
                                       transfer : ClassHierarchyConstraints => TransferFunctions[M,C],
                                       printProgress : Boolean = sys.env.getOrElse("DEBUG","false").toBoolean,
                                       z3Timeout : Option[Int] = None,
                                       component : Option[Seq[String]] = None,
//                                       stateTypeSolving: StateTypeSolving = SetInclusionTypeSolving,
                                       stateTypeSolving: StateTypeSolving = SolverTypeSolving,
                                       outputMode : OutputMode = MemoryOutputMode
                                      ){
  def getSymbolicExecutor =
    new SymbolicExecutor[M, C](this)}
class SymbolicExecutor[M,C](config: SymbolicExecutorConfig[M,C]) {

  implicit var pathMode = config.outputMode
  implicit var w = config.w

  val cha =
    new ClassHierarchyConstraints(config.w.getClassHierarchy,config.w.getInterfaces, config.stateTypeSolving)

  def getClassHierarchy = cha
  val transfer = config.transfer(cha)

  val appCodeResolver = new DefaultAppCodeResolver[M,C](config.w)
  def getAppCodeResolver = appCodeResolver
  val controlFlowResolver =
    new ControlFlowResolver[M,C](config.w,appCodeResolver, cha, config.component.map(_.toList))
  def writeIR():Unit = {
    val callbacks = appCodeResolver.getCallbacks
    config.outputMode match {
      case db@DBOutputMode(_) =>
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
  writeIR()

  def getControlFlowResolver = controlFlowResolver
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
      case (entry, AppLoc(_, _, _)) if entry.isEntry == Some(true) => -1
      case (AppLoc(_,_,_), entry) if entry.isEntry == Some(true) => 1
      case (exit, AppLoc(_,_,_)) if exit.isEntry == Some(false) => 1
      case (AppLoc(_,_,_), exit) if exit.isEntry == Some(false) => -1
      case (entry, exit) if exit.isEntry == Some(false) && entry.isEntry == Some(true) => -1
      case (exit, entry) if exit.isEntry == Some(false) && entry.isEntry == Some(true) => 1
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
      val stack1 = ((None,Some(p1.qry.loc)):: p1.qry.state.callStack.map(sf => (Some(sf.methodLoc),sf.retLoc))).reverse
      val stack2 = ((None,Some(p2.qry.loc)):: p2.qry.state.callStack.map(sf => (Some(sf.methodLoc),sf.retLoc))).reverse

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
//          p2.depth - p1.depth
          if(h1._1.toString < h2._1.toString) 1 else -1
        case (v1,v2) =>
          println(v1)
          println(v2)
          ??? //TODO: any missed cases possible?
      }
      iCompare(stack1,stack2)

//      (p1.qry.loc, p2.qry.loc) match{
//        case (_,_) if p2.ordDepth != p1.ordDepth =>
//          // process shorter traces first
//          p2.ordDepth - p1.ordDepth
//        case (_:AppLoc, exitMsg) if exitMsg.isEntry == Some(false) => //&& stack1 == stack2.tail =>
//          1
//        case (exitMsg, _:AppLoc) if exitMsg.isEntry == Some(false) => //&& stack1.tail == stack2  =>
//          -1
//
//        case (a1@AppLoc(m1,_,_), a2@AppLoc(m2,_,_)) if m1 == m2 =>
//          val c1 = w.commandTopologicalOrder(w.cmdAtLocation(a1))
//          val c2 = w.commandTopologicalOrder(w.cmdAtLocation(a2))
//          c1 - c2 // reversed because topological order increases from beginning of function
//        case (CallbackMethodReturn(fmwClazz, fmwName, loc, _), AppLoc(mloc, lineloc, _)) if mloc == loc =>
//          // Callback return should be processed before commands in callback
//          1
//        case (AppLoc(mloc, lineloc, _), CallbackMethodReturn(fmwClazz, fmwName, loc, _)) if mloc == loc =>
//          -1
//        case (a1:AppLoc, i2:InternalMethodReturn) if stack1 == stack2 =>
//          // if at the same stack level, internal method return should be processed before app commands
//          -1
//        case (_:InternalMethodReturn, _:AppLoc) if stack1 == stack2 =>
//          1
//        case (_:AppLoc, _) if stack1 == stack2 =>
//          1 //Always prefer appLoc
//        case (_, _:AppLoc) if stack1 == stack2 =>
//          -1
//        case (l1,l2) if stack1.nonEmpty && stack2.nonEmpty && stack1.tail == stack2.tail =>
//          (l1.isEntry,l2.isEntry) match{
//            case (v1,v2) if v1 == v2 => p2.depth - p1.depth
//            case (Some(true),_) => -1
//            case (_,Some(true)) => 1
//            case (Some(false),_) => 1
//            case (_, Some(false)) => -1
//          }
//        case _ =>
//          p2.depth - p1.depth
//      }
    }
  }
//  implicit object PVCountOrdering extends OrdCount{
//    override def delta(current: Qry): Int = 0
//
//    override def compare(x: IPathNode, y: IPathNode): Int = y.qry.state.pureVars.size - x.qry.state.pureVars.size
//  }
//  implicit object CallbackCountOrdering extends OrdCount{
//    def compare(a:IPathNode, b:IPathNode) = b.ordDepth - a.ordDepth
//
//    override def delta(current: Qry): Int = current.loc match {
//      case CallbackMethodInvoke(_, _, _) => 1
//      case CallbackMethodReturn(_, _, _, _) => 1
//      case _ => 0
//    }
//  }
//  implicit object DepthOrdering extends OrdCount{
//    def compare(a:IPathNode, b:IPathNode) = b.depth - a.depth
//    override def delta(current:Qry):Int = 1
//  }
  /**
   *
   * @param qry - a source location and an assertion to prove
   * @return None if the assertion at that location is unreachable, Some(Trace) if it is reachable.
   *         Trace will contain a tree of backward executions for triage.
   */
  def run(qry: Set[Qry], initialize: Set[IPathNode] => Unit = _ => ()) : Set[IPathNode] = {
    val pathNodes = qry.map(PathNode(_,Nil,None))
    initialize(pathNodes)
    val queue = new PriorityQueue[IPathNode]()(LexicalStackThenTopo)
    queue.addAll(pathNodes)
    config.stepLimit match{
      case Some(limit) => executeBackward(queue, limit)
      case None =>
        ???
    }
  }


  def isSubsumed(pathNode:IPathNode,
                 nVisited: Map[SubsumableLocation,Map[Int,StateSet]]):Option[IPathNode] = pathNode.qry match{
    case SomeQry(_,SwapLoc(loc)) if nVisited.contains(loc) =>
      val root = nVisited(loc).getOrElse(pathNode.qry.state.callStack.size, StateSet.init)
      val res = StateSet.findSubsuming(pathNode, root,(s1,s2) => stateSolver.canSubsume(s1,s2))

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

  private def groupAndTransferPostIfCmd(qrySet: mutable.PriorityQueue[IPathNode]):mutable.PriorityQueue[IPathNode] = {
    val qrySet2  = qrySet.clone
    sealed trait GroupType
    case class IfGroup(loc:AppLoc) extends GroupType
    case class InvokeGroup(loc:Option[Loc]) extends GroupType
    // Group states by next command to process, stack (excluding locals), and trace length
    val groups = qrySet2.toList.groupBy{ pn =>
      val stack = pn.qry.state.callStack
      val groupStack = stack.map(sf => (sf.methodLoc, sf.retLoc))
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
    val newQ = new mutable.PriorityQueue[IPathNode]()(LexicalStackThenTopo)
    groups.foreach{
      case (None,v) => newQ.addAll(v)
      case (Some(group),v) =>
        val nodeSet = v.toSet
        val groupedNodes: Set[IPathNode] = nodeSet.foldLeft(Set[IPathNode]()){ case (acc,pathNode) =>
          acc.find(otherPathNode => equivStates(otherPathNode.qry.state,pathNode.qry.state)) match {
            case Some(other) =>
              (acc - other) + other.mergeEquiv(pathNode)
            case None => acc + pathNode
          }
        }
        val groupedWithAlt = groupedNodes.map{n =>
          val otherNodes = nodeSet - n
          otherNodes.foldLeft(n){case (acc,v) => acc.addAlternate(v)}
        }
        newQ.addAll(groupedWithAlt)
    }
    newQ
  }

  /**
   *
   * @param qrySet Work list of locations and states to process
   * @param limit Step limit to terminate at
   * @param refutedSubsumedOrWitnessed Terminal nodes
   * @param visited Map of visited states StackSize -> Location -> Set[State]
   * @return
   */
  @tailrec
  final def executeBackward(qrySet: PriorityQueue[IPathNode], limit:Int,
                            refutedSubsumedOrWitnessed: Set[IPathNode] = Set(),
                            visited:Map[SubsumableLocation,Map[Int,StateSet]] = Map()):Set[IPathNode] = {

    //TODO: This is way too sensitive to queue ordering, figure out something better
    val qrySetIG = groupAndTransferPostIfCmd(qrySet)
    if(qrySetIG.isEmpty){
      return refutedSubsumedOrWitnessed
    }

    val current = qrySetIG.dequeue()

//    println()
    val curTop = current.qry.loc match{
      case a:AppLoc => Some(w.commandTopologicalOrder(w.cmdAtLocation(a)))
      case _ => None
    }
    //TODO: uncomment dbg code
    val tmpPrint = current.ordDepth == 2 && List("39","40","39","44", "onPause").exists(v => current.qry.loc.toString.contains(v)) &&
      current.qry.state.callStack.exists(_.methodLoc.toString.contains("onPause"))
    if (true || tmpPrint) {
      val loc = current.qry.loc
      println(s"current loc: $loc ordDepth: ${current.ordDepth} topo: ${curTop}")
//      println(s"    ${current.qry.state}")
//      println(s"    subsLoc: ${SwapLoc(loc)}")
    }
//    println("--------------------")


    //TODO: uncomment:
//    current.qry.loc match{
//      case SwapLoc(FrameworkLocation) =>
//        println("Framework location query")
//        println(s"    State: ${current.qry.state}")
//        println(s"    Loc  : ${current.qry.loc}")
//        println(s"    depth: ${current.depth}")
//        println(s"    size of worklist: ${qrySetIG.size}")
//        println(s"    ord depth: ${current.ordDepth}")
//      case _ =>
//    }

    current match {
      case p@PathNode(_:SomeQry, true) =>
        if(tmpPrint) {
//          println(s"    ${p.qry.state}")
        }
        executeBackward(qrySetIG, limit, refutedSubsumedOrWitnessed + p, visited)
      case p@PathNode(_:BottomQry,_) =>
        if(tmpPrint) {
          println(s"     ${p.qry.state}")
          println("      refuted")
        }
        executeBackward(qrySetIG, limit, refutedSubsumedOrWitnessed + p, visited)
      case p@PathNode(_:WitnessedQry,_) =>
        if(tmpPrint) {
//          println(s"     ${p.qry.state}")
        }
        refutedSubsumedOrWitnessed.union(qrySetIG.toSet) + p
      case p:IPathNode if p.depth > limit =>
//        executeBackward(qrySetIG, limit, refutedSubsumedOrWitnessed + p, visited)
        refutedSubsumedOrWitnessed.union(qrySetIG.toSet)
      case p@PathNode(qry:SomeQry,false) =>
        isSubsumed(p, visited) match{
          case v@Some(_) =>
            if(tmpPrint) {
//              println(s"     ${p.qry.state}")
              println("    subsumed")
            }
            executeBackward(qrySetIG, limit, refutedSubsumedOrWitnessed + p.setSubsumed(v), visited)
          case None =>
            if(tmpPrint) {
//              println(s"     ${p.qry.state}")
            }
            val stackSize = p.qry.state.callStack.size
            val newVisited = SwapLoc(current.qry.loc) match{
              case Some(v) =>
                val stackSizeToNode: Map[Int, StateSet] = visited.getOrElse(v,Map[Int,StateSet]())
                val nodeSetAtLoc: StateSet = stackSizeToNode.getOrElse(stackSize, StateSet.init)
                val nodeSet = StateSet.add(p, nodeSetAtLoc)
                val newStackSizeToNode = stackSizeToNode + (stackSize -> nodeSet)
                visited + (v -> newStackSizeToNode)
              case None => visited
            }
            val nextQry = executeStep(qry).map(q => PathNode(q, List(p), None))
            val nextQrySet = qrySetIG.addAll(nextQry)
            executeBackward(nextQrySet, limit, refutedSubsumedOrWitnessed, newVisited)
        }
    }
  }

  /**
   * Call methods to choose where to go with symbolic execution and apply transfer functions
   * @param qry location and state combination
   * @return
   */
  def executeStep(qry:Qry):Set[Qry] = qry match{
    case SomeQry(state, loc) =>
      val predecessorLocations = controlFlowResolver.resolvePredicessors(loc,state)
      //TODO: add par back in?
      predecessorLocations.flatMap(l => {
        val newStates = transfer.transfer(state,l,loc)
        newStates.map(state => stateSolver.simplify(state) match {
          case Some(state) if stateSolver.witnessed(state) =>
            WitnessedQry(state, l)
          case Some(state) => SomeQry(state, l)
          case None =>
            BottomQry(state,l)
        })
      }).seq.toSet
    case BottomQry(_,_) => Set()
    case WitnessedQry(_,_) => Set()
  }
}
