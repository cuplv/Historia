package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, IRWrapper, If, InternalMethodInvoke, InternalMethodReturn, InvokeCmd, Loc, NopCmd, ReturnCmd, SkippedInternalMethodInvoke, SkippedInternalMethodReturn, SwitchCmd, ThrowCmd}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, SetInclusionTypeSolving, SolverTypeSolving, StateTypeSolving, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, DBOutputMode, FrameworkLocation, IPathNode, MemoryOutputMode, OrdCount, OutputMode, PathNode, Qry, SomeQry, StateSet, SubsumableLocation, SwapLoc, WitnessedQry}

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

  implicit object StackThenHeapOrder extends OrdCount{
    override def delta(current: Qry): Int = current.loc match {
      case CallbackMethodInvoke(_, _, _) => 1
      case CallbackMethodReturn(_, _, _, _) => 1
      case _ => 0
    }
    // return positive if p1 should be first
    // return negative if p2 should be first
    override def compare(p1: IPathNode, p2: IPathNode): Int = {
      val s1 = p1.qry.state
      val s2 = p2.qry.state
      if(s1.callStack.size != s2.callStack.size)
        return s1.callStack.size - s2.callStack.size //TODO: is this the correct order?

      val stack1 = p1.qry.state.callStack.map(sf => sf.methodLoc)
      val stack2 = p2.qry.state.callStack.map(sf => sf.methodLoc)
      (p1.qry.loc, p2.qry.loc) match{
        case (_,_) if p2.ordDepth != p1.ordDepth =>
          // process shorter traces first
          p2.ordDepth - p1.ordDepth
        case (AppLoc(m1,l1,isPre1), AppLoc(m2,l2,isPre2)) if m1 == m2 && l1 == l2  && stack1 == stack2 =>
          if(isPre1 == isPre2) {
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
        case (CallbackMethodReturn(fmwClazz, fmwName, loc, _), AppLoc(mloc, lineloc, _)) if mloc == loc =>
          1
        case (AppLoc(mloc, lineloc, _), CallbackMethodReturn(fmwClazz, fmwName, loc, _)) if mloc == loc =>
          -1
        case (_:AppLoc, _:InternalMethodInvoke) if stack1 == stack2 => -1
        case (_:InternalMethodInvoke, _:AppLoc) if stack1 == stack2 => 1
        case (_:AppLoc, _) if stack1 == stack2 =>
          1 //Always prefer appLoc
        case (_, _:AppLoc) if stack1 == stack2 =>
          -1
        case _ =>{
          p2.depth - p1.depth
//          if(p2.depth != p1.depth)
//            p2.depth - p1.depth
//          else
//            s2.heapConstraints.size - s1.heapConstraints.size
        }
      }
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
  def executeBackward(qry: Set[Qry]) : Set[IPathNode] = {
    val pathNodes = qry.map(PathNode(_,Nil,None))
    val queue = PriorityQueue[IPathNode]()
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

  private def groupAndTransferPostIfCmd(qrySet:mutable.PriorityQueue[IPathNode]):mutable.PriorityQueue[IPathNode] = {
    //TODO: is copy needed here?
    val qrySet2 = qrySet.clone
    val groups: Map[Option[AppLoc], List[IPathNode]] = qrySet2.toList.groupBy{ pn => pn.qry.loc match {
      case l@AppLoc(_,_,false) =>
        val cmd = w.cmdAtLocation(l)
        cmd match{
          case If(_,_,_) => Some(l)
          case _ => None
        }
      case _ => None
    }}
    val newQ = mutable.PriorityQueue[IPathNode]()
    groups.foreach{
      case (None,v) => newQ.addAll(v)
      case (Some(l),v) if v.size == 1 => newQ.addAll(v)
      case (Some(l),v) =>
        val groups = v.groupBy(v2 => v2.qry.state.nextCmd.get)
        if(groups.size == 1)
          newQ.addAll(v)
        else if(groups.size == 2) {
//          println(groups)
          val (_, group1) = groups.head
          val (_, group2) = groups.last
          val subsPairs: Seq[(IPathNode, Option[IPathNode])] = group1.map{ v1 =>
            val g2Subs = group2.find(v2 =>
              // Test if states are equivalent
              stateSolver.canSubsume(v1.qry.state,v2.qry.state) && stateSolver.canSubsume(v2.qry.state,v1.qry.state)
            )
            (v1,g2Subs)
          }.filter{case (_,g2s) => g2s.nonEmpty}

          // For each subsumed pair, switch the location of the subsuming state to before the if and
          val preIf: Seq[IPathNode] = subsPairs.map{case (k,_) => k.copyWithNewLoc({
            case AppLoc(m,l,false) => AppLoc(m,l,true)
            case _ => throw new IllegalStateException(s"Loc match error: $k")
          })}
          newQ.addAll(preIf)

          // drop the pair from the set that transfers over the if
          val subsPairAllSet = subsPairs.flatMap{case (k,v) => List(k) ++ v }

          // Add other branches
          val v2 = v.toSet -- subsPairAllSet
          newQ.addAll(v2)


        } else {
          throw new IllegalStateException("More than two target branches for condition statement")
        }

      case (_,v) =>
        throw new IllegalStateException(s"If edge with more than 2 successors: ${v.map(_.toString).mkString(";;")}")
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
//    println(s"current loc: ${current.qry.loc}")
//    println("--------------------")


    //TODO: uncomment:
    current.qry.loc match{
      case SwapLoc(FrameworkLocation) =>
        println("Framework location query")
        println(s"    State: ${current.qry.state}")
        println(s"    Loc  : ${current.qry.loc}")
//        println(s"    Subsumed:${current.subsumed}")
        println(s"    depth: ${current.depth}")
        println(s"    size of worklist: ${qrySetIG.size}")
        println(s"    ord depth: ${current.ordDepth}")
      case _ =>
    }

    current match {
      case p@PathNode(_:SomeQry, true) =>
        executeBackward(qrySetIG, limit, refutedSubsumedOrWitnessed + p, visited)
      case p@PathNode(_:BottomQry,_) =>
        executeBackward(qrySetIG, limit, refutedSubsumedOrWitnessed + p, visited)
      case p@PathNode(_:WitnessedQry,_) =>
        refutedSubsumedOrWitnessed.union(qrySetIG.toSet) + p
      case p:IPathNode if p.depth > limit =>
//        executeBackward(qrySetIG, limit, refutedSubsumedOrWitnessed + p, visited)
        refutedSubsumedOrWitnessed.union(qrySetIG.toSet)
      case p@PathNode(qry:SomeQry,false) =>
        isSubsumed(p, visited) match{
          case v@Some(_) =>
            executeBackward(qrySetIG, limit, refutedSubsumedOrWitnessed + p.setSubsumed(v), visited)
          case None =>
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
      predecessorLocations.par.flatMap(l => {
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
