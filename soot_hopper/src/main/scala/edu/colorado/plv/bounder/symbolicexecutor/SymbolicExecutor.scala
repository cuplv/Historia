package edu.colorado.plv.bounder.symbolicexecutor

import com.microsoft.z3.Context
import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, IRWrapper, InternalMethodInvoke, InternalMethodReturn, Invoke, InvokeCmd, Loc, MethodLoc, SpecialInvoke, StaticInvoke, VirtualInvoke}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, NoTypeSolving, StateTypeSolving, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, DBOutputMode, IPathNode, MemoryOutputMode$, OutputMode, PathNode, Qry, SomeQry, WitnessedQry}
import soot.SootMethod

import scala.annotation.tailrec
import scala.collection.MapView
import scala.collection.parallel.CollectionConverters.ImmutableSetIsParallelizable
import upickle.default._

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
                                       stateTypeSolving: StateTypeSolving = NoTypeSolving,
                                       outputMode : OutputMode = MemoryOutputMode$
                                      ){
  def getSymbolicExecutor =
    new SymbolicExecutor[M, C](this)}
class SymbolicExecutor[M,C](config: SymbolicExecutorConfig[M,C]) {
  implicit var pathMode = config.outputMode
  val ctx = new Context
  val solver = {
    val solver = ctx.mkSolver
    val params = ctx.mkParams()
    config.z3Timeout match{
      case Some(v) => params.add("timeout", v*1000)
      case None =>
    }
    solver.setParameters(params)
    solver
  }
  val cha =
    new ClassHierarchyConstraints(ctx, solver, config.w.getClassHierarchy, config.stateTypeSolving)
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
  /**
   *
   * @param qry - a source location and an assertion to prove
   * @return None if the assertion at that location is unreachable, Some(Trace) if it is reachable.
   *         Trace will contain a tree of backward executions for triage.
   */
  def executeBackward(qry: Set[Qry]) : Set[IPathNode] = {
    val pathNodes = qry.map(PathNode(_,None,None))
    config.stepLimit match{
      case Some(limit) => executeBackward(pathNodes.toList, limit)
      case None =>
        ???
    }
  }

  sealed trait SubsumableLocation
  case class CodeLocation(loc:Loc)extends SubsumableLocation
  case object FrameworkLocation extends SubsumableLocation
  //TODO: add loop heads?
  object SwapLoc {
    def unapply(loc: Loc): Option[SubsumableLocation] = loc match {
      case _: CallbackMethodInvoke => Some(FrameworkLocation)
      case _: CallbackMethodReturn => None
      case AppLoc(_,_,false) => None
      case a@AppLoc(_,_,true) if config.w.degreeIn(a) > 1 => Some(CodeLocation(a))
      case _: CallinMethodInvoke => None // message locations don't remember program counter so subsumption is unsound
      case _: CallinMethodReturn => None
      case _: InternalMethodInvoke => None
      case _: InternalMethodReturn => None
      case a@AppLoc(_,_,true) =>
        config.w.cmdAtLocation(a) match {
          case InvokeCmd(_, _) => Some(CodeLocation(a))
          case AssignCmd(_, VirtualInvoke(_,_,_,_),_) => Some(CodeLocation(a))
          case AssignCmd(_, SpecialInvoke(_,_,_,_),_) => Some(CodeLocation(a))
          case AssignCmd(_, StaticInvoke(_,_,_),_) => Some(CodeLocation(a))
          case _ => None
        }
    }
    def apply(loc:Loc):Option[SubsumableLocation] = unapply(loc)
  }

  def isSubsumed(qry: Qry, nVisited: Map[SubsumableLocation,Map[Int,Set[IPathNode]]]):Option[IPathNode] = qry match{
    case SomeQry(state,SwapLoc(loc)) if nVisited.contains(loc) =>
      nVisited(loc).getOrElse(qry.state.callStack.size, Set()).find(a => {
        val possiblySubsumingState = a.qry.state
        val res = stateSolver.canSubsume(possiblySubsumingState, state)
        res
      })
    case _ => None
  }

  /**
   *
   * @param qrySet
   * @param limit
   * @param refutedSubsumedOrWitnessed
   * @param visited Map of visited states StackSize -> Location -> Set[State]
   * @return
   */
  @tailrec
  final def executeBackward(qrySet: List[IPathNode], limit:Int,
                            refutedSubsumedOrWitnessed: Set[IPathNode] = Set(),
                            visited:Map[SubsumableLocation,Map[Int,Set[IPathNode]]] = Map()):Set[IPathNode] = {

    if(qrySet.isEmpty){
      return refutedSubsumedOrWitnessed ++ qrySet
    }
    val current = qrySet.head

//    if (config.printProgress && current.depth % 10 == 0 ){
//      println(s"CurrentNodeSteps: ${current.depth} queries: ${qrySet.size}")
//    }
    current.qry.loc match{
      case SwapLoc(FrameworkLocation) =>
        println("Framework location query")
        println(s"    State: ${current.qry.state}")
        println(s"    Loc  : ${current.qry.loc}")
        println(s"    Subsumed:${current.subsumed}")
        println(s"    depth: ${current.depth}")
        println(s"    size of worklist: ${qrySet.size}")
      case _ =>
    }

    current match {
      case p@PathNode(_:SomeQry, true) =>
        executeBackward(qrySet.tail, limit, refutedSubsumedOrWitnessed + p, visited)
      case p@PathNode(_:BottomQry,_) =>
        executeBackward(qrySet.tail, limit, refutedSubsumedOrWitnessed + p, visited)
      case PathNode(_:WitnessedQry,_) =>
        refutedSubsumedOrWitnessed.union(qrySet.toSet)
      case p:IPathNode if p.depth > limit =>
        refutedSubsumedOrWitnessed.union(qrySet.toSet)
      case p@PathNode(qry:SomeQry,false) =>
        isSubsumed(qry, visited) match{
          case v@Some(_) =>
            executeBackward(qrySet.tail, limit, refutedSubsumedOrWitnessed + p.setSubsumed(v), visited)
          case None =>
            val stackSize = p.qry.state.callStack.size
            val newVisited = SwapLoc(current.qry.loc) match{
              case Some(v) =>
                val stackSizeToNode = visited.getOrElse(v,Map[Int,Set[IPathNode]]())
                val nodeSet = stackSizeToNode.getOrElse(stackSize, Set()) + p
                val newStackSizeToNode = stackSizeToNode + (stackSize -> nodeSet)
                visited + (v -> newStackSizeToNode)
              case None => visited
            }
            val nextQry = executeStep(qry).map(q => PathNode(q, Some(p), None))
            val nextQrySet = qrySet.tail.appendedAll(nextQry)
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
      //TODO: combine all callin locs that behave the same in the control flow resolver
      predecessorLocations.flatMap(l => {
        val newStates = transfer.transfer(state,l,loc)
        newStates.map(state => state.simplify(stateSolver) match {
          case Some(state) if stateSolver.witnessed(state) =>
            WitnessedQry(state, l)
          case Some(state) => SomeQry(state, l)
          case None =>
            BottomQry(state,l)
        })
      }).toSet
    case BottomQry(_,_) => Set()
    case WitnessedQry(_,_) => Set()
  }
}
