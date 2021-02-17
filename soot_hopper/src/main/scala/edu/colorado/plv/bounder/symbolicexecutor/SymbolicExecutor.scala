package edu.colorado.plv.bounder.symbolicexecutor

import com.microsoft.z3.Context
import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, IRWrapper, Loc}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, NoTypeSolving, StateTypeSolving, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, PathNode, Qry, SomeQry, WitnessedQry}
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
                                       stateTypeSolving: StateTypeSolving = NoTypeSolving
                                      ){
  def getSymbolicExecutor =
    new SymbolicExecutor[M, C](this)}
class SymbolicExecutor[M,C](config: SymbolicExecutorConfig[M,C]) {
  val ctx = new Context
//  val solver = ctx.mkSolver
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
  def getControlFlowResolver = controlFlowResolver
  val stateSolver = new Z3StateSolver(cha)
  /**
   *
   * @param qry - a source location and an assertion to prove
   * @return None if the assertion at that location is unreachable, Some(Trace) if it is reachable.
   *         Trace will contain a tree of backward executions for triage.
   */
  def executeBackward(qry: Set[Qry]) : Set[PathNode] = {
    val pathNodes = qry.map(PathNode(_,None,None))
    config.stepLimit match{
      case Some(limit) => executeBackwardOAT(pathNodes.toList, limit)
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
      case a: AppLoc if config.w.degreeOut(a) > 1 => Some(CodeLocation(a))
      case _: CallinMethodInvoke => None // message locations don't remember program counter so subsumption is unsound
      case _: CallinMethodReturn => None
      case _ => None
    }
    def apply(loc:Loc):Option[SubsumableLocation] = unapply(loc)
  }

  def isSubsumed(qry: Qry, nVisited: Map[SubsumableLocation,Set[PathNode]]):Option[PathNode] = qry match{
    case SomeQry(state,SwapLoc(loc)) if nVisited.contains(loc) =>
      nVisited(loc).find(a => {
        val possiblySubsumingState = a.qry.state
        val res = stateSolver.canSubsume(possiblySubsumingState, state)
        res
      })
    case _ => None
  }

  @tailrec
  final def executeBackwardOAT(qrySet: List[PathNode], limit:Int,
                                           refutedSubsumedOrWitnessed: Set[PathNode] = Set(),
                                           visited:Map[SubsumableLocation,Set[PathNode]] = Map()):Set[PathNode] = {


    if(qrySet.isEmpty){
      return refutedSubsumedOrWitnessed ++ qrySet
    }
    val current = qrySet.head

    if (config.printProgress && current.depth % 10 == 0 ){
      println(s"CurrentNodeSteps: ${current.depth} queries: ${qrySet.size}")
    }

    current match {
      case p@PathNode(_:SomeQry, _,Some(_)) =>
        executeBackwardOAT(qrySet.tail, limit, refutedSubsumedOrWitnessed + p, visited)
      case p@PathNode(_:BottomQry,_,_) =>
        executeBackwardOAT(qrySet.tail, limit, refutedSubsumedOrWitnessed + p, visited)
      case PathNode(_:WitnessedQry,_,_) =>
        refutedSubsumedOrWitnessed.union(qrySet.toSet)
      case p:PathNode if p.depth > limit =>
        refutedSubsumedOrWitnessed.union(qrySet.toSet)
      case p@PathNode(qry:SomeQry, _,None) =>
        isSubsumed(qry, visited) match{
          case v@Some(_) =>
            executeBackwardOAT(qrySet.tail, limit, refutedSubsumedOrWitnessed + p.copy(subsumed = v), visited)
          case None =>
            val newVisited: Map[SubsumableLocation, Set[PathNode]] = SwapLoc(current.qry.loc) match{
              case Some(v) => visited + (v -> (visited.getOrElse(v,Set()) + p))
              case None => visited
            }
            val nextQry = executeStep(qry).map(q => PathNode(q, Some(p), None))
            val nextQrySet = qrySet.tail.appendedAll(nextQry)
            executeBackwardOAT(nextQrySet, limit, refutedSubsumedOrWitnessed, newVisited)
        }
    }
  }
  @tailrec
  final def executeBackwardLimitKeepAll(qrySet: Set[PathNode], limit:Int,
                                  refuted: Set[PathNode] = Set()):Set[PathNode] = {
    if(qrySet.isEmpty){
      refuted
    }else if(limit > 0) {
      val nextQry = qrySet.map{
        case succ@PathNode(qry@SomeQry(_,_), _,_) => executeStep(qry).map(PathNode(_,Some(succ), None))
        case PathNode(BottomQry(_,_), _,_) => Set()
        case PathNode(WitnessedQry(_,_),_,_) => Set()
      }
      executeBackwardLimitKeepAll(nextQry.flatten, limit - 1, qrySet.filter(_.qry.isInstanceOf[BottomQry]))
    }else {
      refuted ++ qrySet
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
      //TODO: check for witnessed state
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
