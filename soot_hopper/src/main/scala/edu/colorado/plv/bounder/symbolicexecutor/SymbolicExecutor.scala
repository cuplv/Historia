package edu.colorado.plv.bounder.symbolicexecutor

import com.microsoft.z3.Context
import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, IRWrapper, Loc}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, SetInclusionTypeSolving, StateTypeSolving, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, PathNode, Qry, SomeQry, WitnessedQry}
import soot.SootMethod

import scala.annotation.tailrec
import scala.collection.MapView
import scala.collection.parallel.CollectionConverters.ImmutableSetIsParallelizable

sealed trait CallGraphSource
case object FlowdroidCallGraph extends CallGraphSource
case object PatchedFlowdroidCallGraph extends CallGraphSource
case object CHACallGraph extends CallGraphSource
case object SparkCallGraph extends CallGraphSource
case object AppOnlyCallGraph extends CallGraphSource

/**
 *
 * @param stepLimit
 * @param w
 * @param transfer
 * @param printProgress
 * @param z3Timeout
 * @param component restrict analysis to callbacks that match the listed regular expressions
 * @tparam M
 * @tparam C
 */
case class SymbolicExecutorConfig[M,C](stepLimit: Option[Int],
                                       w :  IRWrapper[M,C],
                                       transfer : TransferFunctions[M,C],
                                       printProgress : Boolean = sys.env.getOrElse("DEBUG","false").toBoolean,
                                       z3Timeout : Option[Int] = None,
                                       component : Option[List[String]] = None,
                                       stateTypeSolving: StateTypeSolving = SetInclusionTypeSolving
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
  val persistantConstraints =
    new ClassHierarchyConstraints(ctx, solver, config.w.getClassHierarchy, config.stateTypeSolving)

  val appCodeResolver = new DefaultAppCodeResolver[M,C](config.w)
  def getAppCodeResolver = appCodeResolver
  val controlFlowResolver =
    new ControlFlowResolver[M,C](config.w,appCodeResolver, persistantConstraints, config.component)
  def getControlFlowResolver = controlFlowResolver
  val stateSolver = new Z3StateSolver(persistantConstraints)
  /**
   *
   * @param qry - a source location and an assertion to prove
   * @return None if the assertion at that location is unreachable, Some(Trace) if it is reachable.
   *         Trace will contain a tree of backward executions for triage.
   */
  def executeBackward(qry: List[Qry]) : Set[PathNode] = {
    val pathNodes = qry.map(PathNode(_,None,None)).toSet
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

  @tailrec
  final def executeBackwardLimitSubsumeAll(qrySet: Set[PathNode], limit:Int,
                                           refutedSubsumedOrWitnessed: Set[PathNode] = Set(),
                                           visited:Map[SubsumableLocation,Set[PathNode]] = Map()):Set[PathNode] = {

    if (config.printProgress){
      println(s"Steps left until limit: $limit queries: ${qrySet.size}")
    }
    if(qrySet.isEmpty || qrySet.exists(p => p.qry.isInstanceOf[WitnessedQry]) || 0 >= limit){
      refutedSubsumedOrWitnessed ++ qrySet
    }else {
      // Split queries into live queries(true) and refuted/witnessed/subsumed(false)
      val queriesByType: Map[Boolean, Set[PathNode]] = qrySet.groupBy{
        case PathNode(_:SomeQry, _,None) => true
        case p@PathNode(_:SomeQry, _,Some(_)) =>
          false
        case PathNode(_:BottomQry,_,_) => false
        case PathNode(_:WitnessedQry,_,_) => false
      }

      val liveQueries: Set[PathNode] = queriesByType.getOrElse(true, Set())
      // add new visited to old visited
      // filter out locations that we don't want to consider for subsumption
      val newVisited: MapView[SubsumableLocation, Set[PathNode]] = liveQueries
        .flatMap(pathNode => SwapLoc(pathNode.qry.loc)
          .map((_,pathNode))).groupBy(_._1).view.mapValues(_.map(_._2))
      val nextVisited = (visited ++ newVisited).map {
        case (k, v) => k -> v.union(visited.getOrElse(k, Set()))
      }

      // collect dead queries
      val newRefutedSubsumedOrWitnessed = refutedSubsumedOrWitnessed ++
        queriesByType.getOrElse(false,Set())

      // execute step on live queries
      val nextQry = liveQueries.flatMap {
        case p@PathNode(qry: SomeQry, _, None) =>
          executeStep(qry).map((p,_))
      }

      val nextPathNode = nextQry.map{
        case (parent,q@SomeQry(_,_)) =>
          // Check subsumption for live queries
          val subsumingState = isSubsumed(q, nextVisited)
          PathNode(q, succ = Some(parent), subsumed = subsumingState)
        case (parent,q) =>
          // No subsumption check for Witnessed or Refuted queries
          PathNode(q, succ = Some(parent), subsumed = None)
      }

      executeBackwardLimitSubsumeAll(nextPathNode,
        limit - 1,
        newRefutedSubsumedOrWitnessed,
        nextVisited)
    }
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
        val newStates = config.transfer.transfer(state,l,loc)
        newStates.map(state => state.simplify(stateSolver) match {
          case Some(state) if stateSolver.witnessed(state) => WitnessedQry(state, l)
          case Some(state) => SomeQry(state, l)
          case None =>
            BottomQry(state,l)
        })
      }).toSet
    case BottomQry(_,_) => Set()
  }
}
