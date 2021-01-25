package edu.colorado.plv.bounder.symbolicexecutor

import com.microsoft.z3.Context
import edu.colorado.plv.bounder.ir.{CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, IRWrapper, Loc}
import edu.colorado.plv.bounder.solver.{PersistantConstraints, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, PathNode, Qry, SomeQry, WitnessedQry}

import scala.annotation.tailrec

sealed trait CallGraphSource
case object FlowdroidCallGraph extends CallGraphSource
case object CHACallGraph extends CallGraphSource
case object SparkCallGraph extends CallGraphSource
case object AppOnlyCallGraph extends CallGraphSource

case class SymbolicExecutorConfig[M,C](stepLimit: Option[Int],
                                       w :  IRWrapper[M,C],
                                       c : ControlFlowResolver[M,C],
                                       transfer : TransferFunctions[M,C],
                                       printProgress : Boolean = false,
                                       z3Timeout : Option[Int] = None
                                      )
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
    new PersistantConstraints(ctx, solver, config.w.getClassHierarchy)
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
      case Some(limit) => executeBackwardLimitSubsumeAll(pathNodes,limit)
      case None =>
        ???
    }
  }

  //TODO: add loop heads?
  private def subsumableLocation(loc:Loc) :Boolean = loc match{
    case _ : CallbackMethodInvoke => true
    case _ : CallbackMethodReturn => true
    case _ : CallinMethodInvoke => true
    case _ : CallinMethodReturn => true
    case _ => false
  }

  @tailrec
  final def executeBackwardLimitSubsumeAll(qrySet: Set[PathNode], limit:Int,
                                           refutedSubsumedOrWitnessed: Set[PathNode] = Set(),
                                           visited:Map[Loc,Set[PathNode]] = Map()):Set[PathNode] = {

    def isSubsumed(qry: Qry, nVisited: Map[Loc,Set[PathNode]]):Option[PathNode] = qry match{
      case SomeQry(state,loc) if nVisited.contains(loc) =>
        nVisited(loc).find(a =>
          stateSolver.canSubsume(a.qry.state,state)
        )
      case _ => None
    }
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
      val newVisited: Map[Loc, Set[PathNode]] = liveQueries
        .filter(pathNode => subsumableLocation(pathNode.qry.loc))
        .groupBy(_.qry.loc)
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
  @tailrec
  final def executeBackwardLimitKeepAll(qrySet: Set[PathNode], limit:Int,
                                  refuted: Set[PathNode] = Set()):Set[PathNode] = {
    if(qrySet.isEmpty){
      refuted
    }else if(limit > 0) {
      val nextQry = qrySet.flatMap{
        case succ@PathNode(qry@SomeQry(_,_), _,_) => executeStep(qry).map(PathNode(_,Some(succ), None))
        case PathNode(BottomQry(_,_), _,_) => Set()
      }
      executeBackwardLimitKeepAll(nextQry, limit - 1, qrySet.filter(_.qry.isInstanceOf[BottomQry]))
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
      val predecessorLocations = config.c.resolvePredicessors(loc,state)
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
