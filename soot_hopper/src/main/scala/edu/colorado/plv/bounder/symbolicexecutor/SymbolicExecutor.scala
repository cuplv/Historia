package edu.colorado.plv.bounder.symbolicexecutor

import com.microsoft.z3.Context
import edu.colorado.plv.bounder.ir.{IRWrapper, Loc}
import edu.colorado.plv.bounder.solver.{PersistantConstraints, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, PathNode, Qry, SomeQry}

import scala.annotation.tailrec

case class SymbolicExecutorConfig[M,C](stepLimit: Option[Int],
                                       w :  IRWrapper[M,C],
                                       c : ControlFlowResolver[M,C],
                                       transfer : TransferFunctions[M,C],
                                       printProgress : Boolean = false,
                                       z3Timeout : Option[Int] = None // Timeout in seconds
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
  def executeBackward(qry: Qry) : Set[PathNode] = {
    config.stepLimit match{
      case Some(limit) => executeBackwardLimitSubsumeAll(Set(PathNode(qry,None,None)),limit)
      case None =>
        ???
    }
  }
  @tailrec
  final def executeBackwardLimitSubsumeAll(qrySet: Set[PathNode], limit:Int,
                                            refuted: Set[PathNode] = Set(),
                                           visited:Map[Loc,Set[PathNode]] = Map()):Set[PathNode] = {
    if (config.printProgress){
      println(s"Steps left until limit: $limit")
    }
    if(qrySet.isEmpty){
      refuted
    }else if(limit > 0) {
      val nextQry: Set[PathNode] = qrySet.flatMap{
        case succ@PathNode(qry@SomeQry(_,_), _, None) =>
          executeStep(qry).map{
            case q@SomeQry(state, loc) =>
              val subsumed = visited.get(loc).flatMap(_.find{
                case PathNode(SomeQry(subsumer, _), _, None) =>
                  val subs = stateSolver.canSubsume(subsumer,state)
                  subs
                case _ => false
              })
              PathNode(q, Some(succ), subsumed)
            case b@BottomQry(_,_) => PathNode(b, Some(succ), None)
          }
        case PathNode(SomeQry(_,_), _, Some(_)) => Set()
        case PathNode(BottomQry(_,_), _, _) => Set()
      }
      val newVisited: Map[Loc, Set[PathNode]] = qrySet.groupBy(_.qry.loc)
      val refuted = qrySet.filter(a => a.qry.isInstanceOf[BottomQry] || a.subsumed.isDefined)
      val nextVisited = (visited ++ newVisited).map {
        case (k,v) => k-> v.union(visited.getOrElse(k,Set()))
      }
      executeBackwardLimitSubsumeAll(nextQry, limit - 1, refuted, nextVisited)
    }else {
      refuted ++ qrySet
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
      predecessorLocations.flatMap(l => {
        val newStates = config.transfer.transfer(state,l,loc)
        newStates.map(state => state.simplify(stateSolver) match {
          case Some(state) => SomeQry(state, l)
          case None =>
            BottomQry(state,l)
        })
      }).toSet
    case BottomQry(_,_) => Set()
  }
}
