package edu.colorado.plv.bounder.executor

import java.util

import edu.colorado.plv.bounder.ir.{CallinMethodReturn, CmdWrapper, IRWrapper, Loc}
import edu.colorado.plv.bounder.state.{BottomQry, FullTrace, PathNode, Qry, SomeQry, State, Trace}
import edu.colorado.plv.fixedsoot.EnhancedUnitGraphFixed
import soot.{Body, UnitPatchingChain}

import scala.collection.mutable
import scala.jdk.CollectionConverters._

case class SymbolicExecutorConfig[M,C](stepLimit: Int,
                                       w :  IRWrapper[M,C],
                                       c : ControlFlowResolver[M,C],
                                       transfer : TransferFunctions[M,C]
                                      )
class SymbolicExecutor[M,C](config: SymbolicExecutorConfig[M,C]) {
//  val controlFlowResolver = new ControlFlowResolver[M,C](w)
  /**
   *
   * @param qry - a source location and an assertion to prove
   * @return None if the assertion at that location is unreachable, Some(Trace) if it is reachable.
   *         Trace will contain a tree of backward executions for triage.
   *         // TODO; Config to exclude proven
   */
  def executeBackwardRec(qry : Qry,stepLimit:Int) : PathNode = {
    if(stepLimit > 0) {
      val predStates = executeStep(qry)
      val nodes = predStates.map(a => executeBackwardRec(a,stepLimit-1))
      PathNode(qry, nodes)
    }else{
      // Exceeded number of steps, terminate search
      PathNode(qry, Set())
    }
  }

  /**
   * Call methods to choose where to go with symbolic execution and apply transfer functions
   * @param qry location and state combination
   * @return
   */
  def executeStep(qry:Qry):Set[Qry] = qry match{
    case SomeQry(state@State(callStack,_), loc) =>
      val predecessorLocations: Seq[Loc] = config.c.resolvePredicessors(loc,callStack)
      predecessorLocations.flatMap(l => {
        val newStates = config.transfer.transfer(state,l,loc)
        newStates.map(state =>
          if(state.isFeasible) SomeQry(state,l) else BottomQry(l))
      }).toSet
    case BottomQry(_) => Set()
  }
}
