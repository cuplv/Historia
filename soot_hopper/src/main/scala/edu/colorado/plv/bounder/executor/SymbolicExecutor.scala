package edu.colorado.plv.bounder.executor

import java.util

import edu.colorado.plv.bounder.ir.{CmdWrapper, IRWrapper}
import edu.colorado.plv.bounder.state.{FullTrace, Qry, SomeQry, Trace, TraceNode}
import edu.colorado.plv.fixedsoot.EnhancedUnitGraphFixed
import soot.{Body, UnitPatchingChain}

import scala.collection.mutable
import scala.jdk.CollectionConverters._

case class SymbolicExecutorConfig[M,C](stepLimit: Int, w :  IRWrapper[M,C])
class SymbolicExecutor[M,C](config: SymbolicExecutorConfig[M,C]) {

  var transfer = new TransferFunctions[M,C]()
  /**
   *
   * @param qry - a source location and an assertion to prove
   * @return None if the assertion at that location is unreachable, Some(Trace) if it is reachable.
   *         Trace will contain a tree of backward executions for triage.
   *         // TODO; Config to exclude proven
   */
  def executeBackward(qry : Qry) : TraceNode = {
    if(config.stepLimit > 0) {
      val cmd = config.w.makeCmd(qry.loc)

      if(config.w.isMethodEntry(cmd)){
        // TODO: handle entry of method
        ???
      }else {
        val preds: Set[CmdWrapper[M, C]] = config.w.preds(cmd)
        val predStates: Set[TraceNode] = preds.flatMap(cmd => {
          val predStates = transfer.transfer(qry, cmd)
          predStates.map(executeBackward)
        })
        TraceNode(qry, predStates)
      }
    }else{
      // Exceeded number of steps, terminate search
      TraceNode(qry, Set())
    }
  }
}
