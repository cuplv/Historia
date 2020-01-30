package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallinMethodReturn, CmdWrapper, IRWrapper, Invoke, InvokeCmd, Loc, SpecialInvoke, StaticInvoke, VirtualInvoke}
import edu.colorado.plv.bounder.state.State

/**
 * Functions to resolve code targets for call sites and match lifestate rules.
 */
class ControlFlowResolver[M,C](w:IRWrapper[M,C], a: AppCodeResolver) {
  def resolveReturns(cmd:CmdWrapper[M,C]):List[Loc] = cmd match{
    case AssignCmd(_, i:Invoke[M,C],l,w) => resolveReturns(i)
    case InvokeCmd(i,l, w) => resolveReturns(i)
    case _ => List()
  }
  def resolveReturns(invoke: Invoke[M,C]):List[Loc] = {
    if(a.isFrameworkClass(invoke.targetClass)){
      //TODO: what to do if multiple targets possible?
      List(CallinMethodReturn(invoke.targetClass,invoke.targetMethod))
    }else{
      ???
    }
  }
  def resolvePredicessors(loc:Loc):List[Loc] = loc match{
    case l@AppLoc(_,_) => {
      val cmd: CmdWrapper[M, C] = w.cmdAfterLocation(l)
      if(w.isMethodEntry(cmd)){

        ???
      }else{
        // Delegate control flow within a procedure to the IR wrapper
        val predecessorCommands: List[Loc] = w.commandPredicessors(cmd)
        val functionReturns: List[Loc] = resolveReturns(cmd)
        if(functionReturns.isEmpty)predecessorCommands else functionReturns
      }
    }
    case CallinMethodReturn(clazz, name) => ???
    case _ => ???
  }
}

