package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, IRWrapper, Invoke, InvokeCmd, Loc, SpecialInvoke, StaticInvoke, UnresolvedMethodTarget, VirtualInvoke}
import edu.colorado.plv.bounder.state.{CallStackFrame, State}

/**
 * Functions to resolve code targets for call sites and match lifestate rules.
 */
class ControlFlowResolver[M,C](wrapper:IRWrapper[M,C], resolver: AppCodeResolver) {
  def resolvePredicessors(loc:Loc, stack: List[CallStackFrame]):List[Loc] = (loc,stack) match{
    case (l@AppLoc(_,_,true),_) => {
      val cmd: CmdWrapper[M, C] = wrapper.cmdAfterLocation(l)
      if(wrapper.isMethodEntry(cmd)){
        ???
      }else{
        // Delegate control flow within a procedure to the IR wrapper
        val predecessorCommands: List[AppLoc] = wrapper.commandPredicessors(cmd)
        predecessorCommands
      }
    }
    case (l@AppLoc(_,_,false),_) => {
      val cmd: CmdWrapper[M, C] = wrapper.cmdBeforeLocation(l)
      cmd match{
        case i:InvokeCmd[M,C] => {
          val unresolvedTargets = wrapper.makeInvokeTargets(i)
          unresolvedTargets.map(resolver.resolveMethodLocation).toList
        }
        case _ => List(l.copy(isPre=true))
      }
    }
    case (CallinMethodReturn(clazz, name),_) => List(CallinMethodInvoke(clazz,name))
    case (CallinMethodInvoke(_, _), CallStackFrame(_,Some(returnLoc@AppLoc(_,_,true)),_)::_) =>
      List(returnLoc)
    case _ =>
      ???
  }
}

