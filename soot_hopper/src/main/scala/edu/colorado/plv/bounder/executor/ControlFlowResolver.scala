package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, IRWrapper, Invoke, InvokeCmd, Loc, SpecialInvoke, StaticInvoke, VirtualInvoke}
import edu.colorado.plv.bounder.state.{CallStackFrame, State}

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
  def resolvePredicessors(loc:Loc, stack: List[CallStackFrame]):List[Loc] = (loc,stack) match{
    case (l@AppLoc(_,_),_) => {
      val cmd: CmdWrapper[M, C] = w.cmdAfterLocation(l)
      if(w.isMethodEntry(cmd)){

        ???
      }else{
        // Delegate control flow within a procedure to the IR wrapper
        val predecessorCommands = w.commandPredicessors(cmd)
        predecessorCommands.flatMap(a => w.cmdAfterLocation(a) match{
          case i:InvokeCmd[M,C] => resolveReturns(i)
          case _ => List(a)
        })
      }
    }
    case (CallinMethodReturn(clazz, name),_) => List(CallinMethodInvoke(clazz,name))
    case (CallinMethodInvoke(_, _), CallStackFrame(_,Some(returnLoc@AppLoc(_,_)),_)::_) => {
      w.commandPredicessors(w.cmdAfterLocation(returnLoc))
    }
    case _ => ???
  }
}

