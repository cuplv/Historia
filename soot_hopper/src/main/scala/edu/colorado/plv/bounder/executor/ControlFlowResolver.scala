package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, IRWrapper, Invoke, InvokeCmd, Loc, SpecialInvoke, StaticInvoke, VirtualInvoke}
import edu.colorado.plv.bounder.state.{CallStackFrame, State}

/**
 * Functions to resolve code targets for call sites and match lifestate rules.
 */
class ControlFlowResolver[M,C](wrapper:IRWrapper[M,C], resolver: AppCodeResolver) {
//  def resolveReturns(cmd:CmdWrapper[M,C]):List[Loc] = cmd match{
//    case AssignCmd(_, i:Invoke[M,C],l,w) => resolveReturns(i)
//    case InvokeCmd(i,l, w) => resolveReturns(i)
//    case _ => List()
//  }
//  def resolveReturns(invoke: Invoke[M,C]):List[Loc] = {
//    val targets = wrapper.makeInvokeTargets(invoke)
//    ???
////    if(resolver.isFrameworkClass(invoke.targetClass)){
////      List(CallinMethodReturn(invoke.targetClass,invoke.targetMethod))
////    }else{
////      ???
////    }
//  }
  def resolvePredicessors(loc:Loc, stack: List[CallStackFrame]):List[Loc] = (loc,stack) match{
    case (l@AppLoc(_,_),_) => {
      val cmd: CmdWrapper[M, C] = wrapper.cmdAfterLocation(l)
      if(wrapper.isMethodEntry(cmd)){

        ???
      }else{
        // Delegate control flow within a procedure to the IR wrapper
        val predecessorCommands = wrapper.commandPredicessors(cmd)
        predecessorCommands.flatMap(a => wrapper.cmdAfterLocation(a) match{
          case i:InvokeCmd[M,C] => wrapper.makeInvokeTargets(i)
          case _ => List(a)
        })
      }
    }
    case (CallinMethodReturn(clazz, name),_) => List(CallinMethodInvoke(clazz,name))
    case (CallinMethodInvoke(_, _), CallStackFrame(_,Some(returnLoc@AppLoc(_,_)),_)::_) => {
      wrapper.commandPredicessors(wrapper.cmdAfterLocation(returnLoc))
    }
    case _ => ???
  }
}

