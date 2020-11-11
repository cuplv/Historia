package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallStackFrame, State}

/**
 * Functions to resolve control flow edges while maintaining context sensitivity.
 */
class ControlFlowResolver[M,C](wrapper:IRWrapper[M,C], resolver: AppCodeResolver) {
  def getResolver = resolver
  def resolvePredicessors(loc:Loc, state: State):List[Loc] = (loc,state.callStack) match{
    case (l@AppLoc(method,_,true),_) => {
      val cmd: CmdWrapper = wrapper.cmdAfterLocation(l)
      if(wrapper.isMethodEntry(cmd)) {
        //TODO: resolve app call sites
        val callback = resolver.resolveCallbackEntry(method)
        callback.toList
      } else {
        // Delegate control flow within a procedure to the IR wrapper
        val predecessorCommands: List[AppLoc] = wrapper.commandPredicessors(cmd)
        predecessorCommands
      }
    }
    case (l@AppLoc(_,_,false),_) => {
      val cmd: CmdWrapper = wrapper.cmdBeforeLocation(l)
      cmd match{
        case i:InvokeCmd => {
          val unresolvedTargets = wrapper.makeInvokeTargets(i)
          val resolved = unresolvedTargets.map(resolver.resolveCallLocation).toList
          resolved
        }
        case _ => List(l.copy(isPre=true))
      }
    }
    case (CallinMethodReturn(clazz, name),_) =>
      // TODO: nested callbacks not currently handled
      List(CallinMethodInvoke(clazz,name))
    case (CallinMethodInvoke(_, _), CallStackFrame(_,Some(returnLoc@AppLoc(_,_,true)),_)::_) =>
      List(returnLoc)
    case (CallbackMethodInvoke(fmwClazz, fmwName, loc), _) =>
      val callbacks = resolver.getCallbacks
      callbacks.flatMap(callback => {
        val locCb = wrapper.makeMethodRetuns(callback)
        locCb.map{case AppLoc(method,line,isPre) => CallbackMethodReturn(method.classType,fmwName, callback,Some(line))}
      }).toList
    case (CallbackMethodReturn(fmwClazz,fmwName, loc, Some(line)),_) => AppLoc(loc, line, true)::Nil
    case _ =>
      ???
  }
}

