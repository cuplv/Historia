package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallStackFrame, State}

/**
 * Functions to resolve control flow edges while maintaining context sensitivity.
 */
class ControlFlowResolver[M,C](wrapper:IRWrapper[M,C], resolver: AppCodeResolver) {
  def getResolver = resolver
  def upperBoundOfInvoke(i:Invoke):Option[String] = i match{
    case SpecialInvoke(LocalWrapper(_,baseType),_,_,_) => Some(baseType)
    case StaticInvoke(targetClass, _,_) => Some(targetClass)
    case VirtualInvoke(LocalWrapper(_,baseType),_,_,_) => Some(baseType)
  }
  def resolvePredicessors(loc:Loc, state: State):Iterable[Loc] = (loc,state.callStack) match{
    case (l@AppLoc(method,_,true),_) => {
      val cmd: CmdWrapper = wrapper.cmdAtLocation(l)
      cmd match {
        case cmd if wrapper.isMethodEntry(cmd) =>
          val callback = resolver.resolveCallbackEntry(method)
          callback.toList
        case _ => // normal control flow
          val pred = wrapper.commandPredicessors(cmd)
          pred
      }
    }
    case (l@AppLoc(_,_,false),_) => {
      val cmd: CmdWrapper = wrapper.cmdAtLocation(l)
      cmd match{
        case InvokeCmd(i, loc) => {
          val upper = upperBoundOfInvoke(i)
          val unresolvedTargets = wrapper.makeInvokeTargets(loc,upper)
          val resolved = resolver.resolveCallLocation(unresolvedTargets)
          resolved
        }
        case AssignCmd(tgt, i:Invoke,loc) => {
          val upper = upperBoundOfInvoke(i)
          val unresolvedTargets = wrapper.makeInvokeTargets(loc,upper)
          val resolved = resolver.resolveCallLocation(unresolvedTargets)
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
        locCb.flatMap{case AppLoc(method,line,isPre) => resolver.resolveCallbackExit(method, Some(line))}
      }).toList
    case (CallbackMethodReturn(fmwClazz,fmwName, loc, Some(line)),_) =>
      AppLoc(loc, line, true)::Nil
    case (CallinMethodInvoke(fmwClazz, fmwName),Nil) =>
      val m: Option[MethodLoc] = wrapper.findMethodLoc(fmwClazz, fmwName)
      m.map(m2 =>
        wrapper.appCallSites(m2,resolver).map(v => v.copy(isPre = true))).getOrElse(List())
    case (InternalMethodReturn(clazz,name,loc), state) =>
      wrapper.makeMethodRetuns(loc)
    case v =>
      println(v)
      ???
  }
}