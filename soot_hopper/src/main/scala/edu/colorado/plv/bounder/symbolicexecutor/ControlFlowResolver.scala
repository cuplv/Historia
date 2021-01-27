package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallStackFrame, FieldPtEdge, HeapPtEdge, LSPure, PureVar, State, StaticPtEdge}

import scala.collection.mutable

/**
 * Functions to resolve control flow edges while maintaining context sensitivity.
 */
class ControlFlowResolver[M,C](wrapper:IRWrapper[M,C], resolver: AppCodeResolver) {
  def getResolver = resolver

  //TODO: cache result
  def lazyDirectCallsGraph(loc: MethodLoc) : Set[Loc] = {
    val unresolvedTargets = wrapper.makeMethodTargets(loc).map(callee =>
      UnresolvedMethodTarget(callee.classType, callee.simpleName, Set(callee)))
    unresolvedTargets.flatMap(target => resolver.resolveCallLocation(target))
  }

  /**
   * Normally we crash on unsupported instructions, but when determining relevance, all we care about is invokes
   * Since relevance scans lots of methods,
   * @param loc
   * @return
   */
  def cmdAtLocationNopIfUnknown(loc: AppLoc):CmdWrapper = {
    try {
      wrapper.cmdAtLocation(loc)
    }catch{
      case _:NotImplementedError => NopCmd(loc)
    }
  }

  private def callsToRetLoc(loc:MethodLoc):Set[MethodLoc] = {
    val directCalls = lazyDirectCallsGraph(loc)
    val internalCalls = directCalls.flatMap{
      case InternalMethodReturn(_,_,loc) =>
        Some(loc)
      case _ =>
        None
    }
    internalCalls
  }

  def allCalls(loc: MethodLoc):Set[MethodLoc] = {
    val empty = Set[MethodLoc]()
    val out = BounderUtil.graphFixpoint[MethodLoc,Set[MethodLoc]](Set(loc),
      empty,
      empty,
      next = callsToRetLoc,
      comp = (_,v) => callsToRetLoc(v),
      join = (a,b) => a.union(b)
    )
    out.flatMap{
      case(k,v) => v
    }.toSet
  }

  def upperBoundOfInvoke(i: Invoke): Option[String] = i match {
    case SpecialInvoke(LocalWrapper(_, baseType), _, _, _) => Some(baseType)
    case StaticInvoke(targetClass, _, _) => Some(targetClass)
    case VirtualInvoke(LocalWrapper(_, baseType), _, _, _) => Some(baseType)
  }

  private def fieldCanPt(fr:FieldReference, state:State):Boolean = {
    val fname = fr.name
    val localType = fr.base.localType
    state.heapConstraints.exists{
      case (FieldPtEdge(p, otherFieldName),_) if fname == otherFieldName =>
        state.pvTypeUpperBound(p).forall(wrapper.canAlias(localType, _))
      case _ => false
    }
  }
  def relevantHeap(m: MethodLoc, state: State): Boolean = {
    def canModifyHeap(c : CmdWrapper) : Boolean = c match{
      case AssignCmd(fr:FieldReference, _,_) => fieldCanPt(fr, state)
      case AssignCmd(_,fr:FieldReference,_) => fieldCanPt(fr,state)
      case _:AssignCmd => false
      case _:ReturnCmd => false
      case _:InvokeCmd => false // This method only counts commands that directly modify the heap
      case _:If => false
      case _:NopCmd => false
      case _:ThrowCmd => false
    }
    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) => cmdAtLocationNopIfUnknown(v).mkPre)
    BounderUtil.graphExists[CmdWrapper](start = returns,
      next = n =>
        wrapper.commandPredecessors(n).map((v: AppLoc) => cmdAtLocationNopIfUnknown(v).mkPre).toSet,
      exists = canModifyHeap
    )
  }

  def relevantTrace(m: MethodLoc, state: State): Boolean = {
    val calls: Set[CallinMethodReturn] = lazyDirectCallsGraph(m).flatMap{
      case v: CallinMethodReturn => Some(v)
      case _: InternalMethodInvoke => None
      case _: InternalMethodReturn => None
      case v =>
        println(v)
        ???
    }
    calls.exists{call =>
      val relI = state.findIFromCurrent(CIEnter, (call.fmwClazz, call.fmwName)).union(
        state.findIFromCurrent(CIEnter, (call.fmwClazz, call.fmwName)))
      relI.exists{
        case v =>
          println(v)
          ???
      }
    }
  }

  def relevantMethodBody(m:MethodLoc, state:State):Boolean = {
    if (resolver.isFrameworkClass(m.classType))
      return false // body can only be relevant to app heap or trace if method is in the app
    val callees = allCalls(m) + m
    callees.exists{c =>
      if(relevantHeap(c,state))
        true
      else if(relevantTrace(c,state))
        true
      else
        false
    }
  }

  def existsIAlias(locals: List[Option[RVal]], dir :MessageType, sig: (String,String), state:State):Boolean = {
    val aliasPos = TransferFunctions.relevantAliases(state, dir, sig)
    aliasPos.exists{ aliasPo =>
      (aliasPo zip locals).forall{
        case (LSPure(v:PureVar), Some(local:LocalWrapper)) =>
          state.pvTypeUpperBound(v).forall(wrapper.canAlias(_, local.localType))
        case (LSPure(v:PureVar), Some(NullConst)) => ???
        case (LSPure(v:PureVar), Some(i:IntConst)) => ???
        case (LSPure(v:PureVar), Some(i:StringConst)) => ???
        case _ => true
      }
    }
  }
  def irrelevantCallinInvoke(m:Loc,state:State):Boolean = m match{
    case CallinMethodReturn(clazz, name) =>
      TransferFunctions.relevantAliases(state, CIExit, (clazz,name)).isEmpty &&
        TransferFunctions.relevantAliases(state, CIEnter, (clazz,name)).isEmpty
    case _ => false
  }
  def relevantMethod(loc: Loc, state: State): Boolean = loc match{
    case InternalMethodReturn(_,_,m) =>
      val callees: Set[MethodLoc] = allCalls(m)
      val out = callees.exists(c => relevantMethodBody(c,state))
      out
    case CallinMethodReturn(_,_) => true
    case CallbackMethodReturn(clazz, name, rloc, Some(retLine)) => {
      //TODO: switch on static or not
      val retVars =
        if(rloc.isStatic)
          wrapper.makeMethodRetuns(rloc).map{ retloc =>
            wrapper.cmdAtLocation(retloc) match{
              case ReturnCmd(Some(l), loc) => Some(l)
              case _ => None
            }
          }
        else List(None)
      val iExists = retVars.exists { retVar =>
        val locs: List[Option[RVal]] = retVar :: rloc.getArgs
        val res = existsIAlias(locs, CBExit, (clazz,name),state) ||
          existsIAlias(None::locs.tail, CBEnter, (clazz,name),state)
        res
      }
      val relevantBody = relevantMethodBody(rloc,state)
      iExists || relevantBody
    }
    case _ => throw new IllegalStateException("relevantMethod only for method returns")
  }
  def resolvePredicessors(loc:Loc, state: State):Iterable[Loc] = (loc,state.callStack) match{
    case (l@AppLoc(method,_,true),_) => {
      val cmd: CmdWrapper = wrapper.cmdAtLocation(l)
      cmd match {
        case cmd if wrapper.isMethodEntry(cmd) =>
//          val callback = resolver.resolveCallbackEntry(method)
          val callback = BounderUtil.resolveMethodEntryForAppLoc(resolver,l )
          callback
        case _ => // normal control flow
          val pred = wrapper.commandPredecessors(cmd)
          pred
      }
    }
    case (l@AppLoc(_,_,false),_) => {
      //TODO: filter resolved based on things that can possibly alias reciever
      val cmd: CmdWrapper = wrapper.cmdAtLocation(l)
      cmd match{
        case InvokeCmd(i, loc) => {
          val unresolvedTargets =
            wrapper.makeInvokeTargets(loc)
          val resolved: Set[Loc] = resolver.resolveCallLocation(unresolvedTargets) // .filter(relevantMethod(_, state))
          if(resolved.forall(m => !relevantMethod(m,state)))
            List(l.copy(isPre = true)) // skip if all method targets are not relevant
          else {
            val irrelevantCallinsToMerge: Set[Loc] = resolved.filter(irrelevantCallinInvoke(_,state))
            // merge all irrelevant callins with most general type
            val merged = irrelevantCallinsToMerge.headOption.map{v =>
              irrelevantCallinsToMerge.foldLeft(v){
                case (CallinMethodReturn(clazz,_), other@CallinMethodReturn(clazz2, _)) if wrapper.isSuperClass(clazz2,clazz) =>
                  other
                case (cur,other) =>
                  println(other)
                  cur
              }
            }
            (resolved -- irrelevantCallinsToMerge) ++ merged
          }
        }
        case AssignCmd(tgt, i:Invoke,loc) => {
          val unresolvedTargets =
            wrapper.makeInvokeTargets(loc)
          val resolved = resolver.resolveCallLocation(unresolvedTargets)
          if (state.get(tgt).isDefined)
            resolved
          else {
            if(resolved.forall(m => !relevantMethod(m,state)))
              List(l.copy(isPre = true)) // skip if all method targets are not relevant
            else
              resolved
          }
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
      val res = callbacks.flatMap(callback => {
        val locCb = wrapper.makeMethodRetuns(callback)
        locCb.flatMap{case AppLoc(method,line,isPre) => resolver.resolveCallbackExit(method, Some(line))}
      }).toList
      val res1 = res.filter(relevantMethod(_,state))
      res1
    case (CallbackMethodReturn(fmwClazz,fmwName, loc, Some(line)),_) =>
      AppLoc(loc, line, true)::Nil
    case (CallinMethodInvoke(fmwClazz, fmwName),Nil) =>
      val m: Option[MethodLoc] = wrapper.findMethodLoc(fmwClazz, fmwName)
      m.map(m2 =>
        wrapper.appCallSites(m2,resolver).map(v => v.copy(isPre = true))).getOrElse(List())
    case (InternalMethodReturn(clazz,name,loc), state) =>
      wrapper.makeMethodRetuns(loc)
    case (InternalMethodInvoke(_, _, _), CallStackFrame(_,Some(returnLoc:AppLoc),_)::_) => List(returnLoc)
    case (InternalMethodInvoke(clazz, name, loc), _) =>
      val locations = wrapper.appCallSites(loc, resolver)
        .filter(loc => !resolver.isFrameworkClass(loc.containingMethod))
      locations.map(loc => loc.copy(isPre = true))
    case v =>
      println(v)
      ???
  }
}