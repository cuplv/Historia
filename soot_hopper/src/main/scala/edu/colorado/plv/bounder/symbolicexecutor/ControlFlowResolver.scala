package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{Invoke, _}
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallStackFrame, FieldPtEdge, LSParamConstraint, LSPure, PureVar, State, StaticPtEdge}
import org.scalactic.anyvals.NonEmptySet
import scalaz.Memo

import scala.collection.mutable
import scala.collection.parallel.CollectionConverters.ImmutableIterableIsParallelizable
import scala.util.matching.Regex
/**
 * Functions to resolve control flow edges while maintaining context sensitivity.
 */
class ControlFlowResolver[M,C](wrapper:IRWrapper[M,C],
                               resolver: AppCodeResolver,
                               cha: ClassHierarchyConstraints,
                               component: Option[List[String]]) {
  private val componentR: Option[List[Regex]] = component.map(_.map(_.r))

  def callbackInComponent(loc: Loc): Boolean = loc match {
    case CallbackMethodReturn(_, _, methodLoc, _) =>
      val className = methodLoc.classType
      componentR.forall(_.exists(r => r.matches(className)))
    case _ => throw new IllegalStateException("callbackInComponent should only be called on callback returns")
  }

  def getResolver = resolver
  def getWrapper = wrapper

  def directCallsGraph(loc: MethodLoc): Set[Loc] = {
    val unresolvedTargets = wrapper.makeMethodTargets(loc).map(callee =>
      UnresolvedMethodTarget(callee.classType, callee.simpleName, Set(callee)))
    unresolvedTargets.flatMap(target => resolver.resolveCallLocation(target))
  }

  /**
   * Normally we crash on unsupported instructions, but when determining relevance, all we care about is invokes
   * Since relevance scans lots of methods,
   *
   * @param loc
   * @return
   */
  def cmdAtLocationNopIfUnknown(loc: AppLoc): CmdWrapper = {
    try {
      wrapper.cmdAtLocation(loc)
    } catch {
      case CmdNotImplemented(_) => NopCmd(loc)
    }
  }

  var printCacheCache = mutable.Set[String]()

  /**
   * Debug function that only prints any given string once
   * @param s string to print
   */
  def printCache(s: String): Unit = {
    if (!printCacheCache.contains(s)) {
      println(s)
      printCacheCache.add(s)
    }
  }

  private def callsToRetLoc(loc: MethodLoc): Set[MethodLoc] = {
    val directCalls = directCallsGraph(loc)
    val internalCalls = directCalls.flatMap {
      case InternalMethodReturn(_, _, oloc) =>
        // We only care about direct calls, calls through framework are considered callbacks
        if (!resolver.isFrameworkClass(oloc.classType))
          Some(oloc)
        else
          None
      case _ =>
        None
    }
    internalCalls
  }

  def allCalls(loc: MethodLoc): Set[MethodLoc] = {
    val empty = Set[MethodLoc]()
    val out = BounderUtil.graphFixpoint[MethodLoc, Set[MethodLoc]](Set(loc),
      empty,
      empty,
      next = callsToRetLoc,
      comp = (_, v) => callsToRetLoc(v),
      join = (a, b) => a.union(b)
    )
    out.flatMap {
      case (k, v) => v
    }.toSet
  }

  val memoizedallCalls: MethodLoc => Set[MethodLoc] = Memo.mutableHashMapMemo(allCalls)

  //  val memoizedallCalls: MethodLoc => Set[MethodLoc]= allCalls
  def upperBoundOfInvoke(i: Invoke): Option[String] = i match {
    case SpecialInvoke(LocalWrapper(_, baseType), _, _, _) => Some(baseType)
    case StaticInvoke(targetClass, _, _) => Some(targetClass)
    case VirtualInvoke(LocalWrapper(_, baseType), _, _, _) => Some(baseType)
  }

  private def fieldCanPt(fr: FieldReference, state: State): Boolean = {
    val fname = fr.name
    val localType = fr.base.localType
    state.heapConstraints.exists {
      case (FieldPtEdge(p, otherFieldName), _) if fname == otherFieldName =>
        //        val res = state.pvTypeUpperBound(p).forall(wrapper.canAlias(localType, _))
        val posLocalTypes = cha.getSubtypesOf(localType)
        val pureTypes = cha.typeSetForPureVar(p, state)
        val res = posLocalTypes.exists(t => pureTypes.contains(t))
        res
      case _ => false
    }
  }

  def relevantHeap(m: MethodLoc, state: State): Boolean = {
    def canModifyHeap(c: CmdWrapper): Boolean = c match {
      case AssignCmd(fr: FieldReference, _, _) => fieldCanPt(fr, state)
      case AssignCmd(_, fr: FieldReference, _) => fieldCanPt(fr, state)
      case AssignCmd(StaticFieldReference(clazz, name, _), _, _) =>
        val out = state.heapConstraints.contains(StaticPtEdge(clazz, name))
        out //&& !manuallyExcludedStaticField(name) //TODO:

      case AssignCmd(_, StaticFieldReference(clazz, name, _), _) =>
        val out = state.heapConstraints.contains(StaticPtEdge(clazz, name))
        out //&& !manuallyExcludedStaticField(name)
      case _: AssignCmd => false
      case _: ReturnCmd => false
      case _: InvokeCmd => false // This method only counts commands that directly modify the heap
      case _: If => false
      case _: NopCmd => false
      case _: ThrowCmd => false
      case _: SwitchCmd => false
    }

    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) => cmdAtLocationNopIfUnknown(v).mkPre)
    BounderUtil.graphExists[CmdWrapper](start = returns,
      next = n =>
        wrapper.commandPredecessors(n).map((v: AppLoc) => cmdAtLocationNopIfUnknown(v).mkPre).toSet,
      exists = canModifyHeap
    )
  }

  //TODO: manuallyExcluded.* methods are for debugging scalability issues
  val excludedCaller =
    List(
      ".*ItemDescriptionFragment.*",
      ".*PlaybackController.*initServiceNot.*",
      ".*PlaybackController.*release.*",
      ".*PlaybackController.*bindToService.*",
    ).mkString("|").r
  /**
   * Experiment to see if better relevance filtering would improve performance
   * @param caller
   * @param callee
   * @return
   */
  def manuallyExcludedCallSite(caller:MethodLoc, callee:CallinMethodReturn):Boolean = {
    if (excludedCaller.matches(caller.classType + ";" + caller.simpleName)){
      printCache(s"excluding $caller calls $callee")
      true
    }else{
      false
    }
  }
  def manuallyExcludedStaticField(fieldName:String):Boolean = {
    fieldName == "isRunning"
  }

  def relevantTrace(m: MethodLoc, state: State): Boolean = {
    val calls: Set[CallinMethodReturn] = directCallsGraph(m).flatMap {
      case v: CallinMethodReturn => Some(v)
      case _: InternalMethodInvoke => None
      case _: InternalMethodReturn => None
      case v =>
        println(v)
        ???
    }
    // Find any call that matches a spec in the abstract trace
    // TODO: later this should be refined based on type information
    calls.exists { call =>
      Set(CIEnter, CIExit).exists{cdir =>
        val relI = state.findIFromCurrent(cdir, (call.fmwClazz, call.fmwName))
        relI.nonEmpty
      } //&& !manuallyExcludedCallSite(m,call) // TODO==== manually excluded call sites
    }
  }

  def iHeapNamesModified(m:MethodLoc):Set[String] = {
    def modifiedNames(c: CmdWrapper): Option[String] = c match {
      case AssignCmd(fr: FieldReference, _, _) => Some(fr.name)
      case AssignCmd(_, fr: FieldReference, _) => Some(fr.name)
      case AssignCmd(StaticFieldReference(_, name, _), _, _) => Some(name)
      case AssignCmd(_, StaticFieldReference(_, name, _), _) => Some(name)
      case _: AssignCmd => None
      case _: ReturnCmd => None
      case _: InvokeCmd => None
      case _: If => None
      case _: NopCmd => None
      case _: ThrowCmd => None
      case _: SwitchCmd => None
    }
    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) => cmdAtLocationNopIfUnknown(v).mkPre)
    BounderUtil.graphFixpoint[CmdWrapper, Set[String]](start = returns,Set(),Set(),
      next = n => wrapper.commandPredecessors(n).map((v: AppLoc) => cmdAtLocationNopIfUnknown(v).mkPre).toSet,
      comp = (acc,v) => acc ++ modifiedNames(v),
      join = (a,b) => a.union(b)
    ).flatMap{ case (_,v) => v}.toSet
  }
  val heapNamesModified:MethodLoc => Set[String] = Memo.mutableHashMapMemo{iHeapNamesModified}
  def iCallinNames(m:MethodLoc):Set[String] = {
    def modifiedNames(c: CmdWrapper): Option[String] = c match {
      case AssignCmd(_,i : Invoke, _) => Some(i.targetMethod)
      case _: AssignCmd => None
      case _: ReturnCmd => None
      case InvokeCmd(i,_) => Some(i.targetMethod)
      case _: If => None
      case _: NopCmd => None
      case _: ThrowCmd => None
      case _: SwitchCmd => None
    }
    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) => cmdAtLocationNopIfUnknown(v).mkPre)
    BounderUtil.graphFixpoint[CmdWrapper, Set[String]](start = returns,Set(),Set(),
      next = n => wrapper.commandPredecessors(n).map((v: AppLoc) => cmdAtLocationNopIfUnknown(v).mkPre).toSet,
      comp = (acc,v) => acc ++ modifiedNames(v),
      join = (a,b) => a.union(b)
    ).flatMap{ case (_,v) => v}.toSet
  }
  val callinNames:MethodLoc => Set[String] = Memo.mutableHashMapMemo{iCallinNames}
  def relevantMethodBody(m: MethodLoc, state: State): Boolean = {
    val fnSet = state.fieldNameSet()
    val mSet = state.traceMethodSet()
    if (resolver.isFrameworkClass(m.classType))
      return false // body can only be relevant to app heap or trace if method is in the app

    val allCalls = memoizedallCalls(m) + m
    val callees = allCalls.par.filter { m =>
      val fnOverlap = fnSet.exists { fn =>
        val hn = iHeapNamesModified(m)
        hn.contains(fn)
      }
      lazy val mSetOverlap = mSet.exists{ci =>
        val cin = callinNames(m)
        cin.contains(ci)
      }
      fnOverlap || mSetOverlap
    }

    callees.par.exists { c =>
      if (relevantHeap(c, state)) {
        printCache(s"method: $m calls $c - heap relevant to state: $state")
        true
      } else if (relevantTrace(c, state)) {
        printCache(s"method: $m calls $c trace relevant to state: $state")
      true
      } else
        false
    }
  }

  def existsIAlias(locals: List[Option[RVal]], dir: MessageType, sig: (String, String), state: State): Boolean = {
    val aliasPos = TransferFunctions.relevantAliases(state, dir, sig)
    aliasPos.exists { aliasPo =>
      (aliasPo zip locals).forall {
        case (LSPure(v: PureVar), Some(local: LocalWrapper)) =>
          cha.typeSetForPureVar(v, state).forall(wrapper.canAlias(_, local.localType))
        case (LSPure(v: PureVar), Some(NullConst)) => ???
        case (LSPure(v: PureVar), Some(i: IntConst)) => ???
        case (LSPure(v: PureVar), Some(i: StringConst)) => ???
        case _ => true
      }
    }
  }

  def relevantMethod(loc: Loc, state: State): Boolean = loc match {
    case InternalMethodReturn(_, _, m) =>
      val callees: Set[MethodLoc] = memoizedallCalls(m)
      val out = (callees + m).exists(c => relevantMethodBody(c, state))
      out
    case CallinMethodReturn(_, _) => true
    case CallbackMethodReturn(clazz, name, rloc, Some(retLine)) => {
      val retVars =
        if (rloc.isStatic)
          wrapper.makeMethodRetuns(rloc).map { retloc =>
            wrapper.cmdAtLocation(retloc) match {
              case ReturnCmd(Some(l), loc) => Some(l)
              case _ => None
            }
          } else List(None)
      val iExists = retVars.exists { retVar =>
        val locs: List[Option[RVal]] = retVar :: rloc.getArgs
        val res = existsIAlias(locs, CBExit, (clazz, name), state) ||
          existsIAlias(None :: locs.tail, CBEnter, (clazz, name), state)
        res
      }
      val relevantBody = relevantMethodBody(rloc, state)
      iExists || relevantBody
    }
    case _ => throw new IllegalStateException("relevantMethod only for method returns")
  }
  // Callins are equivalent if they match the same set of I predicates in the abstract trace
  def mergeEquivalentCallins(callins: Set[Loc], state: State): Set[Loc] ={
    val groups: Map[Object, Set[Loc]] = callins.groupBy{
      case CallinMethodReturn(fc,fn) =>
        val i: Set[(LifeState.I, List[LSParamConstraint])] = state.findIFromCurrent(CIExit,(fc,fn))
        i.map(a => a._1)
      case i => i
    }
    val out:Set[Loc] = groups.keySet.map{k =>
      //TODO: find least upper bound for receiver=========
      val classesToGroup = groups(k).map{
        case CallinMethodReturn(fmwClazz,_) => fmwClazz
        case InternalMethodReturn(clazz,_, _) => clazz
        case _ => throw new IllegalStateException()
      }
      groups(k).collectFirst{
        case CallinMethodReturn(_,name) =>
          GroupedCallinMethodReturn(classesToGroup,name)
        case imr@InternalMethodReturn(_,_,_) => imr
      }.getOrElse(throw new IllegalStateException())
    }
    out
  }
  def resolvePredicessors(loc:Loc, state: State):Iterable[Loc] = (loc,state.callStack) match{
    case (l@AppLoc(_,_,true),_) => {
      val cmd: CmdWrapper = wrapper.cmdAtLocation(l)
      cmd match {
        case cmd if wrapper.isMethodEntry(cmd) =>
          val methodEntries = BounderUtil.resolveMethodEntryForAppLoc(resolver,l )
          val out = methodEntries.filter(state.entryPossible(_))
          out
        case _ => // normal control flow
          val pred = wrapper.commandPredecessors(cmd)
          pred
      }
    }
    case (l@AppLoc(_,_,false),_) => {
      //TODO: filter resolved based on things that can possibly alias reciever
      // TODO: filter out clinit, call somewhere else?
      val cmd: CmdWrapper = wrapper.cmdAtLocation(l)
      cmd match{
        case InvokeCmd(i, loc) => {
          val unresolvedTargets: UnresolvedMethodTarget =
            wrapper.makeInvokeTargets(loc)
          val resolved: Set[Loc] = resolver.resolveCallLocation(unresolvedTargets)
          if(resolved.par.forall(m => !relevantMethod(m,state)))
            List(l.copy(isPre = true)) // skip if all method targets are not relevant
          else {
            mergeEquivalentCallins(resolved, state)
          }
        }
        case AssignCmd(tgt, _:Invoke,loc) => {
          val unresolvedTargets =
            wrapper.makeInvokeTargets(loc)
          val resolved = resolver.resolveCallLocation(unresolvedTargets)
          if (state.get(tgt).isDefined)
            mergeEquivalentCallins(resolved,state)
          else {
            if(resolved.par.forall(m => !relevantMethod(m,state)))
              List(l.copy(isPre = true)) // skip if all method targets are not relevant
            else
              mergeEquivalentCallins(resolved,state)
          }
        }
        case _ => List(l.copy(isPre=true))
      }
    }
    case (CallinMethodReturn(clazz, name),_) =>
      // TODO: nested callbacks not currently handled
      List(CallinMethodInvoke(clazz,name))
    case (GroupedCallinMethodReturn(classes, name),_) =>
      // TODO: nested callbacks not currently handled
      List(GroupedCallinMethodInvoke(classes, name))
    case (CallinMethodInvoke(_, _), CallStackFrame(_,Some(returnLoc@AppLoc(_,_,true)),_)::_) =>
      List(returnLoc)
    case (GroupedCallinMethodInvoke(_,_),CallStackFrame(_,Some(returnLoc@AppLoc(_,_,true)),_)::_) =>
      List(returnLoc)
    case (CallbackMethodInvoke(_, _, _), _) =>
      val callbacks = resolver.getCallbacks
      val res: Seq[Loc] = callbacks.flatMap(callback => {
        val locCb = wrapper.makeMethodRetuns(callback)
        locCb.flatMap{case AppLoc(method,line,_) => resolver.resolveCallbackExit(method, Some(line))}
      }).toList
      val componentFiltered = res.filter(callbackInComponent)
      val res1 = componentFiltered.filter(relevantMethod(_,state))
      res1
    case (CallbackMethodReturn(_,_, loc, Some(line)),_) =>
      AppLoc(loc, line, isPre = false)::Nil
    case (CallinMethodInvoke(fmwClazz, fmwName),Nil) =>
      //TODO: these two cases for callin with empty stack only seem to be used by SootUtilsTest
      val m: Iterable[MethodLoc] = wrapper.findMethodLoc(fmwClazz, fmwName)
      assert(m.toList.size < 2, "Wrong number of methods found")
      m.flatMap(m2 =>
        wrapper.appCallSites(m2,resolver).map(v => v.copy(isPre = true)))
    case (GroupedCallinMethodInvoke(fmwClazzs, fmwName),Nil) =>
      val m: Iterable[MethodLoc] = fmwClazzs.flatMap(c => wrapper.findMethodLoc(c, fmwName))
      assert(m.toList.size < 2, "Wrong number of methods found")
      m.flatMap(m2 =>
        wrapper.appCallSites(m2,resolver).map(v => v.copy(isPre = true)))
    case (InternalMethodReturn(_,_,loc), _) =>
      wrapper.makeMethodRetuns(loc)
    case (InternalMethodInvoke(_, _, _), CallStackFrame(_,Some(returnLoc:AppLoc),_)::_) => List(returnLoc)
    case (InternalMethodInvoke(_, _, loc), _) =>
      val locations = wrapper.appCallSites(loc, resolver)
        .filter(loc => !resolver.isFrameworkClass(loc.containingMethod.get.classType))
      locations.map(loc => loc.copy(isPre = true))
    case v =>
      throw new IllegalStateException(s"No predecessor locations for loc: ${v._1} with stack: ${v._2}")
  }
}