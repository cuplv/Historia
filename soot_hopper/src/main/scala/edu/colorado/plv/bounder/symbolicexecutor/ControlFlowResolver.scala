package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.EmptyTypeSet.intersect
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecSpace}
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, OAbsMsg, Signature}
import edu.colorado.plv.bounder.lifestate.SpecSpace.allI
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, EncodingTools}
import edu.colorado.plv.bounder.symbolicexecutor.state.{ArrayPtEdge, CallStackFrame, ClassVal, FieldPtEdge, IntVal, NullVal, PureExpr, PureVar, State, StaticPtEdge, StringVal, TopVal}
import scalaz.Memo
import soot.Scene
import upickle.default.{macroRW, ReadWriter => RW}

import scala.collection.mutable
import scala.collection.parallel.CollectionConverters.ImmutableIterableIsParallelizable
import scala.collection.parallel.immutable.ParIterable
import scala.util.matching.Regex
sealed trait RelevanceRelation{
  def join(other: RelevanceRelation):RelevanceRelation
  def applyPrecisionLossForSkip(state:State):State
}
object RelevanceRelation{
  implicit val rw:RW[RelevanceRelation] = RW.merge(macroRW[RelevantMethod.type], macroRW[NotRelevantMethod.type])
}
case object RelevantMethod extends RelevanceRelation {
  override def join(other: RelevanceRelation): RelevanceRelation = RelevantMethod

  override def applyPrecisionLossForSkip(state: State): State =
    throw new IllegalStateException("No precision loss for relevant method.")
}
case object NotRelevantMethod extends RelevanceRelation {
  override def join(other: RelevanceRelation): RelevanceRelation = other

  override def applyPrecisionLossForSkip(state: State): State = state
}

/**
 * Functions to resolve control flow edges while maintaining context sensitivity.
 */
class ControlFlowResolver[M,C](wrapper:IRWrapper[M,C],
                               resolver: AppCodeResolver,
                               cha: ClassHierarchyConstraints,
                               component: Option[List[String]], config:ExecutorConfig[M,C]) { //TODO: remove pathMode here
  private implicit val ch = cha
  private val componentR: Option[List[Regex]] = component.map(_.map(_.r))
  private val specSpace: SpecSpace = config.specSpace

  //private val messageToCallback:Map[OAbsMsg, ]

  /**
   * Get a mapping from points to messages to arg number and abstract message.
   *
   * @param msgs set of messages that may be used by the specification
   * @return the mapping
   */
  def ptsToMsgs(msgs: Set[OAbsMsg]): Set[(OAbsMsg, List[TypeSet])] = {
    resolver.getCallbacks.flatMap { cb =>

      val ret = wrapper.makeMethodRetuns(cb)
      val cbSig = cb.getSignature
      val matchedCB = msgs.filter(absMsg => List(CBEnter, CBExit).exists(absMsg.contains(_, cbSig)))

      // Get pts to regions for cb return var Empty if void
      val retPts = ret.map(r => wrapper.cmdAtLocation(r) match {
        case ReturnCmd(Some(returnVar: LocalWrapper), loc) => wrapper.pointsToSet(cb, returnVar)
        case ReturnCmd(None, loc) => EmptyTypeSet
        case otherCmd => throw new IllegalStateException(s"Cannot have non-return cmd as return location: $otherCmd")
      }).foldLeft(EmptyTypeSet: TypeSet) {
        case (acc, v) => acc.union(v)
      }

      // Get pts to regions for args of cb empty if static
      val argPts = cb.getArgs.map(_.map(wrapper.pointsToSet(cb, _)).getOrElse(EmptyTypeSet))

      val allMethodsCalled = allCallsApp(cb) + cb
      val callins_ = allMethodsCalled.flatMap(callinNamesAndPts)
      val callins = callins_.flatMap { ci =>
        msgs.filter { absMsg =>
          absMsg.contains(CIExit, ci._1)
        }.map(absMsg => (absMsg, ci._2))
      }

      val callbacks = matchedCB.map(absMsg => (absMsg, retPts :: argPts))

      callins ++ callbacks
    }
  }

  def callbackInComponent(loc: Loc): Boolean = loc match {
    case CallbackMethodReturn(_, methodLoc, _) =>
      val className = methodLoc.classType
      //componentR.forall(_.exists(r => r.matches(className)))
      componentR match {
        case Some(rList) =>
          rList.exists(r => r.matches(className))
        case None => true
      }
    case _ => throw new IllegalStateException("callbackInComponent should only be called on callback returns")
  }

  def getWrapper = wrapper

  def directCallsGraph(loc: MethodLoc): Set[Loc] = {
    val unresolvedTargets = wrapper.makeMethodTargets(loc).map(callee =>
      UnresolvedMethodTarget(callee.classType, callee.simpleName, Set(callee)))
    unresolvedTargets.flatMap(target => resolver.resolveCallLocation(target))
  }


  var printCacheCache = mutable.Set[String]()

  /**
   * Debug function that only prints any given string once
   *
   * @param s string to print
   */
  def printCache(s: String): Unit = {
    if (!printCacheCache.contains(s)) {
      println(s)
      printCacheCache.add(s)
    }
  }

  private def callsToRetLoc(loc: MethodLoc, includeCallin: Boolean): Set[MethodLoc] = {
    val directCalls = directCallsGraph(loc)
    val internalCalls = directCalls.flatMap {
      case InternalMethodReturn(_, _, oloc) =>
        // We only care about direct calls, calls through framework are considered callbacks
        if (!resolver.isFrameworkClass(oloc.classType))
          Some(oloc)
        else if (includeCallin) Some(oloc) else None
      case CallinMethodReturn(sig) if includeCallin =>
        val res = wrapper.findMethodLoc(sig)
        res
      case _ =>
        None
    }
    internalCalls
  }

  def computeAllCalls___(loc: MethodLoc, includeCallin: Boolean = false): Set[MethodLoc] = {
    val empty = Set[MethodLoc]()
    val out = BounderUtil.graphFixpoint[MethodLoc, Set[MethodLoc]](Set(loc),
      empty,
      empty,
      next = c => callsToRetLoc(c, includeCallin),
      comp = (_, v) => callsToRetLoc(v, includeCallin),
      join = (a, b) => a.union(b)
    )
    out.flatMap {
      case (k, v) => v
    }.toSet
  }
  def computeAllCalls(loc:MethodLoc, includeCallin:Boolean = false):Set[MethodLoc] = {
     callsToRetLoc(loc, includeCallin)
  }
  def allCallsApp: MethodLoc => Set[MethodLoc] = Memo.mutableHashMapMemo(c => computeAllCalls(c))
  def computeAllCallsTransitive(loc:MethodLoc):Set[MethodLoc] = {
    val calls = mutable.Set[MethodLoc]()
    calls.addAll(allCallsApp(loc))
    var added = true
    while(added){
      val newCalls = calls.flatMap{called => allCallsApp(called)}
      added = newCalls.exists{newCall => !calls.contains(newCall)}
      calls.addAll(newCalls)
    }
    calls.toSet
  }


  def allCallsAppTransitive:MethodLoc => Set[MethodLoc] = Memo.mutableHashMapMemo(computeAllCallsTransitive)

  //  val memoizedallCalls: MethodLoc => Set[MethodLoc]= allCalls
  def upperBoundOfInvoke(i: Invoke): Option[String] = i match {
    case SpecialInvoke(LocalWrapper(_, baseType), _, _, _) => Some(baseType)
    case StaticInvoke(targetClass, _, _) => Some(targetClass)
    case VirtualInvoke(LocalWrapper(_, baseType), _, _, _) => Some(baseType)
  }

  private def fieldCanPt(fr: FieldReference, m: MethodLoc, state: State, tgt: Option[RVal]): Boolean = {
    val fname = fr.name
    val baseLocal = fr.base
    state.heapConstraints.exists {
      case (FieldPtEdge(p, otherFieldName), matTgt) if fname == otherFieldName =>
        val baseLocalPTS = wrapper.pointsToSet(m, baseLocal)
        val existsBaseType =
          state.typeConstraints.get(p).forall { materializedBaseTS =>
            baseLocalPTS.intersectNonEmpty(materializedBaseTS)
          }

        if (existsBaseType) {
          (tgt, matTgt) match {
            case (Some(tgtLocal: LocalWrapper), mt: PureVar) =>
              state.canAlias(mt, m, tgtLocal, wrapper, inCurrentStackFrame = false)
            case _ => true
          }
        } else false
      case _ => false
    }

  }

  def relevantHeap(m: MethodLoc, state: State): Boolean = {
    def canModifyHeap(c: CmdWrapper): Boolean = c match {
      case AssignCmd(fr: FieldReference, tgt, _) =>
        fieldCanPt(fr, m, state, Some(tgt))
      case AssignCmd(src, fr: FieldReference, _) => fieldCanPt(fr, m, state, Some(src))
      case AssignCmd(StaticFieldReference(clazz, name, _), _, _) =>
        val out = state.heapConstraints.contains(StaticPtEdge(clazz, name))
        out //&& !manuallyExcludedStaticField(name) //TODO: remove dbg code

      case AssignCmd(_, StaticFieldReference(clazz, name, _), _) =>
        val out = state.heapConstraints.contains(StaticPtEdge(clazz, name))
        out //&& !manuallyExcludedStaticField(name)
      case _: AssignCmd => false
      case _: ReturnCmd => false
      case _: InvokeCmd => false // This method only counts commands that directly modify the heap
      case _: Goto => false
      case _: NopCmd => false
      case _: ThrowCmd => false
      case _: SwitchCmd => false
    }

    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) =>
      BounderUtil.cmdAtLocationNopIfUnknown(v, wrapper).mkPre)
    BounderUtil.graphExists[CmdWrapper](start = returns,
      next = n =>
        wrapper.commandPredecessors(n).map((v: AppLoc) => BounderUtil.cmdAtLocationNopIfUnknown(v, wrapper).mkPre).toSet,
      exists = canModifyHeap
    )
  }

  //  TODO: manuallyExcluded.* methods are for debugging scalability issues
  //  val excludedCaller =
  //    List(
  //      ".*ItemDescriptionFragment.*",
  //      ".*PlaybackController.*"
  //      ".*PlaybackController.*initServiceNot.*",
  //      ".*PlaybackController.*release.*",
  //      ".*PlaybackController.*bindToService.*",
  //    ).mkString("|").r
  //
  //  val excludedCallee = List(".*PlaybackController.*").mkString("|").r
  //
  //  /**
  //   * Experiment to see if better relevance filtering would improve performance
  //   * @param caller
  //   * @param callee
  //   * @return
  //   */
  //  def manuallyExcludedCallSite(caller:MethodLoc, callee:CallinMethodReturn):Boolean = {
  //    if (excludedCaller.matches(caller.classType + ";" + caller.simpleName)){
  //      printCache(s"excluding $caller calls $callee")
  //      true
  //    }else if (excludedCallee.matches(???)){
  //      printCache(s"excluding $caller calls $callee")
  //      true
  //    }else{
  //      false
  //    }
  //  }
  //  def manuallyExcludedStaticField(fieldName:String):Boolean = {
  //    fieldName == "isRunning"
  //  }

  //  //TODO test method: exclude after testing if itemdescriptionFrag is problem
  //  def testExclusions(relI: Set[(I, List[LSParamConstraint])], m: MethodLoc):Boolean = {
  ////    val exclusions = Set("ItemDescriptionFragment", "PlaybackController")
  ////    val isExcluded = exclusions.exists(v => m.toString.contains(v))
  //    if((!m.toString.contains("ExternalPlayerFragment")) && relI.nonEmpty){
  //      println(s"excluding $m reli: ${relI.map(_._1).mkString(",")}")
  //      true
  //    }else
  //      false
  //  }


  def iHeapNamesModified(m: MethodLoc): Set[String] = {
    def modifiedNames(c: CmdWrapper): Option[String] = c match {
      case AssignCmd(fr: FieldReference, _, _) => Some(fr.name)
      case AssignCmd(_, fr: FieldReference, _) => Some(fr.name)
      case AssignCmd(StaticFieldReference(_, name, _), _, _) => Some(name)
      case AssignCmd(_, StaticFieldReference(_, name, _), _) => Some(name)
      case _: AssignCmd => None
      case _: ReturnCmd => None
      case _: InvokeCmd => None
      case _: Goto => None
      case _: NopCmd => None
      case _: ThrowCmd => None
      case _: SwitchCmd => None
    }

    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) =>
      BounderUtil.cmdAtLocationNopIfUnknown(v, wrapper).mkPre)
    BounderUtil.graphFixpoint[CmdWrapper, Set[String]](start = returns, Set(), Set(),
      next = n => wrapper.commandPredecessors(n).map((v: AppLoc) =>
        BounderUtil.cmdAtLocationNopIfUnknown(v, wrapper).mkPre).toSet,
      comp = (acc, v) => acc ++ modifiedNames(v),
      join = (a, b) => a.union(b)
    ).flatMap { case (_, v) => v }.toSet
  }

  val heapNamesModified: MethodLoc => Set[String] = Memo.mutableHashMapMemo {
    iHeapNamesModified
  }

  def iCallinNamesAndPts(m: MethodLoc): Set[(Signature, List[TypeSet])] = {
    def paramToTypeSet(p: RVal): TypeSet = p match {
      case l: LocalWrapper =>
        wrapper.pointsToSet(m, l)
      case _ =>
        EmptyTypeSet
    }

    def modifiedNames(c: CmdWrapper): Set[(Signature, List[TypeSet])] = c match {
      case AssignCmd(x, i: Invoke, _) => Set((i.targetSignature, paramToTypeSet(x)
        :: i.targetOptional.map(paramToTypeSet).getOrElse(EmptyTypeSet) :: i.params.map(paramToTypeSet)))
      case _: AssignCmd => Set.empty
      case _: ReturnCmd => Set.empty
      case InvokeCmd(i, _) =>
        Set((i.targetSignature, EmptyTypeSet :: i.targetOptional.map(paramToTypeSet).getOrElse(EmptyTypeSet)
          :: i.params.map(paramToTypeSet)))
      case _: Goto => Set.empty
      case _: NopCmd => Set.empty
      case _: ThrowCmd => Set.empty
      case _: SwitchCmd => Set.empty
    }

    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) =>
      BounderUtil.cmdAtLocationNopIfUnknown(v, wrapper).mkPre)
    BounderUtil.graphFixpoint[CmdWrapper, Set[(Signature, List[TypeSet])]](start = returns, Set(), Set(),
      next = n => wrapper.commandPredecessors(n).map((v: AppLoc) =>
        BounderUtil.cmdAtLocationNopIfUnknown(v, wrapper).mkPre).toSet,
      comp = (acc, v) => acc ++ modifiedNames(v),
      join = (a, b) => a.union(b)
    ).flatMap { case (_, v) => v }.toSet
  }

  val callinNamesAndPts: MethodLoc => Set[(Signature, List[TypeSet])] = Memo.mutableHashMapMemo {
    iCallinNamesAndPts
  }

  def iCallinNames(m: MethodLoc): Set[String] = {
    def modifiedNames(c: CmdWrapper): Option[String] = c match {
      case AssignCmd(_, i: Invoke, _) => Some(i.targetSignature.methodSignature)
      case _: AssignCmd => None
      case _: ReturnCmd => None
      case InvokeCmd(i, _) => Some(i.targetSignature.methodSignature)
      case _: Goto => None
      case _: NopCmd => None
      case _: ThrowCmd => None
      case _: SwitchCmd => None
    }

    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) =>
      BounderUtil.cmdAtLocationNopIfUnknown(v, wrapper).mkPre)
    BounderUtil.graphFixpoint[CmdWrapper, Set[String]](start = returns, Set(), Set(),
      next = n => wrapper.commandPredecessors(n).map((v: AppLoc) =>
        BounderUtil.cmdAtLocationNopIfUnknown(v, wrapper).mkPre).toSet,
      comp = (acc, v) => acc ++ modifiedNames(v),
      join = (a, b) => a.union(b)
    ).flatMap { case (_, v) => v }.toSet
  }

  val callinNames: MethodLoc => Set[String] = Memo.mutableHashMapMemo {
    iCallinNames
  }

  def shouldDropMethod(state: State, heapCellsInState: Set[String], callees: Iterable[MethodLoc]): RelevanceRelation = {
    if (false) { //TODO: better lose precision condition
      //    val heapNamesModifiedByCallee =
      //      callees.foldLeft(Set[String]()){(acc,callee) => acc.union(heapNamesModified(callee))}
      //    //pure variables are sequentially instantiated, so a higher pure variable is more removed from query
      //    val smallestPvTouched = state.heapConstraints.foldLeft(Integer.MAX_VALUE){
      //      case (acc, (FieldPtEdge(PureVar(id1), name),PureVar(id2))) if heapNamesModifiedByCallee.contains(name) =>
      //        if(acc > id1 || acc > id2) List(id1,id2).min else acc
      //      case (acc, (FieldPtEdge(PureVar(id1), name),_)) if heapNamesModifiedByCallee.contains(name) =>
      //        if(acc > id1) id1 else acc
      //      case (acc, (StaticPtEdge(_,name), PureVar(pv))) if heapNamesModifiedByCallee.contains(name) =>
      //        if(acc > pv) pv else acc
      //      case (acc,_) => acc
      //    }
      //    if(smallestPvTouched > 3){ //TODO: better lose precision condition
      val allHeapCellsThatCouldBeModified = callees.foldLeft(Set[String]()) { (acc, v) =>
        val modifiedAndInState = heapNamesModified(v).intersect(heapCellsInState)
        acc.union(modifiedAndInState)
      }
      //DropHeapCellsMethod(allHeapCellsThatCouldBeModified)
      ???
    } else {
      RelevantMethod
    }
  }

  def relevantMethodBody(m: MethodLoc, state: State): RelevanceRelation = {
    val fnSet: Set[String] = state.fieldNameSet()
    //    val mSet: Set[String] = state.traceMethodSet()
    if (resolver.isFrameworkClass(m.classType)) {
      return NotRelevantMethod // body can only be relevant to app heap or trace if method is in the app
    }

    val currentCalls = allCallsAppTransitive(m) + m
    val heapRelevantCallees = currentCalls.filter { callee =>
      val hn: Set[String] = heapNamesModified(callee)
      fnSet.exists { fn =>
        hn.contains(fn)
      }
    }
    val heapExists = heapRelevantCallees.exists { callee => relevantHeap(callee, state) }
    if (heapExists) {
      //      println(s"Heap relevant method: $m state: $state")
      // Method may modify a heap cell in the current state
      // We may decide to drop heap cells and skip the method to scale
      shouldDropMethod(state, fnSet, heapRelevantCallees.seq)
    } else {
      NotRelevantMethod
    }
  }

  val allCBIFromSpec = config.specSpace.allI.filter{
    case OAbsMsg(CBEnter, signatures, lsVars) => true
    case OAbsMsg(CBExit, signatures, lsVars) => true
    case _=> false
  }
  //  matches for callback method abstract messages
  val callbackMessage: Map[MethodLoc, Set[(OAbsMsg, List[TypeSet])]] = {
    val callbacks = resolver.getCallbacks
    callbacks.map{callback =>
      val retType:TypeSet = wrapper.makeMethodRetuns(callback).map{ret =>
        wrapper.cmdAtLocation(ret) match {
          case ReturnCmd(Some(returnVar:LocalWrapper),_) => wrapper.pointsToSet(ret.method,returnVar)
          case _:ReturnCmd => TopTypeSet
          case v => throw new IllegalStateException(s"$v is not a return")
        }}.reduceOption((a,b) =>a.union(b)).getOrElse(TopTypeSet)
      val signature = callback.getSignature
      (callback,
      allCBIFromSpec.flatMap{absMsg =>
        if(absMsg.contains(CBEnter, signature) || absMsg.contains(CBExit, signature)){
          Some(absMsg, retType :: callback.getArgs.map{
            case Some(local) => wrapper.pointsToSet(callback, local)
            case None => TopTypeSet
          })
        }else None
      })
    }.toMap
  }

  val allCIIFromSpec = config.specSpace.allI.filter{
    case OAbsMsg(CIEnter, signatures, lsVars) => true
    case OAbsMsg(CIExit, signatures, lsVars) => true
    case _=> false
  }
  def ptsFromRVal(rval:RVal, method:MethodLoc):TypeSet = rval match{
    case l:LocalWrapper => wrapper.pointsToSet(method,l)
    case _ => TopTypeSet
  }
  val transitiveCallinMessage: Map[MethodLoc, Set[(OAbsMsg, List[TypeSet])]] = {
    val appMethods = resolver.appMethods
    val directCalls = appMethods.map{method =>
      val absMsgs = wrapper.allMethodLocations(method).flatMap{ loc =>
        wrapper.cmdAtLocation(loc) match {
          case AssignCmd(assign, i:Invoke, _) =>
            resolver.matchesCI(i,allCIIFromSpec).map{matchedMsg =>
              val assignPts = ptsFromRVal(assign, method)
              val recPts = i.targetOptional.map(rec => ptsFromRVal(rec,method)).getOrElse(TopTypeSet)
              (matchedMsg, assignPts::recPts::(i.params.map(rv => ptsFromRVal(rv,method))))
            }
          case InvokeCmd(i:Invoke, _) =>
            resolver.matchesCI(i, allCIIFromSpec).map { matchedMsg =>
              val recPts = i.targetOptional.map(rec => ptsFromRVal(rec,method)).getOrElse(TopTypeSet)
              (matchedMsg, TopTypeSet::recPts::(i.params.map(rv => ptsFromRVal(rv, method))))
            }
          case _ => None
        }
      }
      (method, absMsgs)
    }.toMap
    directCalls.map{
      case (method, absMsgs) =>
        val allCalls = allCallsAppTransitive(method)
        (method,allCalls.foldLeft(absMsgs){case (acc,v) =>
          acc ++ directCalls.getOrElse(v, Set.empty)
        })
    }
  }

  private def isRelevantI(fromCG: Set[(OAbsMsg, List[TypeSet])],
                        relevantIMsg:Set[OAbsMsg], state:State):RelevanceRelation = {
    if (fromCG.exists {
      case (absMsg, pts) =>
        val ex = relevantIMsg.exists{
          case OAbsMsg(mt,sig, lsVars) if absMsg.mt == mt && absMsg.signatures == sig =>
            lsVars.zip(pts).forall{
              case (v:PureVar, ts) =>
                val out = state.sf.typeConstraints.getOrElse(v,TopTypeSet).intersectNonEmpty(ts)
                out
              case _ => true
            }
          case v => false
        }
        ex
    }) {
      RelevantMethod
    } else {
      NotRelevantMethod
    }
  }
  def relevantMethod(loc: Loc, state: State): RelevanceRelation = {
    val relevantI = EncodingTools.rhsToPred(state.sf.traceAbstraction.rightOfArrow, config.specSpace)
      .flatMap { a => allI(a) }
    loc match {
      case InternalMethodReturn(_, _, m) =>
        relevantMethodBody(m, state).join(
        isRelevantI(transitiveCallinMessage.getOrElse(m,Set.empty), relevantI, state))
      case _: CallinMethodReturn => RelevantMethod
      case CallbackMethodReturn(_, rloc, Some(retLine)) => {
        val relevantCB = isRelevantI(callbackMessage(rloc), relevantI, state)
        val relevantCI = isRelevantI(transitiveCallinMessage.getOrElse(rloc,Set.empty), relevantI, state)
        val relevantBody = relevantMethodBody(rloc, state)
        val res = relevantCB.join(relevantCI).join(relevantBody)
        res
      }
      case _ => throw new IllegalStateException("relevantMethod only for method returns")
    }
  }

  // Callins are equivalent if they match the same set of I predicates in the abstract trace
  def mergeEquivalentCallins(callins: Set[Loc], state: State): Set[Loc] ={
    val groups: Map[Object, Set[Loc]] = callins.groupBy{
      case CallinMethodReturn(sig) =>
        specSpace.findIFromCurrent(CIExit,sig)
      case i => i
    }
    val out:Set[Loc] = groups.keySet.map{k =>
      val classesToGroup = groups(k).map{
        case CallinMethodReturn(sig) => sig.base
        case InternalMethodReturn(clazz,_, _) => clazz
        case SkippedInternalMethodReturn(clazz, name, rel, loc) => clazz
        case v =>
          throw new IllegalStateException(s"${v}")
      }
      groups(k).collectFirst{
        case CallinMethodReturn(sig) =>
          GroupedCallinMethodReturn(classesToGroup,sig.methodSignature)
        case imr@InternalMethodReturn(_,_,_) => imr
        case imr@SkippedInternalMethodReturn(_, _, _, _) => imr
      }.getOrElse(throw new IllegalStateException())
    }
    out
  }

  private def methodRetToEntry(loc:Loc):Loc = loc match {
    case AppLoc(method, line, isPre) => ???
    case CallinMethodReturn(sig) => CallinMethodInvoke(sig)
    case CallinMethodInvoke(sig) => ???
    case GroupedCallinMethodInvoke(targetClasses, fmwName) => ???
    case GroupedCallinMethodReturn(targetClasses, fmwName) => GroupedCallinMethodInvoke(targetClasses, fmwName)
    case CallbackMethodInvoke(sig, loc) => ???
    case CallbackMethodReturn(sig, loc, line) => CallbackMethodInvoke(sig,loc)
    case InternalMethodInvoke(clazz, name, loc) => ???
    case InternalMethodReturn(clazz, name, loc) => InternalMethodInvoke(clazz, name, loc)
    case SkippedInternalMethodInvoke(clazz, name, loc) => ???
    case SkippedInternalMethodReturn(clazz, name, rel, loc) => SkippedInternalMethodInvoke(clazz,name,loc)
  }

  /**
   * TODO: this function is not complete yet, only used for partially implemented feature
   * @param loc
   * @param skipCallins
   * @return
   */
  def resolveSuccessors(loc:Loc, skipCallins:Boolean):Iterable[Loc] = loc match {
    case l@AppLoc(_,_,false) =>
      val cmd:CmdWrapper = wrapper.cmdAtLocation(l)
      cmd match{
        case ReturnCmd(_,loc) => wrapper.appCallSites(loc.method,resolver)
        case _ => wrapper.commandNext(cmd)
      }

    case l@AppLoc(_,_,true) =>
      val cmd:CmdWrapper = wrapper.cmdAtLocation(l)

      def handleInvoke(): Iterable[Loc] = {
        val unresolvedTargets = wrapper.makeInvokeTargets(l)
        val resolved: Set[Loc] = resolver.resolveCallLocation(unresolvedTargets)
        resolved.map(methodRetToEntry).flatMap {
          case _: CallinMethodInvoke if skipCallins => List(l.copy(isPre = false))
          case v => Some(v)
        }
      }

      val res = cmd match {
        case InvokeCmd(method, loc) => handleInvoke()
        case AssignCmd(target, _: Invoke, loc) => handleInvoke()
        case _ =>
          List(l.copy(isPre = false))
      }
      res
    case InternalMethodInvoke(clazz,name,loc) =>
      ???
    case InternalMethodReturn(clazz, name, loc) =>
      ???
    case CallinMethodInvoke(sig) => List(CallinMethodReturn(sig))
    case other =>
      println(other)
      ???
  }
  def resolvePredicessors(loc:Loc, state: State):Iterable[Loc] = (loc,state.callStack) match{
    case (l@AppLoc(_,_,true),_) => {
      val cmd: CmdWrapper = wrapper.cmdAtLocation(l)
      cmd match {
        case cmd if l.line.isFirstLocInMethod =>
          val methodEntries = BounderUtil.resolveMethodEntryForAppLoc(resolver,l )
          val out = methodEntries.filter(state.entryPossible)
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
          val unresolvedTargets = wrapper.makeInvokeTargets(loc)
          val resolved: Set[Loc] = resolver.resolveCallLocation(unresolvedTargets)
          val resolvedSkipIrrelevant = resolved.par.map{m => (relevantMethod(m,state),m) match{
            case (_,InternalMethodReturn(clazz, name, loc)) if m.containingMethod.exists(_.isNative()) =>
              SkippedInternalMethodReturn(clazz, name,NotRelevantMethod,loc)
            case (RelevantMethod,_) => m
            case (NotRelevantMethod, InternalMethodReturn(clazz, name, loc)) =>
              SkippedInternalMethodReturn(clazz, name,NotRelevantMethod,loc)
            case v => throw new IllegalStateException(s"$v")
          }}
          val out = mergeEquivalentCallins(resolvedSkipIrrelevant.seq.toSet, state)
          out
        }
        case AssignCmd(tgt:LocalWrapper, _:Invoke,loc) => {
          val unresolvedTargets = wrapper.makeInvokeTargets(loc)
          val resolved = resolver.resolveCallLocation(unresolvedTargets)
          val resolvedSkipIrrelevant = resolved.par.map{m => (relevantMethod(m,state),m) match{
            case (_, InternalMethodReturn(clazz, name, loc)) if m.containingMethod.exists(_.isNative()) =>
              SkippedInternalMethodReturn(clazz, name, NotRelevantMethod, loc)
            case (RelevantMethod,_) => m
            case (NotRelevantMethod, InternalMethodReturn(_, _, _)) if state.containsLocal(tgt) =>
              // don't skip method if return value is materialized
              m
            case (NotRelevantMethod, InternalMethodReturn(clazz, name, loc)) =>
              SkippedInternalMethodReturn(clazz, name,NotRelevantMethod,loc)
            case v => throw new IllegalStateException(s"$v")
          }}
          val out: Set[Loc] = mergeEquivalentCallins(resolvedSkipIrrelevant.seq.toSet, state)
          out
        }
        case AssignCmd(tgt, inv:Invoke,_) =>
          throw new IllegalStateException(s"Invoke cmd assigns to non-local: $tgt  invoke: $inv")
        case _ => List(l.copy(isPre=true))
      }
    }
    case (SkippedInternalMethodReturn(clazz,name,_,loc),_) =>
      List(SkippedInternalMethodInvoke(clazz,name,loc))
    case (CallinMethodReturn(sig),_) =>
      // TODO: nested callbacks not currently handled
      List(CallinMethodInvoke(sig))
    case (GroupedCallinMethodReturn(classes, name),_) =>
      // TODO: nested callbacks not currently handled
      List(GroupedCallinMethodInvoke(classes, name))
    case (_:CallinMethodInvoke, CallStackFrame(_,Some(returnLoc@AppLoc(_,_,true)),_)::_) =>
      List(returnLoc)
    case (GroupedCallinMethodInvoke(_,_),CallStackFrame(_,Some(returnLoc@AppLoc(_,_,true)),_)::_) =>
      List(returnLoc)
    case (_:CallbackMethodInvoke, _) =>
      val callbacks = resolver.getCallbacks
      val res: Seq[Loc] = callbacks.flatMap(callback => {
        val locCb = wrapper.makeMethodRetuns(callback)
        locCb.flatMap{case AppLoc(method,line,_) => resolver.resolveCallbackExit(method, Some(line))}
      }).toList
      val componentFiltered = res.filter(callbackInComponent)
      // filter for callbacks that may affect current state
      val res2 = componentFiltered.filter{m => relevantMethod(m,state) match{
        case RelevantMethod => true
        case NotRelevantMethod => false
      }}
      //TODO: check this
      res2
    case (CallbackMethodReturn(_, loc, Some(line)),_) =>
      AppLoc(loc, line, isPre = false)::Nil
    case (CallinMethodInvoke(sig),Nil) =>
      //TODO: these two cases for callin with empty stack only seem to be used by SootUtilsTest
      val m: Iterable[MethodLoc] = wrapper.findMethodLoc(sig)
      assert(m.toList.size < 2, "Wrong number of methods found")
      m.flatMap(m2 =>
        wrapper.appCallSites(m2,resolver).map(v => v.copy(isPre = true)))
    case (GroupedCallinMethodInvoke(fmwClazzs, fmwName),Nil) =>
      val m: Iterable[MethodLoc] = fmwClazzs.flatMap(c => wrapper.findMethodLoc(Signature(c, fmwName)))
      assert(m.toList.size < 2, "Wrong number of methods found")
      m.flatMap(m2 =>
        wrapper.appCallSites(m2,resolver).map(v => v.copy(isPre = true)))
    case (InternalMethodReturn(_,_,loc), _) =>
      wrapper.makeMethodRetuns(loc)
    case (InternalMethodInvoke(_, _, _), CallStackFrame(_,Some(returnLoc:AppLoc),_)::_) => List(returnLoc)
    case (SkippedInternalMethodInvoke(_, _, _), CallStackFrame(_,Some(returnLoc:AppLoc),_)::_) => List(returnLoc)
    case (InternalMethodInvoke(_, _, loc), _) =>
      val locations = wrapper.appCallSites(loc, resolver)
        .filter(loc => !resolver.isFrameworkClass(loc.containingMethod.get.classType))
      locations.map(loc => loc.copy(isPre = true))
    case v =>
      throw new IllegalStateException(s"No predecessor locations for loc: ${v._1} with stack: ${v._2}")
  }
}