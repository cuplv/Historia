package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{Invoke, _}
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState.{I, LSAnyVal}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{ArrayPtEdge, CallStackFrame, FieldPtEdge, LSAny, LSConstConstraint, LSModelVar, LSParamConstraint, LSPure, OutputMode, PrettyPrinting, PureVar, State, StaticPtEdge}
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
  implicit val rw:RW[RelevanceRelation] = RW.merge(macroRW[RelevantMethod.type], macroRW[NotRelevantMethod.type],
    DropHeapCellsMethod.rw)
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
case class DropHeapCellsMethod(names:Set[String]) extends RelevanceRelation {
  override def join(other: RelevanceRelation): RelevanceRelation = other match{
    case DropHeapCellsMethod(otherNames) => DropHeapCellsMethod(names.union(otherNames))
    case RelevantMethod => RelevantMethod
    case NotRelevantMethod => this
  }

  override def applyPrecisionLossForSkip(state: State): State = state.copy(
    heapConstraints = state.heapConstraints.filter{
      case (FieldPtEdge(_,fName),_) => !names.contains(fName)
      case (StaticPtEdge(_,fieldName),_) => !names.contains(fieldName)
      case (ArrayPtEdge(_,_),_) =>
        ???
    }
  )
}
object DropHeapCellsMethod{
  implicit var rw:RW[DropHeapCellsMethod] = macroRW[DropHeapCellsMethod]
}

/**
 * Functions to resolve control flow edges while maintaining context sensitivity.
 */
class ControlFlowResolver[M,C](wrapper:IRWrapper[M,C],
                               resolver: AppCodeResolver,
                               cha: ClassHierarchyConstraints,
                               component: Option[List[String]], config:SymbolicExecutorConfig[M,C]) { //TODO: remove pathMode here
  private implicit val ch = cha
  private val componentR: Option[List[Regex]] = component.map(_.map(_.r))

  def callbackInComponent(loc: Loc): Boolean = loc match {
    case CallbackMethodReturn(_, _, methodLoc, _) =>
      val className = methodLoc.classType
      //componentR.forall(_.exists(r => r.matches(className)))
      componentR match{
        case Some(rList) =>
          rList.exists(r => r.matches(className))
        case None => true
      }
    case _ => throw new IllegalStateException("callbackInComponent should only be called on callback returns")
  }

  def getResolver = resolver
  def getWrapper = wrapper

  def directCallsGraph(loc: MethodLoc): Set[Loc] = {
    val unresolvedTargets = wrapper.makeMethodTargets(loc).map(callee =>
      UnresolvedMethodTarget(callee.classType, callee.simpleName, Set(callee)))
    unresolvedTargets.flatMap(target => resolver.resolveCallLocation(target))
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

  private def fieldCanPt(fr: FieldReference, state: State, tgt:Option[RVal]): Boolean = {
    val fname = fr.name
    val baseLocalType = fr.base.localType
    state.heapConstraints.exists {
      case (FieldPtEdge(p, otherFieldName), matTgt) if fname == otherFieldName =>
        val posLocalTypes = cha.getSubtypesOf(baseLocalType)
        val existsBaseType = posLocalTypes.exists { lt =>
          state.typeConstraints.get(p).forall(_.subtypeOfCanAlias(lt,cha))
        }
        if(existsBaseType){
          (tgt,matTgt) match{
            case (Some(LocalWrapper(_,tgtLocalType)),mt:PureVar) =>
              // Check if local that is assigned to or from can possibly alias materialized heap cell
              val possibleTgtTypes = cha.getSubtypesOf(tgtLocalType)
              val res = state.typeConstraints.get(mt)
                .map(ts => ts.typeSet(cha).exists(v =>possibleTgtTypes.contains(v)))
              res.getOrElse(true)
            case _ => true
          }
        }else false
      case _ => false
    }
  }

  def relevantHeap(m: MethodLoc, state: State): Boolean = {
    def canModifyHeap(c: CmdWrapper): Boolean = c match {
      case AssignCmd(fr: FieldReference, tgt, _) => fieldCanPt(fr, state,Some(tgt))
      case AssignCmd(src, fr: FieldReference, _) => fieldCanPt(fr, state,Some(src))
      case AssignCmd(StaticFieldReference(clazz, name, _), _, _) =>
        val out = state.heapConstraints.contains(StaticPtEdge(clazz, name))
        out //&& !manuallyExcludedStaticField(name) //TODO: remove dbg code

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

    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) =>
      BounderUtil.cmdAtLocationNopIfUnknown(v,wrapper).mkPre)
    BounderUtil.graphExists[CmdWrapper](start = returns,
      next = n =>
        wrapper.commandPredecessors(n).map((v: AppLoc) => BounderUtil.cmdAtLocationNopIfUnknown(v,wrapper).mkPre).toSet,
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

  def relevantTrace(m: MethodLoc, state: State): Boolean = {
    val calls: Set[CallinMethodReturn] = directCallsGraph(m).flatMap {
      case v: CallinMethodReturn =>
        Some(v)
      case _: InternalMethodInvoke => None
      case _: InternalMethodReturn => None
      case v =>
        println(v)
        ???
    }
    // Find any call that matches a spec in the abstract trace
    val relI: Set[(I, List[LSParamConstraint])] = calls.flatMap { call =>
      Set(CIEnter, CIExit).flatMap{ cdir =>
        state.findIFromCurrent(cdir, (call.fmwClazz, call.fmwName))
      }
    }
    //Check if method call can alias all params

    def matchesType(pair: (LSParamConstraint, Option[RVal])):Boolean = pair match{
      case (_,None) => true
      case (_:LSConstConstraint,_) => ???
      case (LSPure(lsV:PureVar), Some(LocalWrapper(_, localType))) =>
        state.typeConstraints.get(lsV).forall{ts =>
          val res = ts.constrainSubtypeOf(localType, cha)
          !res.isEmpty(cha)
        }
      case (LSModelVar(s,t), Some(LocalWrapper(name,localType))) =>
        true //TODO: could make more precise by matching receivers and arg types
      case (LSAny, _) =>
        true

    }
    def relIExistsForCmd(tgt: List[Option[RVal]],inv:Invoke)(implicit ch:ClassHierarchyConstraints):Boolean = {
      val relIHere: Set[(I, List[LSParamConstraint])] = relI.filter{ i =>
        i._1.signatures.matches((inv.targetClass, inv.targetMethod))
      }
      relIHere.exists(v => v match{
        case (_,lsPar) =>
          val zipped: List[(LSParamConstraint, Option[RVal])] = lsPar zip tgt
          val res = zipped.forall(matchesType)
          res
      })
    }

    //TODO remove commented code for test exclusions
    if (relI.nonEmpty) { //&& !testExclusions(relI, m)
      val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) =>
        BounderUtil.cmdAtLocationNopIfUnknown(v,wrapper).mkPre)
      BounderUtil.graphExists[CmdWrapper](start = returns,
        next = n =>
          wrapper.commandPredecessors(n).map((v: AppLoc) =>
            BounderUtil.cmdAtLocationNopIfUnknown(v,wrapper).mkPre).toSet,
        exists = {
          case ReturnCmd(returnVar, loc) => false
          case AssignCmd(target, invCmd: Invoke, loc) =>
            relIExistsForCmd(TransferFunctions.inVarsForCall(loc,wrapper), invCmd)
          case AssignCmd(target, source, loc) => false
          case InvokeCmd(method:Invoke, loc) =>
            relIExistsForCmd(TransferFunctions.inVarsForCall(loc,wrapper), method)
          case If(b, trueLoc, loc) => false
          case NopCmd(loc) => false
          case SwitchCmd(key, targets, loc) => false
          case ThrowCmd(loc) => false
        }
      )
    } else
      false
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
    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) =>
      BounderUtil.cmdAtLocationNopIfUnknown(v,wrapper).mkPre)
    BounderUtil.graphFixpoint[CmdWrapper, Set[String]](start = returns,Set(),Set(),
      next = n => wrapper.commandPredecessors(n).map((v: AppLoc) =>
        BounderUtil.cmdAtLocationNopIfUnknown(v,wrapper).mkPre).toSet,
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
    val returns = wrapper.makeMethodRetuns(m).toSet.map((v: AppLoc) =>
      BounderUtil.cmdAtLocationNopIfUnknown(v,wrapper).mkPre)
    BounderUtil.graphFixpoint[CmdWrapper, Set[String]](start = returns,Set(),Set(),
      next = n => wrapper.commandPredecessors(n).map((v: AppLoc) =>
        BounderUtil.cmdAtLocationNopIfUnknown(v,wrapper).mkPre).toSet,
      comp = (acc,v) => acc ++ modifiedNames(v),
      join = (a,b) => a.union(b)
    ).flatMap{ case (_,v) => v}.toSet
  }
  val callinNames:MethodLoc => Set[String] = Memo.mutableHashMapMemo{iCallinNames}

  def shouldDropMethod(state:State, heapCellsInState: Set[String], callees: Iterable[MethodLoc]):RelevanceRelation = {
    if(false){ //TODO: better lose precision condition
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
      val allHeapCellsThatCouldBeModified = callees.foldLeft(Set[String]()){(acc,v) =>
        val modifiedAndInState = heapNamesModified(v).intersect(heapCellsInState)
        acc.union(modifiedAndInState)}
      DropHeapCellsMethod(allHeapCellsThatCouldBeModified)
    }else{
      RelevantMethod
    }
  }

  def relevantMethodBody(m: MethodLoc, state: State): RelevanceRelation = {
    val fnSet: Set[String] = state.fieldNameSet()
//    val mSet: Set[String] = state.traceMethodSet()
    if (resolver.isFrameworkClass(m.classType)) {
      return NotRelevantMethod // body can only be relevant to app heap or trace if method is in the app
    }

    val allCalls = memoizedallCalls(m) + m
    //TODO: add par back in?
    val traceRelevantCallees = allCalls.filter{ m =>
//      mSet.exists{ci =>
//        val cin: Set[String] = callinNames(m)
//        cin.contains(ci)
//      }
      val ciN = callinNames(m)
      ciN.exists(state.fastIMatches)
    }
    if (traceRelevantCallees.nonEmpty){
      val traceExists = traceRelevantCallees.exists{callee =>
        relevantTrace(callee,state)
      }
      if(traceExists) {
//        println(s"Trace relevant method: $m state: $state")
        return RelevantMethod
      }
    }
    //TODO: add par back in?
    val heapRelevantCallees = allCalls.filter { callee =>
      val hn: Set[String] = heapNamesModified(callee)
      fnSet.exists { fn =>
        hn.contains(fn)
      }
    }
    val heapExists= heapRelevantCallees.exists{ callee => relevantHeap(callee,state)}
    if(heapExists) {
//      println(s"Heap relevant method: $m state: $state")
      // Method may modify a heap cell in the current state
      // We may decide to drop heap cells and skip the method to scale
      shouldDropMethod(state, fnSet, heapRelevantCallees.seq)
    } else{
      NotRelevantMethod
    }


//    callees.par.exists { c =>
//      if (relevantHeap(c, state)) {
////        printCache(s"method: $m calls $c - heap relevant to state: $state")
//        true
//      } else if (relevantTrace(c, state)) {
////        printCache(s"method: $m calls $c trace relevant to state: $state")
//        true
//      } else
//        false
//    }
  }

  def existsIAlias(locals: List[Option[RVal]], dir: MessageType, sig: (String, String), state: State): Boolean = {
    val aliasPos = TransferFunctions.relevantAliases(state, dir, sig)
    aliasPos.exists { aliasPo =>
      (aliasPo zip locals).forall {
        case (LSPure(v: PureVar), Some(local: LocalWrapper)) =>
          state.typeConstraints.get(v).forall(_.subtypeOfCanAlias(local.localType,cha))
        case (LSPure(v: PureVar), Some(NullConst)) => ???
        case (LSPure(v: PureVar), Some(i: IntConst)) => ???
        case (LSPure(v: PureVar), Some(i: StringConst)) => ???
        case _ => true
      }
    }
  }

  def relevantMethod(loc: Loc, state: State): RelevanceRelation = loc match {
    case InternalMethodReturn(_, _, m) =>
      relevantMethodBody(m,state)
    case CallinMethodReturn(_, _) => RelevantMethod
    case CallbackMethodReturn(clazz, name, rloc, Some(retLine)) => {
      val retVars =
        if (rloc.isStatic)
          wrapper.makeMethodRetuns(rloc).map { retloc =>
            wrapper.cmdAtLocation(retloc) match {
              case ReturnCmd(Some(l), loc) => Some(l)
              case _ => None
            }
          } else List(None)
      val iExists = retVars.exists { retVar => //TODO: ==== check types to rule out aliasing of CBEnter/Exit
        val locs: List[Option[RVal]] = retVar :: rloc.getArgs
        val res = existsIAlias(locs, CBExit, (clazz, name), state) ||
          existsIAlias(None :: locs.tail, CBEnter, (clazz, name), state)
        res
      }
      val relevantBody = relevantMethodBody(rloc, state) match{
        case NotRelevantMethod => false
        case DropHeapCellsMethod(_) => true
        case RelevantMethod => true
      }
      if(iExists || relevantBody)
        RelevantMethod
      else
        NotRelevantMethod
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
      val classesToGroup = groups(k).map{
        case CallinMethodReturn(fmwClazz,_) => fmwClazz
        case InternalMethodReturn(clazz,_, _) => clazz
        case SkippedInternalMethodReturn(clazz, name, rel, loc) => clazz
        case v =>
          throw new IllegalStateException(s"${v}")
      }
      groups(k).collectFirst{
        case CallinMethodReturn(_,name) =>
          GroupedCallinMethodReturn(classesToGroup,name)
        case imr@InternalMethodReturn(_,_,_) => imr
        case imr@SkippedInternalMethodReturn(_, _, _, _) => imr
      }.getOrElse(throw new IllegalStateException())
    }
    out
  }
  def resolvePredicessors(loc:Loc, state: State):Iterable[Loc] = (loc,state.callStack) match{
    case (l@AppLoc(_,_,true),_) => {
      //TODO: remove dbg code =====
//      val pp = new PrettyPrinting(config.outputMode)
//      pp.dotMethod(loc,this, "/Users/shawnmeier/Documents/source/bounder/experiments/inspectRun/itkach.aard2/itkach.slob.Slob$4/method.dot")

      //end remove dbg code
      val cmd: CmdWrapper = wrapper.cmdAtLocation(l)
      cmd match {
        case cmd if wrapper.isMethodEntry(cmd) =>
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
          val unresolvedTargets: UnresolvedMethodTarget =
            wrapper.makeInvokeTargets(loc)
          val resolved: Set[Loc] = resolver.resolveCallLocation(unresolvedTargets)
          val resolvedSkipIrrelevant = resolved.par.map{m => (relevantMethod(m,state),m) match{
            case (RelevantMethod,_) => m
            case (NotRelevantMethod, InternalMethodReturn(clazz, name, loc)) =>
              SkippedInternalMethodReturn(clazz, name,NotRelevantMethod,loc)
            case (d:DropHeapCellsMethod, InternalMethodReturn(clazz, name, loc)) =>
              SkippedInternalMethodReturn(clazz,name,d,loc)
            case v =>
              throw new IllegalStateException(s"$v")
          }}
          val out = mergeEquivalentCallins(resolvedSkipIrrelevant.seq.toSet, state)
          if(out.isEmpty) {
            Scene.v()
            println(s"empty pred location (possible cg unsoundness) loc: $l inMethod: ${l.method}")
            //throw QueryInterruptedException(Set(),"cgunsound")
          }
          out
        }
        case AssignCmd(tgt:LocalWrapper, _:Invoke,loc) => {
          val unresolvedTargets =
            wrapper.makeInvokeTargets(loc)
          val resolved = resolver.resolveCallLocation(unresolvedTargets)
          val resolvedSkipIrrelevant = resolved.par.map{m => (relevantMethod(m,state),m) match{
            case (RelevantMethod,_) => m
            case (NotRelevantMethod, InternalMethodReturn(_, _, _)) if state.containsLocal(tgt) =>
              // don't skip method if return value is materialized
              m
            case (NotRelevantMethod, InternalMethodReturn(clazz, name, loc)) =>
              SkippedInternalMethodReturn(clazz, name,NotRelevantMethod,loc)
            case (d:DropHeapCellsMethod, InternalMethodReturn(clazz, name, loc)) =>
              SkippedInternalMethodReturn(clazz,name,d,loc)
            case _ => throw new IllegalStateException("")
          }}
          val out: Set[Loc] = mergeEquivalentCallins(resolvedSkipIrrelevant.seq.toSet, state)
          if(out.isEmpty) {
            Scene.v()
            println(s"empty pred location (possible cg unsoundness) $l inMethod: ${l.method}")
            //throw QueryInterruptedException(Set(),"cgunsound")
          }
          out
        }
        case AssignCmd(tgt, inv:Invoke,_) =>
          throw new IllegalStateException(s"Invoke cmd assigns to non-local: $tgt  invoke: $inv")
        case _ => List(l.copy(isPre=true))
      }
    }
    case (SkippedInternalMethodReturn(clazz,name,_,loc),_) =>
      List(SkippedInternalMethodInvoke(clazz,name,loc))
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
      val res2 = componentFiltered.filter{m => relevantMethod(m,state) match{
        case RelevantMethod => true
        case DropHeapCellsMethod(_) => true
        case NotRelevantMethod => false
      }}
      res2
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
    case (SkippedInternalMethodInvoke(_, _, _), CallStackFrame(_,Some(returnLoc:AppLoc),_)::_) => List(returnLoc)
    case (InternalMethodInvoke(_, _, loc), _) =>
      val locations = wrapper.appCallSites(loc, resolver)
        .filter(loc => !resolver.isFrameworkClass(loc.containingMethod.get.classType))
      locations.map(loc => loc.copy(isPre = true))
    case v =>
      throw new IllegalStateException(s"No predecessor locations for loc: ${v._1} with stack: ${v._2}")
  }
}