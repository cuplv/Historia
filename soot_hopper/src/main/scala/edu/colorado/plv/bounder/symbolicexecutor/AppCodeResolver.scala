package edu.colorado.plv.bounder.symbolicexecutor

import java.util.NoSuchElementException
import better.files.{File, Resource}
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CBEnter, CBExit, CIEnter, CIExit, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, FieldReference, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, IRWrapper, If, InternalMethodInvoke, InternalMethodReturn, Invoke, InvokeCmd, JimpleMethodLoc, LVal, LineLoc, Loc, LocalWrapper, MethodLoc, NopCmd, ReturnCmd, SkippedInternalMethodInvoke, SkippedInternalMethodReturn, SootWrapper, SpecialInvoke, StaticInvoke, SwitchCmd, ThrowCmd, UnresolvedMethodTarget, VirtualInvoke}
import edu.colorado.plv.bounder.lifestate.LifeState.{OAbsMsg, Signature}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints

import scala.annotation.tailrec
import scala.collection.BitSet
import scala.io.Source
import scala.util.matching.Regex
import scala.util.Random

trait AppCodeResolver {
  def isFrameworkClass(packageName: String): Boolean

  def isAppClass(fullClassName: String): Boolean

  def resolveCallLocation(tgt: UnresolvedMethodTarget): Set[Loc]

  def resolveCallbackExit(method: MethodLoc, retCmdLoc: Option[LineLoc]): Option[Loc]

  def resolveCallbackEntry(method: MethodLoc): Option[Loc]

  def getCallbacks: Set[MethodLoc]

  def nullValueMayFlowTo[M,C](sources: Iterable[AppLoc],
                         cfRes: ControlFlowResolver[M, C]): Set[AppLoc]
}
object FrameworkExtensions{
  private val urlPos = List("FrameworkExtensions.txt",
    "/Resources/FrameworkExtensions.txt",
    "Resources/FrameworkExtensions.txt")
  private val frameworkExtPaths: Seq[String] = urlPos.flatMap{ p =>
    try {
      Some(Resource.getUrl(p).getPath)
    }catch {
      case _:Throwable=>
        None
    }
  }
  val extensionStrings: List[String] = SootWrapper.cgEntryPointName::
    urlPos.flatMap{ (frameworkExtPath:String) =>
//    val source = Source.fromFile(frameworkExtPath)
    try {
      val source = Resource.getAsString(frameworkExtPath)
      Some(source.split("\n").toList)
    }catch{
      case _:Throwable => None
    }
  }.head

  val extensionRegex: Regex = extensionStrings.mkString("|").r
}

class DefaultAppCodeResolver[M,C] (ir: IRWrapper[M,C]) extends AppCodeResolver {

  protected val excludedClasses = "dummyMainClass".r

  var appMethods = ir.getAllMethods.filter(m => !isFrameworkClass(m.classType)).toSet
  private def iGetCallbacks():Set[MethodLoc] = appMethods.filter(resolveCallbackEntry(_).isDefined)
  private var callbacks:Set[MethodLoc] = iGetCallbacks()
  override def getCallbacks:Set[MethodLoc] = callbacks
  def invalidateCallbacks() = {
    appMethods = ir.getAllMethods.filter(m => !isFrameworkClass(m.classType)).toSet
    callbacks = iGetCallbacks()
  }




  /**
   * TODO: not fully implemented
   * Compute null data flows within a single callback.
   * Warning: not a sound analysis, just best effort
   * @param sources Locations returning the values of interest
   * @param condition Condition to yield location that data flows to (e.g. value may be null)
   * @param cfRes Control flow resolver
   * @return
   */
  override def nullValueMayFlowTo[M,C](sources:Iterable[AppLoc],
                                         cfRes:ControlFlowResolver[M,C]):Set[AppLoc] = {

    def mk(v:Any):ValueSpot = v match{
      case LocalWrapper(name, _) => LocalValue(name)
    }
    sealed trait ValueSpot  //note extend further for fields arrays etc if soundness is desired later
    case class LocalValue(name:String) extends ValueSpot
    type AbsState = Map[ValueSpot,Boolean]
    val botVal:AbsState = Map.empty
    def isSensitive(loc:AppLoc, absState:AbsState):Boolean = {
      ir.cmdAtLocation(loc) match {
        case ReturnCmd(returnVar, loc) => false
        case AssignCmd(target, FieldReference(base,_,_,_), loc) =>
          absState.contains(mk(base))
        case AssignCmd(target, source, loc) => false
        case InvokeCmd(_:StaticInvoke, _) => false //TODO: capture @NonNull annotations
        case InvokeCmd(SpecialInvoke(base,_,_,_),_) =>
          absState.contains(mk(base))
        case InvokeCmd(VirtualInvoke(base,_,_,_),_) =>
          absState.contains(mk(base))
        case If(b, trueLoc, loc) => false
        case NopCmd(loc) => false
        case SwitchCmd(key, targets, loc) => false
        case ThrowCmd(loc) => false
      }
    }
    def mkInitFlow(loc:AppLoc):AbsState = BounderUtil.cmdAtLocationNopIfUnknown(loc,ir) match {
      case AssignCmd(tgt, _,_) => Map(mk(tgt) -> true)
      case _ => Map.empty
    }
    def transfer(absState:AbsState,loc:Loc):AbsState = loc match {
      case appLoc@AppLoc(method, line, true) =>
        val cmd = ir.cmdAtLocation(appLoc)
        ???
      case appLoc@AppLoc(_,_,false) => absState
      case InternalMethodReturn(clazz, name, loc) =>
        ???
      case InternalMethodInvoke(clazz, name, loc) =>
        ???
      case CallinMethodReturn(sig) =>
        absState //Note: if we wanted this to be sound, we would capture case where callin causes data flow
      case CallinMethodInvoke(sig) =>
        absState
      case GroupedCallinMethodInvoke(targetClasses, fmwName) => absState
      case GroupedCallinMethodReturn(targetClasses, fmwName) => absState
      case CallbackMethodInvoke(sig, loc) => botVal
      case CallbackMethodReturn(sig, loc, line) => botVal
      case SkippedInternalMethodInvoke(clazz, name, loc) => throw new IllegalArgumentException()
      case SkippedInternalMethodReturn(clazz, name, rel, loc) => throw new IllegalArgumentException()
    }

    def join(absState1: AbsState, absState2:AbsState):AbsState =
      absState1.foldLeft(absState2){
        case (acc,k->v) => acc + (k -> (v || acc.getOrElse(k,false)))
      }

    // accumulator BitSet is set of positions with data flow
    // position 0 is output (value assigned such as x in x = f.y, y is position 1 etc).
    // TODO: may be nice to have interproc version of this
    val fp: Map[Loc, AbsState] = BounderUtil.graphFixpoint[Loc, AbsState](
      start = sources.toSet,
      startVal = sources.flatMap(mkInitFlow).toMap,
      botVal = Map.empty,
      next = n => cfRes.resolveSuccessors(n,skipCallins = true),
      //          ir.commandPredecessors(n).map{v => BounderUtil.cmdAtLocationNopIfUnknown(v,ir).mkPre}.toSet
      comp = transfer,
      join = join
    )
    fp.flatMap{
      case (loc:AppLoc,absState) =>
        if(isSensitive(loc,absState)) Some(loc) else None
      case _ => None
    }.toSet

  }
  final def findCallinsAndCallbacks(messages:Set[OAbsMsg],
                                    packageFilter:Option[String]):Set[(AppLoc,OAbsMsg)] = {
    implicit val ch = ir.getClassHierarchyConstraints
    if(messages.exists{m => m.mt == CBEnter || m.mt == CBExit})
      ??? //TODO: unimplemented, add callback and callin search
    val cbMsg = messages.filter{m => m.mt == CIExit || m.mt == CIEnter}
    def matchesCI(i:Invoke):Option[OAbsMsg] = {
      val sig = i.targetSignature
      cbMsg.find{oMsg =>
        List(CIEnter,CIExit).exists{mt => oMsg.contains(mt, sig)}
      }
    }
    val filteredAppMethods = appMethods.filter {
      case methodLoc: MethodLoc => // apply package filter if it exists
        packageFilter.forall(methodLoc.classType.startsWith)
    }
    val invokeCmds = filteredAppMethods.flatMap{m =>
      ir.allMethodLocations(m).flatMap{v => BounderUtil.cmdAtLocationNopIfUnknown(v,ir) match{
        case AssignCmd(_, i: SpecialInvoke, _) => matchesCI(i).map((v, _))
        case AssignCmd(_, i: VirtualInvoke, _) => matchesCI(i).map((v, _))
        case InvokeCmd(i: SpecialInvoke, _) => matchesCI(i).map((v, _))
        case InvokeCmd(i: VirtualInvoke, _) => matchesCI(i).map((v, _))
        case _ => None
      }}
    }

//    val returns = filteredAppMethods.flatMap{m =>
//      ir.makeMethodRetuns(m).toSet.map((v: AppLoc) => BounderUtil.cmdAtLocationNopIfUnknown(v,ir).mkPre)}
//    val invokeCmds2 = BounderUtil.graphFixpoint[CmdWrapper, Set[(AppLoc,OAbsMsg)]](start = returns, Set(), Set(),
//      next = n => ir.commandPredecessors(n).map((v: AppLoc) =>
//        BounderUtil.cmdAtLocationNopIfUnknown(v, ir).mkPre).toSet,
//      comp = {
//        case (acc, v) =>
//          val newLocs: Set[(AppLoc,OAbsMsg)] = ir.commandPredecessors(v).flatMap { v =>
//            ir.cmdAtLocation(v) match {
//              case AssignCmd(_, i: SpecialInvoke, _) => matchesCI(i).map((v,_))
//              case AssignCmd(_, i: VirtualInvoke, _) => matchesCI(i).map((v,_))
//              case InvokeCmd(i: SpecialInvoke, _) => matchesCI(i).map((v,_))
//              case InvokeCmd(i: VirtualInvoke, _) => matchesCI(i).map((v,_))
//              case _ => None
//            }
//          }.toSet
//          acc ++ newLocs
//      },
//      join = (a, b) => a.union(b)
//    ).flatMap { case (_, v) => v }.toSet
    invokeCmds
  }
  @tailrec
  final def sampleDeref(packageFilter:Option[String]):AppLoc = {
    def keepI(i:Invoke):Boolean = i match {
      case VirtualInvoke(_, _, targetMethod, _) => !targetMethod.contains("<init>")
      case SpecialInvoke(_, _, targetMethod, _) => !targetMethod.contains("<init>")
      case StaticInvoke(_, targetMethod, _) =>  !targetMethod.contains("<init>")
    }
    val filteredAppMethods = appMethods.filter{
      case methodLoc: MethodLoc => // apply package filter if it exists
        packageFilter.forall(methodLoc.classType.startsWith)
    }.toArray
    val methodInd = Random.nextInt(filteredAppMethods.size)
    val m = filteredAppMethods(methodInd)
//    val randomMethodList = Random.shuffle(appMethods.filter{
//      case methodLoc: MethodLoc => // apply package filter if it exists
//        packageFilter.forall(methodLoc.classType.startsWith)
//    }.toList)
//    val m = randomMethodList.head

    // generate set of dereferences for method

    val returns = ir.makeMethodRetuns(m).toSet.map((v: AppLoc) => BounderUtil.cmdAtLocationNopIfUnknown(v,ir).mkPre)
    val derefs = BounderUtil.graphFixpoint[CmdWrapper, Set[AppLoc]](start = returns,Set(),Set(),
      next = n => ir.commandPredecessors(n).map((v: AppLoc) =>
        BounderUtil.cmdAtLocationNopIfUnknown(v,ir).mkPre).toSet,
      comp = {
        case (acc,v) =>
          val newLocs:Set[AppLoc] = ir.commandPredecessors(v).flatMap{v => ir.cmdAtLocation(v) match{
            case AssignCmd(_, i:SpecialInvoke, _) if keepI(i) => Some(v)
            case AssignCmd(_, i:VirtualInvoke, _) if keepI(i) => Some(v)
            case AssignCmd(_, i:FieldReference, _) => Some(v)
            case InvokeCmd(i:SpecialInvoke, _) if keepI(i) => Some(v)
            case InvokeCmd(i:VirtualInvoke,_) if keepI(i) => Some(v)
            case _ => None
          }}.toSet
          acc ++ newLocs
      },
      join = (a,b) => a.union(b)
    ).flatMap{ case (_,v) => v}.toSet.toList
    if(derefs.isEmpty){
      sampleDeref(packageFilter)
    }else {
      val shuf = Random.shuffle(derefs)
      val s = shuf.head
      if(s.line.lineNumber > 0)
        s
      else
        sampleDeref(packageFilter)
    }
  }

  def isFrameworkClass(fullClassName:String):Boolean = fullClassName match{
    case FrameworkExtensions.extensionRegex() =>
      true
    case _ =>
      false
  }

  def isAppClass(fullClassName:String):Boolean = {
    if(isFrameworkClass(fullClassName))
      return false
    fullClassName match{
      case excludedClasses() =>
        false
      case _ => true
    }
  }


  override def resolveCallLocation(tgt: UnresolvedMethodTarget): Set[Loc] = {
    tgt.loc.map{m =>
      val classType = m.classType
      if(isFrameworkClass(classType)){
        CallinMethodReturn(Signature(classType, m.simpleName))
      }else {
        InternalMethodReturn(classType, m.simpleName, m)
      }
    }
  }

  private val CLINIT = "void <clinit>()"
  override def resolveCallbackExit(method: MethodLoc, retCmdLoc: Option[LineLoc]): Option[Loc] = {
//    if(method.simpleName == CLINIT){
//      return Some(CallbackMethodReturn(method.classType, CLINIT,method, retCmdLoc))
//    }
    val overrides = ir.getOverrideChain(method)
    if(overrides.size == 1 && overrides.last.classType == "java.lang.Object" && overrides.last.simpleName == "<init>"){
      // Object init is not considered a callback
      return None
    }
    if (overrides.size > 0) {
      val leastPrecise: MethodLoc = overrides.last
      Some(CallbackMethodReturn(Signature(method.classType, leastPrecise.simpleName), method, retCmdLoc))
    } else None

  }
  override def resolveCallbackEntry(method:MethodLoc):Option[Loc] = {
//    if(method.simpleName == "void <clinit>()"){
//      // <clinit> considered a callback
//      return Some(CallbackMethodInvoke("java.lang.Object", "void <clinit>()", method))
//    }
    if(method.isInterface)
      return None // Interface methods cannot be callbacks
    val overrides = ir.getOverrideChain(method).filter(c =>
      isFrameworkClass(
        SootWrapper.stringNameOfClass(
          c.asInstanceOf[JimpleMethodLoc].method.getDeclaringClass)))
    if(overrides.size == 1 && overrides.last.classType == "java.lang.Object" && overrides.last.simpleName == "<init>"){
      // Object init is not considered a callback unless it overrides a subclass's init
      return None
    }
    if (overrides.size > 0) {
      val leastPrecise: MethodLoc = overrides.last
//      Some(CallbackMethodInvoke(leastPrecise.classType, leastPrecise.simpleName, method))
      Some(CallbackMethodInvoke(Signature(method.classType, leastPrecise.simpleName), method))
    } else None
  }
}