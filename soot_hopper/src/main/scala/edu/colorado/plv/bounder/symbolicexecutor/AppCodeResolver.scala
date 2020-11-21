package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodReturn, IRWrapper, InternalMethodReturn, JimpleFlowdroidWrapper, JimpleMethodLoc, LineLoc, Loc, MethodLoc, UnresolvedMethodTarget}

import scala.io.Source
import scala.util.matching.Regex

trait AppCodeResolver {
  def isFrameworkClass(packageName:String):Boolean
  def resolveCallLocation(tgt : UnresolvedMethodTarget): Loc
  def resolveCallbackExit(method : MethodLoc, retCmdLoc: Option[LineLoc]):Option[Loc]
  def resolveCallbackEntry(method: MethodLoc):Option[Loc]
  def getCallbacks: Set[MethodLoc]
}

class DefaultAppCodeResolver[M,C] (ir: IRWrapper[M,C]) extends AppCodeResolver {
  protected val frameworkExtPath = getClass.getResource("/FrameworkExtensions.txt").getPath
  protected val extensionStrings: Regex = Source.fromFile(frameworkExtPath).getLines.mkString("|").r

  val appMethods = ir.getAllMethods.filter(m => !isFrameworkClass(m.classType)).toSet
  def getCallbacks = appMethods.filter(resolveCallbackEntry(_).isDefined)
  def isFrameworkClass(packageName:String):Boolean = packageName match{
    case extensionStrings() => true
    case _ => false
  }

  override def resolveCallLocation(tgt: UnresolvedMethodTarget): Loc = tgt match{
    case UnresolvedMethodTarget(clazz, method, _) if isFrameworkClass(clazz) => CallinMethodReturn(clazz, method, None)
    case UnresolvedMethodTarget(clazz, method, Some(methodloc: MethodLoc)) => InternalMethodReturn(clazz, method, methodloc)
  }

  override def resolveCallbackExit(method: MethodLoc, retCmdLoc: Option[LineLoc]): Option[Loc] = {
    val overrides = ir.getOverrideChain(method)
    if(overrides.size == 1 && overrides.last.classType == "java.lang.Object" && overrides.last.simpleName == "<init>"){
      // Object init is not considered a callback
      return None
    }
    if (overrides.size > 0) {
      val leastPrecise: MethodLoc = overrides.last
      Some(CallbackMethodReturn(leastPrecise.classType, leastPrecise.simpleName, method, retCmdLoc))
    } else None

  }
  override def resolveCallbackEntry(method:MethodLoc):Option[Loc] = {
    val overrides = ir.getOverrideChain(method)
    if(overrides.size == 1 && overrides.last.classType == "java.lang.Object" && overrides.last.simpleName == "<init>"){
      // Object init is not considered a callback
      return None
    }
    if (overrides.size > 0) {
      val leastPrecise: MethodLoc = overrides.last
      Some(CallbackMethodInvoke(leastPrecise.classType, leastPrecise.simpleName, method))
    } else None
  }
}