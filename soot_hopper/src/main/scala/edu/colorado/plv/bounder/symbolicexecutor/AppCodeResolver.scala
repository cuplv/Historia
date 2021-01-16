package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodReturn, IRWrapper, InternalMethodReturn, JimpleFlowdroidWrapper, JimpleMethodLoc, LineLoc, Loc, MethodLoc, UnresolvedMethodTarget}

import scala.io.Source
import scala.util.matching.Regex

trait AppCodeResolver {
  def isFrameworkClass(packageName:String):Boolean
  def isAppClass(fullClassName:String):Boolean
  def resolveCallLocation(tgt : UnresolvedMethodTarget): Set[Loc]
  def resolveCallbackExit(method : MethodLoc, retCmdLoc: Option[LineLoc]):Option[Loc]
  def resolveCallbackEntry(method: MethodLoc):Option[Loc]
  def getCallbacks: Set[MethodLoc]
}

class DefaultAppCodeResolver[M,C] (ir: IRWrapper[M,C]) extends AppCodeResolver {
  protected val frameworkExtPath = getClass.getResource("/FrameworkExtensions.txt").getPath
  protected val extensionStrings: Regex = Source.fromFile(frameworkExtPath).getLines.mkString("|").r

  protected val excludedClasses = "dummyMainClass".r

  val appMethods = ir.getAllMethods.filter(m => !isFrameworkClass(m.classType)).toSet
  def getCallbacks = appMethods.filter(resolveCallbackEntry(_).isDefined)
  def isFrameworkClass(fullClassName:String):Boolean = fullClassName match{
    case extensionStrings() => true
    case _ => false
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
        CallinMethodReturn(classType, m.simpleName)
      }else {
        InternalMethodReturn(classType, m.simpleName, m)
      }
    }
  }
//  override def resolveCallLocation(tgt: UnresolvedMethodTarget): Set[Loc] = tgt match{
//    case UnresolvedMethodTarget(clazz, method, _) if isFrameworkClass(clazz) =>
//      Set(CallinMethodReturn(clazz, method, None))
//    case UnresolvedMethodTarget(clazz, method, methodLocs) =>
//      methodLocs.map(loc => InternalMethodReturn(clazz, method, _))
//  }

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