package edu.colorado.plv.bounder.symbolicexecutor

import java.net.URL

import better.files.{File, Resource}
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
object FrameworkExtensions{
  private val url = Resource.getUrl("FrameworkExtensions.txt")
  protected val frameworkExtPath = url.getPath
  val extensionStrings: List[String] = {
    val source = Source.fromFile(frameworkExtPath)
    try {
      source.getLines.toList
    }finally{
      source.close
    }
  }
  val extensionRegex: Regex = extensionStrings.mkString("|").r
}

class DefaultAppCodeResolver[M,C] (ir: IRWrapper[M,C]) extends AppCodeResolver {

  protected val excludedClasses = "dummyMainClass".r

  val appMethods = ir.getAllMethods.filter(m => !isFrameworkClass(m.classType)).toSet
  def getCallbacks:Set[MethodLoc] = appMethods.filter(resolveCallbackEntry(_).isDefined)
  def isFrameworkClass(fullClassName:String):Boolean = fullClassName match{
    case FrameworkExtensions.extensionRegex() => true
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
    if(method.simpleName == "void <clinit>()"){
      // <clinit> considered a callback
      return Some(CallbackMethodInvoke("java.lang.Object", "void <clinit>()", method))
    }
    if(method.isInterface)
      return None // Interface methods cannot be callbacks
    val overrides = ir.getOverrideChain(method).filter(c =>
      isFrameworkClass(
        JimpleFlowdroidWrapper.stringNameOfClass(
          c.asInstanceOf[JimpleMethodLoc].method.getDeclaringClass)))
    if(overrides.size == 1 && overrides.last.classType == "java.lang.Object" && overrides.last.simpleName == "<init>"){
      // Object init is not considered a callback unless it overrides a subclass's init
      return None
    }
    if (overrides.size > 0) {
      val leastPrecise: MethodLoc = overrides.last
      Some(CallbackMethodInvoke(leastPrecise.classType, leastPrecise.simpleName, method))
    } else None
  }
}