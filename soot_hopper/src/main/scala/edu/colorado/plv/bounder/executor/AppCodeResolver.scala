package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.ir.{AppLoc, CallinMethodReturn, InternalMethodReturn, JimpleFlowdroidWrapper, Loc, MethodLoc, UnresolvedMethodTarget}
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper.getClass

import scala.io.Source
import scala.util.matching.Regex

trait AppCodeResolver {
  def isFrameworkClass(packageName:String):Boolean
  def resolveMethodLocation(tgt : UnresolvedMethodTarget): Loc
}

class DefaultAppCodeResolver () extends AppCodeResolver {
  protected val frameworkExtPath = getClass.getResource("/FrameworkExtensions.txt").getPath
  protected val extensionStrings: Regex = Source.fromFile(frameworkExtPath).getLines.mkString("|").r
  def isFrameworkClass(packageName:String):Boolean = packageName match{
    case extensionStrings() => true
    case _ => false
  }

  override def resolveMethodLocation(tgt: UnresolvedMethodTarget): Loc = tgt match{
    case UnresolvedMethodTarget(clazz, method, _) if isFrameworkClass(clazz) => CallinMethodReturn(clazz, method)
    case UnresolvedMethodTarget(clazz, method, Some(methodloc: MethodLoc)) => InternalMethodReturn(clazz, method, methodloc)
  }
}