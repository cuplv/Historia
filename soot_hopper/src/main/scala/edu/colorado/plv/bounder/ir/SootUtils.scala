package edu.colorado.plv.bounder.ir

import java.util
import scala.jdk.CollectionConverters._

import soot.{Scene, SootClass, SootMethod}

/**
 * Depricated, use JimpleWrapper
 */
@Deprecated
object SootUtils {
  def findMethodLoc(className: String, methodName : String):Option[JimpleMethodLoc] = {
//    val clazzes = Scene.v().getClasses()
    val clazzFound = Scene.v().getSootClass(className)
    val clazz = if(clazzFound.isPhantom){None} else {Some(clazzFound)}
    val method: Option[SootMethod] = clazz.flatMap(a => try{
      Some(a.getMethod(methodName))
    }catch{
      case t:RuntimeException if t.getMessage.startsWith("No method") =>
        None
      case t:Throwable => throw t
    })
    method.map(a=> JimpleMethodLoc(a))
  }
  def findLineInMethod(line:Int, loc:JimpleMethodLoc):Iterable[Loc] = {
    val activeBody = loc.method.retrieveActiveBody()
    val units: Iterable[soot.Unit] = activeBody.getUnits.asScala
    units.filter(a => a.getJavaSourceStartLineNumber == line).map((a:soot.Unit) => AppLoc(loc, JimpleLineLoc(a,loc.method),true))
  }
}
