package edu.colorado.plv.bounder.ir

import java.io.File
import java.net.URL
import java.util

import edu.colorado.plv.bounder.SetupApplication
import edu.colorado.plv.fixedsoot.EnhancedUnitGraphFixed
import soot.jimple.internal.{AbstractInstanceInvokeExpr, AbstractNewExpr, JAssignStmt, JInvokeStmt, JReturnStmt, JSpecialInvokeExpr, JVirtualInvokeExpr, JimpleLocal, VariableBox}
import soot.{Body, Scene, SootMethod, Value, ValueBox}

import scala.jdk.CollectionConverters._
import scala.io.Source
import scala.util.matching.Regex

object JimpleWrapper{

}
class JimpleWrapper(apkPath : String) extends IRWrapper[SootMethod, soot.Unit] {

  SetupApplication.loadApk(apkPath)

  var unitGraphCache : scala.collection.mutable.Map[Body, EnhancedUnitGraphFixed] = scala.collection.mutable.Map()

  protected def getUnitGraph(body:Body):EnhancedUnitGraphFixed = {
    if(unitGraphCache.contains(body)){
      unitGraphCache.getOrElse(body, ???)
    }else{
      val cache = new EnhancedUnitGraphFixed(body)
      unitGraphCache.put(body, cache)
      cache
    }
  }

  override def findMethodLoc(className: String, methodName: String):Option[JimpleMethodLoc] = {
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
  override def makeCmd(cmd: soot.Unit, method: SootMethod,
                       locOpt:Option[AppLoc] = None): CmdWrapper[SootMethod, soot.Unit] = {
    val loc:AppLoc = locOpt.getOrElse(makeLoc(cmd,method))
    cmd match{
      case cmd: JAssignStmt => {
        val leftBox = makeVal(cmd.leftBox.getValue).asInstanceOf[LVal]
        val rightBox = makeRVal(cmd.rightBox.getValue)
        AssignCmd(leftBox, rightBox,loc,this)
      }
      case cmd: JReturnStmt => {
        val box = makeVal(cmd.getOpBox.getValue).asInstanceOf[LocalWrapper]
        ReturnVal(box, loc, this)
      }
      case cmd:JInvokeStmt => {
        val invokeval = makeVal(cmd.getInvokeExpr).asInstanceOf[Invoke[SootMethod,soot.Unit]]
        InvokeCmd[SootMethod,soot.Unit](invokeval, loc, this)
      }
      case _ =>
        ???
    }
  }

  override def commandPredicessors(cmdWrapper : CmdWrapper[SootMethod,soot.Unit]):List[AppLoc] =
    cmdWrapper.getLoc match{
    case loc@AppLoc(methodWrapper @ JimpleMethodLoc(_),JimpleLineLoc(cmd,sootMethod)) => {
      val unitGraph = getUnitGraph(sootMethod.retrieveActiveBody())
      val predCommands = unitGraph.getPredsOf(cmd).asScala
      predCommands.map(cmd => AppLoc(methodWrapper,JimpleLineLoc(cmd,sootMethod))).toList
    }
    case _ => ???
  }

  override def makeMethod(method: SootMethod): MethodWrapper[SootMethod, soot.Unit] = ???

  override def makeLoc(mcd: soot.Unit, method: SootMethod):AppLoc = {
    ???
  }

  override def cmdAfterLocation(loc: AppLoc): CmdWrapper[SootMethod, soot.Unit] = {
    loc match{
      case AppLoc(_, JimpleLineLoc(cmd,method)) =>{
        makeCmd(cmd,method,Some(loc))
      }
      case _ =>
        ???
    }
  }
  protected def makeRVal(box:Value):RVal = box match{
    case a: AbstractInstanceInvokeExpr =>{
      val target = makeVal(a.getBase) match{
        case jl@LocalWrapper(_)=>jl
        case _ => ???
      }
      val targetClass = a.getMethodRef.getDeclaringClass.getName
      val targetMethod = a.getMethodRef.getSignature
      val params: List[LocalWrapper] = (0 until a.getArgCount()).map(argPos => ???).toList //TODO: implement parameters
      a match{
        case _:JVirtualInvokeExpr => VirtualInvoke(target, targetClass, targetMethod, params,this)
        case _:JSpecialInvokeExpr => SpecialInvoke(target,targetClass, targetMethod, params,this)
        case _ => ???
      }
    }
    case n : AbstractNewExpr => {
      val className = n.getType.toString
      NewCommand(className)
    }
    case a =>
      ???
  }

  protected def makeVal(box: Value):RVal = box match{
    case a : JimpleLocal=> LocalWrapper(a.getName)
    case a => makeRVal(a)
  }

  override def isMethodEntry(cmdWrapper: CmdWrapper[SootMethod, soot.Unit]): Boolean = cmdWrapper.getLoc match {
    case AppLoc(_, JimpleLineLoc(cmd,method)) => {
      val unitBoxes = method.retrieveActiveBody().getUnits
      if(unitBoxes.size > 0){
        cmd.equals(unitBoxes.getFirst)
      }else {false}
    }
    case _ => ???
  }

  override def findLineInMethod(className: String, methodName: String, line: Int): Iterable[AppLoc] = {
    val loc: Option[JimpleMethodLoc] = findMethodLoc(className, methodName)
    loc.map(loc => {
      val activeBody = loc.method.retrieveActiveBody()
      val units: Iterable[soot.Unit] = activeBody.getUnits.asScala
      units.filter(a => a.getJavaSourceStartLineNumber == line).map((a:soot.Unit) => AppLoc(loc, JimpleLineLoc(a,loc.method)))
    }).getOrElse(List())
  }

//  /**
//   * Check if a method is a callback callin or internal application type
//   * @param method
//   * @return
//   */
//  override def methodType(method: Invoke[SootMethod,soot.Unit]): MethodType = {
//    val targetClass: String = method.targetClass
//    if(JimpleWrapper.isFrameworkPackage(targetClass)){
//      // If the target class is a framework class, then it must be a callin
//      CallinMethod(targetClass, method.targetMethod)
//    }else {
//      ???
//    }
//  }
  override def makeInvokeTargets(invoke: InvokeCmd[SootMethod, soot.Unit]): Set[Loc] = {
    var cg = Scene.v().getCallGraph
    var pt = Scene.v().getPointsToAnalysis

    ???
  }
}

case class JimpleMethodLoc(method: SootMethod) extends MethodLoc
case class JimpleLineLoc(cmd: soot.Unit, method: SootMethod) extends LineLoc{
  override def toString: String = cmd.toString
}

