package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.Main
import edu.colorado.plv.fixedsoot.EnhancedUnitGraphFixed
import soot.jimple.internal.{AbstractInstanceInvokeExpr, JAssignStmt, JInvokeStmt, JReturnStmt, JSpecialInvokeExpr, JVirtualInvokeExpr, JimpleLocal, VariableBox}
import soot.{Body, Scene, SootMethod, Value, ValueBox}

import scala.jdk.CollectionConverters._

class JimpleWrapper(apkPath : String) extends IRWrapper[SootMethod, soot.Unit] {

  Main.loadApk(apkPath)

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
                       locOpt:Option[Loc] = None): CmdWrapper[SootMethod, soot.Unit] = {
    val loc = locOpt.getOrElse(makeLoc(cmd,method))
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
        val invokeval = makeVal(cmd.getInvokeExpr).asInstanceOf[Invoke]
        InvokeCmd(invokeval, loc, this)
      }
      case _ =>
        ???
    }
  }

  override def preds(cmdWrapper : CmdWrapper[SootMethod,soot.Unit]):Set[CmdWrapper[SootMethod,soot.Unit]] =
    cmdWrapper.getLoc match{
    case loc@Loc(_,JimpleLineLoc(cmd,method)) => {
      val unitGraph = getUnitGraph(method.retrieveActiveBody())
      unitGraph.getPredsOf(cmd).asScala.map(makeCmd(_, method, Some(loc))).toSet
    }
    case _ => ???
  }

  override def makeMethod(method: SootMethod): MethodWrapper[SootMethod, soot.Unit] = ???

  override def makeLoc(mcd: soot.Unit, method: SootMethod):Loc = {
    ???
  }

  override def makeCmd(loc: Loc): CmdWrapper[SootMethod, soot.Unit] = {
    loc match{
      case Loc(_, JimpleLineLoc(cmd,method)) =>{
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
        case _:JVirtualInvokeExpr => VirtualInvoke(target, targetClass, targetMethod, params)
        case _:JSpecialInvokeExpr => SpecialInvoke(target,targetClass, targetMethod, params)
        case _ => ???
      }
    }
//    case a:JVirtualInvokeExpr => {
//      val target = makeVal(a.getBase) match{
//        case jl@LocalWrapper(name)=>jl
//        case _ => ???
//      }
//      val targetClass = a.getMethodRef.getDeclaringClass.getName
//      val targetMethod = a.getMethodRef.getSignature
//      val params:List[LocalWrapper] = (0 until a.getArgCount).map(sloc => ???).toList //TODO: implement parameters
//      VirtualInvoke(target, targetClass,targetMethod,params)
//    }
//    case a:JSpecialInvokeExpr => {
//
//    }
    case a =>
      ???
  }

  protected def makeVal(box: Value):RVal = box match{
    case a : JimpleLocal=> LocalWrapper(a.getName)
    case a => makeRVal(a)
  }

  override def isMethodEntry(cmdWrapper: CmdWrapper[SootMethod, soot.Unit]): Boolean = cmdWrapper.getLoc match {
    case Loc(_, JimpleLineLoc(cmd,method)) => {
      val unitBoxes = method.retrieveActiveBody().getUnits
      if(unitBoxes.size > 0){
        cmd.equals(unitBoxes.getFirst)
      }else {false}
    }
    case _ => ???
  }

  override def findLineInMethod(className: String, methodName: String, line: Int): Iterable[Loc] = {
    val loc: Option[JimpleMethodLoc] = findMethodLoc(className, methodName)
    loc.map(loc => {
      val activeBody = loc.method.retrieveActiveBody()
      val units: Iterable[soot.Unit] = activeBody.getUnits.asScala
      units.filter(a => a.getJavaSourceStartLineNumber == line).map((a:soot.Unit) => Loc(loc, JimpleLineLoc(a,loc.method)))
    }).getOrElse(List())
  }
}

case class JimpleMethodLoc(method: SootMethod) extends MethodLoc
case class JimpleLineLoc(cmd: soot.Unit, method: SootMethod) extends LineLoc

