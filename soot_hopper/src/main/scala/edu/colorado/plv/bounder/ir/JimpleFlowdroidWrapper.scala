package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.BounderSetupApplication
import edu.colorado.plv.bounder.state.TypeConstraint
import edu.colorado.plv.fixedsoot.EnhancedUnitGraphFixed
import soot.jimple.ThisRef
import soot.jimple.internal.{AbstractDefinitionStmt, AbstractInstanceFieldRef, AbstractInstanceInvokeExpr, AbstractNewExpr, JAssignStmt, JIdentityStmt, JInvokeStmt, JReturnStmt, JSpecialInvokeExpr, JVirtualInvokeExpr, JimpleLocal, VariableBox}
import soot.{Body, Hierarchy, Scene, SootMethod, Value}

import scala.jdk.CollectionConverters._


class JimpleFlowdroidWrapper(apkPath : String) extends IRWrapper[SootMethod, soot.Unit] {

  BounderSetupApplication.loadApk(apkPath)

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
    val loc:AppLoc = locOpt.getOrElse(???)
    cmd match{
      case cmd: AbstractDefinitionStmt => {
        val leftBox = makeVal(cmd.leftBox.getValue).asInstanceOf[LVal]
        val rightBox = makeVal(cmd.rightBox.getValue)
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
    case AppLoc(methodWrapper @ JimpleMethodLoc(_),JimpleLineLoc(cmd,sootMethod), true) => {
      val unitGraph = getUnitGraph(sootMethod.retrieveActiveBody())
      val predCommands = unitGraph.getPredsOf(cmd).asScala
      predCommands.map(cmd => AppLoc(methodWrapper,JimpleLineLoc(cmd,sootMethod), false)).toList
    }
    case _ => ???
  }
  override def commandNext(cmdWrapper: CmdWrapper[SootMethod, soot.Unit]):List[AppLoc] = {
    cmdWrapper.getLoc match{
      case AppLoc(method, line, _) => List(AppLoc(method,line,true))
      case _ =>
        ???
    }
  }

//  override def makeLoc(mcd: soot.Unit, method: SootMethod):AppLoc = {
//    ???
//  }

  override def cmdAfterLocation(loc: AppLoc): CmdWrapper[SootMethod, soot.Unit] = {
    loc match{
      case AppLoc(_, JimpleLineLoc(cmd,method),true) =>{
        makeCmd(cmd,method,Some(loc))
      }
      case _ =>
        ???
    }
  }

  override def cmdBeforeLocation(loc: AppLoc): CmdWrapper[SootMethod, soot.Unit] = loc match{
    case AppLoc(_, JimpleLineLoc(cmd, method), false) =>
      makeCmd(cmd,method,Some(loc))
    case _ =>
      ???
  }
  protected def makeRVal(box:Value):RVal = box match{
    case a: AbstractInstanceInvokeExpr =>{
      val target = makeVal(a.getBase) match{
        case jl@LocalWrapper(_,_)=>jl
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
    case t:ThisRef => ThisWrapper(t.getType.toString)
    case _ =>
      ???
  }

  protected def makeVal(box: Value):RVal = box match{
    case a : JimpleLocal=>
      LocalWrapper(a.getName,a.getType.toString)
    case f: AbstractInstanceFieldRef => {
      val fieldType = f.getType.toString
      val base = makeVal(f.getBase).asInstanceOf[LocalWrapper]
      val fieldname = f.getField.getName
      val fieldDeclType = f.getField.getDeclaringClass.toString
      FieldRef(base,fieldType, fieldDeclType, fieldname)
    }
    case a => makeRVal(a)
  }

  override def isMethodEntry(cmdWrapper: CmdWrapper[SootMethod, soot.Unit]): Boolean = cmdWrapper.getLoc match {
    case AppLoc(_, JimpleLineLoc(cmd,method),true) => {
      val unitBoxes = method.retrieveActiveBody().getUnits
      if(unitBoxes.size > 0){
        cmd.equals(unitBoxes.getFirst)
      }else {false}
    }
    case AppLoc(_, _,false) => false // exit of command is not entry let transfer one more time
    case _ => ???
  }

  override def findLineInMethod(className: String, methodName: String, line: Int): Iterable[AppLoc] = {
    val loc: Option[JimpleMethodLoc] = findMethodLoc(className, methodName)
    loc.map(loc => {
      val activeBody = loc.method.retrieveActiveBody()
      val units: Iterable[soot.Unit] = activeBody.getUnits.asScala
      units.filter(a => a.getJavaSourceStartLineNumber == line).map((a:soot.Unit) => AppLoc(loc, JimpleLineLoc(a,loc.method),true))
    }).getOrElse(List())
  }

  override def makeInvokeTargets(invoke: InvokeCmd[SootMethod, soot.Unit]): Set[UnresolvedMethodTarget] = {
    val cg = Scene.v().getCallGraph
    var pt = Scene.v().getPointsToAnalysis
    val cmd = invoke.getLoc.line match{
      case JimpleLineLoc(cmd, _) => cmd
      case _ => throw new IllegalArgumentException("Bad Location Type")
    }
    val edges = cg.edgesOutOf(cmd)

    edges.asScala.map(a => {
      val tgt = a.getTgt.method()
      val clazz = tgt.getDeclaringClass.getName
      val method = tgt.getName
      UnresolvedMethodTarget(clazz, method, Some(JimpleMethodLoc(tgt)))
    }).toSet
  }

  override def canAlias(type1: String, type2: String): Boolean = {
    if(type1 == type2) true else {
      val hierarchy: Hierarchy = Scene.v().getActiveHierarchy
      val type1Soot = Scene.v().getSootClass(type1)
      val type2Soot = Scene.v().getSootClass(type2)
      val sub1 = hierarchy.getSubclassesOfIncluding(type1Soot).asScala
      val sub2 = hierarchy.getSubclassesOfIncluding(type2Soot).asScala.toSet
      sub1.exists(a => sub2.contains(a))
    }
  }
}

case class JimpleMethodLoc(method: SootMethod) extends MethodLoc
case class JimpleLineLoc(cmd: soot.Unit, method: SootMethod) extends LineLoc{
  override def toString: String = cmd.toString
}

