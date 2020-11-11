package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.BounderSetupApplication
import edu.colorado.plv.bounder.symbolicexecutor.state.TypeConstraint
import edu.colorado.plv.fixedsoot.EnhancedUnitGraphFixed
import soot.jimple.ThisRef
import soot.jimple.internal.{AbstractDefinitionStmt, AbstractInstanceFieldRef, AbstractInstanceInvokeExpr, AbstractNewExpr, JAssignStmt, JIdentityStmt, JInvokeStmt, JReturnStmt, JReturnVoidStmt, JSpecialInvokeExpr, JVirtualInvokeExpr, JimpleLocal, VariableBox}
import soot.{Body, Hierarchy, Scene, SootClass, SootMethod, Value}

import scala.collection.mutable
import scala.jdk.CollectionConverters._

object JimpleFlowdroidWrapper{
  def stringNameOfClass(m : SootClass): String = {
    val name = m.getName
//    s"${m.getPackageName}.${name}"
    name
  }
}

class JimpleFlowdroidWrapper(apkPath : String) extends IRWrapper[SootMethod, soot.Unit] {

  BounderSetupApplication.loadApk(apkPath)

  var unitGraphCache : scala.collection.mutable.Map[Body, EnhancedUnitGraphFixed] = scala.collection.mutable.Map()

  def addClassFile(path: String): Unit = {

  }

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
  override def getAllMethods: Iterable[MethodLoc] = {
    Scene.v().getApplicationClasses.asScala.flatMap(clazz => {
      if(clazz.getJavaPackageName == "com.example.test_interproc_1" && clazz.getName.contains("MainActivity"))
        println()
      clazz.getMethods.asScala
        .filter(!_.hasTag("SimulatedCodeElementTag")) // Remove simulated code elements from Flowdroid
        .map(JimpleMethodLoc)
    })
  }

  override def makeCmd(cmd: soot.Unit, method: SootMethod,
                       locOpt:Option[AppLoc] = None): CmdWrapper = {
    val loc:AppLoc = locOpt.getOrElse(???)
    cmd match{
      case cmd: AbstractDefinitionStmt => {
        val leftBox = makeVal(cmd.leftBox.getValue).asInstanceOf[LVal]
        val rightBox = makeVal(cmd.rightBox.getValue)
        AssignCmd(leftBox, rightBox,loc)
      }
      case cmd: JReturnStmt => {
        val box = makeVal(cmd.getOpBox.getValue).asInstanceOf[LocalWrapper]
        ReturnCmd(Some(box), loc)
      }
      case cmd:JInvokeStmt => {
        val invokeval = makeVal(cmd.getInvokeExpr).asInstanceOf[Invoke]
        InvokeCmd(invokeval, loc)
      }
      case _ : JReturnVoidStmt => {
        ReturnCmd(None, loc)
      }
      case _ =>
        ???
    }
  }

  override def commandPredicessors(cmdWrapper : CmdWrapper):List[AppLoc] =
    cmdWrapper.getLoc match{
    case AppLoc(methodWrapper @ JimpleMethodLoc(_),JimpleLineLoc(cmd,sootMethod), true) => {
      val unitGraph = getUnitGraph(sootMethod.retrieveActiveBody())
      val predCommands = unitGraph.getPredsOf(cmd).asScala
      predCommands.map(cmd => AppLoc(methodWrapper,JimpleLineLoc(cmd,sootMethod), false)).toList
    }
    case _ => ???
  }
  override def commandNext(cmdWrapper: CmdWrapper):List[AppLoc] = {
    cmdWrapper.getLoc match{
      case AppLoc(method, line, _) => List(AppLoc(method,line,true))
      case _ =>
        ???
    }
  }

  override def cmdAfterLocation(loc: AppLoc): CmdWrapper = {
    loc match{
      case AppLoc(_, JimpleLineLoc(cmd,method),true) =>{
        makeCmd(cmd,method,Some(loc))
      }
      case _ =>
        ???
    }
  }

  override def cmdBeforeLocation(loc: AppLoc): CmdWrapper = loc match{
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
        case _:JVirtualInvokeExpr => VirtualInvoke(target, targetClass, targetMethod, params)
        case _:JSpecialInvokeExpr => SpecialInvoke(target,targetClass, targetMethod, params)
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

  override def isMethodEntry(cmdWrapper: CmdWrapper): Boolean = cmdWrapper.getLoc match {
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

  override def makeInvokeTargets(invoke: InvokeCmd): Set[UnresolvedMethodTarget] = {
    val cg = Scene.v().getCallGraph
    //var pt = Scene.v().getPointsToAnalysis
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

  def canAlias(type1: String, type2: String): Boolean = {
    if(type1 == type2) true else {
      val hierarchy: Hierarchy = Scene.v().getActiveHierarchy
      val type1Soot = Scene.v().getSootClass(type1)
      val type2Soot = Scene.v().getSootClass(type2)
      val sub1 = hierarchy.getSubclassesOfIncluding(type1Soot).asScala
      val sub2 = hierarchy.getSubclassesOfIncluding(type2Soot).asScala.toSet
      sub1.exists(a => sub2.contains(a))
    }
  }

  override def getOverrideChain(method: MethodLoc): Seq[MethodLoc] = {
    val m = method.asInstanceOf[JimpleMethodLoc]
    val methodDeclClass = m.method.getDeclaringClass
    val methodSignature = m.method.getSubSignature
    val superclasses = Scene.v().getActiveHierarchy.getSuperclassesOf(methodDeclClass)
    val methods = superclasses.asScala.filter(sootClass => sootClass.declaresMethod(methodSignature))
      .map( sootClass=> JimpleMethodLoc(sootClass.getMethod(methodSignature)))
    methods.toList
  }

  override def callSites(method: SootMethod): Seq[soot.Unit] = ???

  override def makeMethodRetuns(method: MethodLoc): List[Loc] = {
    val smethod = method.asInstanceOf[JimpleMethodLoc]
    val rets = mutable.ListBuffer[AppLoc]()
    smethod.method.getActiveBody.getUnits.forEach( (u:soot.Unit) =>{
      if (u.isInstanceOf[JReturnStmt] || u.isInstanceOf[JReturnVoidStmt]) {
        val lineloc = JimpleLineLoc(u, smethod.method)
        rets.addOne(AppLoc(smethod, lineloc, false))
      }
    })
    rets.toList
  }

  override def getClassHierarchy: Map[String, Set[String]] = {
    val hierarchy: Hierarchy = Scene.v().getActiveHierarchy
    Scene.v().getClasses().asScala.foldLeft(Map[String, Set[String]]()){ (acc,v) =>
      val cname = JimpleFlowdroidWrapper.stringNameOfClass(v)
      val subclasses = if(v.isInterface()) {
        hierarchy.getImplementersOf(v)
      }else {
        hierarchy.getSubclassesOf(v)
      }
      val strSubClasses = subclasses.asScala.map(c => JimpleFlowdroidWrapper.stringNameOfClass(c)).toSet + cname
      acc  + (cname -> strSubClasses)
    }
  }

}

case class JimpleMethodLoc(method: SootMethod) extends MethodLoc {
  override def simpleName: String = method.getName

  override def classType: String = {
    JimpleFlowdroidWrapper.stringNameOfClass(method.getDeclaringClass)
  }

  override def argTypes: List[String] = method.getParameterTypes.asScala.map({
    case t =>
      ???
  }).toList
}
case class JimpleLineLoc(cmd: soot.Unit, method: SootMethod) extends LineLoc{
  override def toString: String = cmd.toString
}

