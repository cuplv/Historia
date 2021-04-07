package edu.colorado.plv.bounder.ir

import java.util

import edu.colorado.plv.bounder.{BounderSetupApplication, BounderUtil}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor._
import edu.colorado.plv.bounder.symbolicexecutor.state.State
import edu.colorado.plv.fixedsoot.{EnhancedUnitGraphFixed, SparkAppOnlyTransformer}
import scalaz.Memo
import soot.jimple.infoflow.entryPointCreators.SimulatedCodeElementTag
import soot.jimple.internal._
import soot.jimple.spark.SparkTransformer
import soot.jimple.toolkits.callgraph.{CHATransformer, CallGraph, ReachableMethods, TopologicalOrderer}
import soot.jimple._
import soot.jimple.toolkits.annotation.logic.LoopFinder
import soot.options.Options
import soot.toolkits.graph.{PseudoTopologicalOrderer, SlowPseudoTopologicalOrderer}
import soot.util.Chain
import soot.{ArrayType, Body, BooleanType, ByteType, CharType, DoubleType, FloatType, Hierarchy, IntType, Local, LongType, Modifier, RefType, Scene, ShortType, SootClass, SootField, SootMethod, SootMethodRef, Type, Value}

import scala.annotation.tailrec
import scala.collection.immutable.Queue
import scala.collection.{MapView, mutable}
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

object JimpleFlowdroidWrapper{
  val cgEntryPointName:String = "CgEntryPoint___________a____b"
  def stringNameOfClass(m : SootClass): String = {
    val name = m.getName
//    s"${m.getPackageName}.${name}"
    name
  }
  def stringNameOfType(t : Type) : String = t match {
    case t:RefType =>
      val str = t.toString
      str
    case _:IntType => ClassHierarchyConstraints.intType
    case _:ShortType => ClassHierarchyConstraints.shortType
    case _:ByteType => ClassHierarchyConstraints.byteType
    case _:LongType => ClassHierarchyConstraints.longType
    case _:DoubleType => ClassHierarchyConstraints.doubleType
    case _:CharType => ClassHierarchyConstraints.charType
    case _:BooleanType => ClassHierarchyConstraints.booleanType
    case _:FloatType => ClassHierarchyConstraints.floatType
    case t => t.toString
  }

  /**
   * Use instead of soot version because soot version crashes on interface.
   * @param sootClass
   * @return
   */
  def subThingsOf(sootClass: SootClass):Set[SootClass] =
    if(sootClass.isInterface)
      Scene.v.getActiveHierarchy.getImplementersOf(sootClass).asScala.toSet
    else
      Scene.v.getActiveHierarchy.getSubclassesOfIncluding(sootClass).asScala.toSet


  protected def makeRVal(box:Value):RVal = box match{
    case a: AbstractInstanceInvokeExpr =>{
      val target = makeVal(a.getBase) match{
        case jl@LocalWrapper(_,_)=>jl
        case _ => ???
      }
      val targetClass = a.getMethodRef.getDeclaringClass.getName
      val targetMethod = a.getMethodRef.getSubSignature.toString
      val params: List[RVal] = (0 until a.getArgCount()).map(argPos =>
        makeVal(a.getArg(argPos))
      ).toList
      a match{
        case _:JVirtualInvokeExpr => VirtualInvoke(target, targetClass, targetMethod, params)
        case _:JSpecialInvokeExpr => SpecialInvoke(target,targetClass, targetMethod, params)
        case _:JInterfaceInvokeExpr => VirtualInvoke(target, targetClass, targetMethod, params)
        case v =>
          //println(v)
          ???
      }
    }
    case a : AbstractStaticInvokeExpr => {
      val params: List[RVal] = (0 until a.getArgCount()).map(argPos =>
        makeVal(a.getArg(argPos))
      ).toList
      val targetClass = a.getMethodRef.getDeclaringClass.getName
      val targetMethod = a.getMethodRef.getSubSignature.toString
      StaticInvoke(targetClass, targetMethod, params)
    }
    case n : AbstractNewExpr => {
      val className = n.getType.toString
      NewCommand(className)
    }
    case t:ThisRef => ThisWrapper(t.getType.toString)
    case _:NullConstant => NullConst
    case v:IntConstant => IntConst(v.value)
    case v:LongConstant => IntConst(v.value.toInt)
    case v:StringConstant => StringConst(v.value)
    case p:ParameterRef =>
      val name = s"@parameter${p.getIndex}"
      val tname = p.getType.toString
      LocalWrapper(name, tname)
    case ne: JNeExpr => Binop(makeRVal(ne.getOp1),Ne, makeRVal(ne.getOp2))
    case eq: JEqExpr => Binop(makeRVal(eq.getOp1),Eq, makeRVal(eq.getOp2))
    case local: JimpleLocal =>
      LocalWrapper(local.getName, JimpleFlowdroidWrapper.stringNameOfType(local.getType))
    case cast: JCastExpr =>
      val castType = JimpleFlowdroidWrapper.stringNameOfType(cast.getCastType)
      val v = makeRVal(cast.getOp)
      Cast(castType, v)
    case mult: JMulExpr =>
      val op1 = makeRVal(mult.getOp1)
      val op2 = makeRVal(mult.getOp2)
      Binop(op1, Mult, op2)
    case div : JDivExpr =>
      val op1 = makeRVal(div.getOp1)
      val op2 = makeRVal(div.getOp2)
      Binop(op1, Div, op2)
    case div : JAddExpr =>
      val op1 = makeRVal(div.getOp1)
      val op2 = makeRVal(div.getOp2)
      Binop(op1, Add, op2)
    case div : JSubExpr =>
      val op1 = makeRVal(div.getOp1)
      val op2 = makeRVal(div.getOp2)
      Binop(op1, Sub, op2)
    case neg :JNegExpr =>
      Binop(IntConst(0), Sub, makeRVal(neg.getOp))
    case lt : JLeExpr =>
      val op1 = makeRVal(lt.getOp1)
      val op2 = makeRVal(lt.getOp2)
      Binop(op1, Le, op2)
    case lt : JLtExpr =>
      val op1 = makeRVal(lt.getOp1)
      val op2 = makeRVal(lt.getOp2)
      Binop(op1, Lt, op2)
    case gt: JGtExpr =>
      val op1 = makeRVal(gt.getOp1)
      val op2 = makeRVal(gt.getOp2)
      Binop(op2, Lt, op1)
    case ge: JGeExpr =>
      val op1 = makeRVal(ge.getOp1)
      val op2 = makeRVal(ge.getOp2)
      Binop(op1, Ge, op2)
    case staticRef : StaticFieldRef =>
      val declaringClass = JimpleFlowdroidWrapper.stringNameOfClass(staticRef.getFieldRef.declaringClass())
      val fieldName = staticRef.getFieldRef.name()
      val containedType = JimpleFlowdroidWrapper.stringNameOfType(staticRef.getFieldRef.`type`())
      StaticFieldReference(declaringClass, fieldName, containedType)

    case const: RealConstant=>
      ConstVal(const.toString) // Not doing anything special with real values for now
    case caught: JCaughtExceptionRef =>
      CaughtException("")
    case jcomp: JCmpExpr =>
      val op1 = makeRVal(jcomp.getOp1)
      val op2 = makeRVal(jcomp.getOp2)
      Binop(op1,Eq, op2)
    case jcomp: JCmplExpr =>
      val op1 = makeRVal(jcomp.getOp1)
      val op2 = makeRVal(jcomp.getOp2)
      Binop(op1,Eq,op2)
    case jcomp: JCmpgExpr =>
      val op1 = makeRVal(jcomp.getOp1)
      val op2 = makeRVal(jcomp.getOp2)
      Binop(op1,Eq,op2)
    case i : JInstanceOfExpr =>
      val targetClassType = JimpleFlowdroidWrapper.stringNameOfType(i.getCheckType)
      val target = makeRVal(i.getOp).asInstanceOf[LocalWrapper]
      InstanceOf(targetClassType, target)
    case a : ArrayRef =>
      val baseVar = makeRVal(a.getBase)
      val index = makeRVal(a.getIndex)
      ArrayReference(baseVar, makeRVal(a.getIndex))
    case a : NewArrayExpr =>
      NewCommand(JimpleFlowdroidWrapper.stringNameOfType(a.getType))
    case a : ClassConstant =>
      val t = IRParser.parseReflectiveRef(a.getValue)
      ClassConst(t.sootString)
    case l : JLengthExpr =>
      ArrayLength(makeRVal(l.getOp).asInstanceOf[LocalWrapper])
    case s : JShrExpr => TopExpr(s.toString + " : JShrExpr")
    case s : JShlExpr => TopExpr(s.toString + " : JShlExpr")
    case s : JXorExpr => TopExpr(s.toString + " : JXorExpr")
    case s : JAndExpr => TopExpr(s.toString + " : JAndExpr")
    case s : JOrExpr => TopExpr(s.toString + " : JOrExpr")
    case s : JUshrExpr => TopExpr(s.toString + " : JUshrExpr")

    case v =>
      //println(v)
      throw CmdNotImplemented(s"Command not implemented: $v  type: ${v.getClass}")
  }
  protected def makeVal(box: Value):RVal = box match{
    case a : JimpleLocal=>
      LocalWrapper(a.getName,a.getType.toString)
    case f: AbstractInstanceFieldRef => {
      val fieldType = f.getType.toString
      val base = makeVal(f.getBase).asInstanceOf[LocalWrapper]
      val fieldname = f.getField.getName
      val fieldDeclType = f.getField.getDeclaringClass.toString
      FieldReference(base,fieldType, fieldDeclType, fieldname)
    }
    case a => makeRVal(a)
  }
  def makeCmd(cmd: soot.Unit, method: SootMethod,
                       locOpt:Option[AppLoc] = None): CmdWrapper = {
    val loc:AppLoc = locOpt.getOrElse(???)
    cmd match{
      case cmd: AbstractDefinitionStmt if cmd.rightBox.isInstanceOf[JCaughtExceptionRef] =>
        val leftBox = makeVal(cmd.leftBox.getValue).asInstanceOf[LVal]
        var exceptionName:String = ""
        method.getActiveBody.getTraps.forEach{trap =>
          if(trap.getHandlerUnit == cmd) exceptionName = JimpleFlowdroidWrapper.stringNameOfClass(trap.getException)
        }
        val rightBox = CaughtException(exceptionName)
        AssignCmd(leftBox, rightBox, loc)
      case cmd: AbstractDefinitionStmt => {
        val leftBox = makeVal(cmd.leftBox.getValue).asInstanceOf[LVal]
        val rightBox = makeVal(cmd.rightBox.getValue)
        AssignCmd(leftBox, rightBox,loc)
      }
      case cmd: JReturnStmt => {
        val box = makeVal(cmd.getOpBox.getValue)
        ReturnCmd(Some(box), loc)
      }
      case cmd:JInvokeStmt => {
        val invokeval = makeVal(cmd.getInvokeExpr).asInstanceOf[Invoke]
        InvokeCmd(invokeval, loc)
      }
      case _ : JReturnVoidStmt => {
        ReturnCmd(None, loc)
      }
      case cmd: JIfStmt =>
        val targetIfTrue = AppLoc(loc.method, JimpleLineLoc(cmd.getTarget, method), true)
        If(makeVal(cmd.getCondition),targetIfTrue,loc)
      case _ : JNopStmt =>
        NopCmd(loc)
      case _: JThrowStmt =>
        // TODO: exception being thrown
        ThrowCmd(loc)
      case _:JGotoStmt => NopCmd(loc) // control flow handled elsewhere
      case _:JExitMonitorStmt => NopCmd(loc) // ignore concurrency
      case _:JEnterMonitorStmt => NopCmd(loc) // ignore concurrency
      case sw:JLookupSwitchStmt =>
        val key = makeRVal(sw.getKey).asInstanceOf[LocalWrapper]
        val targets = sw.getTargets.asScala.map(u => makeCmd(u,method, locOpt))
        SwitchCmd(key,targets.toList,loc)
      case v =>
        throw CmdNotImplemented(s"Unimplemented command: ${v}")
    }
  }
}

trait CallGraphProvider{
  def edgesInto(method:SootMethod):Set[(SootMethod,soot.Unit)]
  def edgesOutOf(unit:soot.Unit):Set[SootMethod]
  def edgesOutOfMethod(method: SootMethod):Set[SootMethod]
}

/**
 * Compute an application only call graph
 * see Application-only Call Graph Construction, Karim Ali
 * @param cg
 */
class AppOnlyCallGraph(cg: CallGraph,
                       callbacks: Set[SootMethod],
                       wrapper: JimpleFlowdroidWrapper,
                       resolver: AppCodeResolver) extends CallGraphProvider {
  sealed trait PointLoc
  case class FieldPoint(clazz: SootClass, fname: String) extends PointLoc
  case class LocalPoint(method: SootMethod, locName:String) extends PointLoc
  // TODO: finish implementing this
//  var pointsTo = mutable.Map[PointLoc, Set[SootClass]]()
//  var icg = mutable.Map[soot.Unit, Set[SootMethod]]()
  var workList = callbacks.toList
  case class PTState(pointsTo: Map[PointLoc, Set[SootClass]],
                     callGraph : Map[soot.Unit, Set[SootMethod]],
                     registered: Set[SootClass]){
    def updateCallGraph(u: soot.Unit, newTargets:Set[SootMethod]):PTState = {
      val newCallSet = callGraph.getOrElse(u, Set()) ++ newTargets
      this.copy(callGraph = callGraph + (u -> newCallSet))
    }
    def updateLocal(method: SootMethod, name:String, clazz : Set[SootClass]): PTState = {
      val ptKey = LocalPoint(method,name)
      val updatedClasses = pointsTo.getOrElse(ptKey, Set()) ++ clazz
      this.copy(pointsTo=pointsTo+(ptKey-> updatedClasses))
    }
    def getLocal(method:SootMethod, name:String):Set[SootClass] = {
      pointsTo.get(LocalPoint(method,name)).getOrElse(Set())
    }
    def join(other:PTState):PTState ={
      val allPtKeys = other.pointsTo.keySet ++ pointsTo.keySet
      val newOther = allPtKeys.map{k => (k ->
        pointsTo.getOrElse(k,Set()).union(other.pointsTo.getOrElse(k,Set())))}.toMap
      val allUnits = callGraph.keySet.union(other.callGraph.keySet)
      val newCallGraph = allUnits.map{k =>
        (k -> callGraph.getOrElse(k,Set()).union(other.callGraph.getOrElse(k,Set())))}.toMap
      val newReg = registered.union(other.registered)
      PTState(newOther, newCallGraph, newReg)
    }
  }
  val emptyPt = PTState(Map(),Map(),Set())
//  val hierarchy = Scene.v().getActiveHierarchy
  def initialParamForCallback(method:SootMethod, state:PTState):PTState = {
    ???
  }
  def cmdTransfer(state:PTState, cmd:CmdWrapper):PTState = {
    val method = cmd.getLoc.method.asInstanceOf[JimpleMethodLoc].method
    cmd match {
      case ReturnCmd(Some(LocalWrapper(name,_)), loc) =>
        val varPt = state.getLocal(method,name)
        state.updateLocal(method,"@ret", varPt)
      case ReturnCmd(_,_) => state
      case AssignCmd(LocalWrapper(targetName,_), LocalWrapper(sourceName, _), loc) =>
        val srcPt = state.getLocal(method, sourceName)
        state.updateLocal(method,targetName, srcPt)
      case InvokeCmd(method, loc) => ???
      case _ => state
    }
  }

  def processMethod(method:SootMethod, state:PTState) : (PTState, List[SootMethod]) = {
    val stateWithFwkBackAdded = if(callbacks.contains(method)){
      initialParamForCallback(method,state)
    }else state
    val returns = wrapper.makeMethodRetuns(JimpleMethodLoc(method)).toSet.map((v: AppLoc) =>
      BounderUtil.cmdAtLocationNopIfUnknown(v,wrapper).mkPre)

    val newPt: Map[CmdWrapper, PTState] = BounderUtil.graphFixpoint[CmdWrapper, PTState](start = returns,state,emptyPt,
      next = n => wrapper.commandPredecessors(n).map((v: AppLoc) =>
        BounderUtil.cmdAtLocationNopIfUnknown(v,wrapper).mkPre).toSet,
      comp = (acc,v) => ???,
      join = (a,b) => a.join(b)
    )


    ???
  }
  @tailrec
  private def iComputePt(workList: Queue[SootMethod], state: PTState): PTState = {
    if(workList.isEmpty) state else {
      val head = workList.front
      val (state1,nextWL) = processMethod(head, state)
      iComputePt(workList.tail ++ nextWL, state1)
    }
  }
//  val callbacks = resolver.getCallbacks
  val allFwkClasses = Scene.v().getClasses.asScala.filter(c =>
    resolver.isFrameworkClass(JimpleFlowdroidWrapper.stringNameOfClass(c))).toSet
  val ptState = iComputePt(Queue.from(callbacks),PTState(Map(), Map(), allFwkClasses))

  override def edgesInto(method : SootMethod): Set[(SootMethod,soot.Unit)] = {
    ???
  }

  override def edgesOutOf(unit: soot.Unit): Set[SootMethod] = {
    ptState.callGraph(unit)
  }

  override def edgesOutOfMethod(method: SootMethod): Set[SootMethod] = ???
}

/**
 * A call graph wrapper that patches in missing edges from CHA
 * missing edges are detected by call sites with no outgoing edges
 * @param cg
 */
class PatchingCallGraphWrapper(cg:CallGraph, appMethods: Set[SootMethod]) extends CallGraphProvider{
  val unitToTargets: MapView[SootMethod, Set[(SootMethod,soot.Unit)]] =
    appMethods.flatMap{ outerMethod =>
      if(outerMethod.hasActiveBody){
        outerMethod.getActiveBody.getUnits.asScala.flatMap{unit =>
          val methods = edgesOutOf(unit)
          methods.map(m => (m,(outerMethod,unit)))
        }
      }else{Set()}
    }.groupBy(_._1).view.mapValues(l => l.map(_._2))

  def edgesInto(method : SootMethod): Set[(SootMethod,soot.Unit)] = {
    unitToTargets.getOrElse(method, Set())
  }

  def findMethodInvoke(clazz : SootClass, method: SootMethodRef) : Option[SootMethod] =
    if(clazz.declaresMethod(method.getSubSignature))
      Some(clazz.getMethod(method.getSubSignature))
    else{
      if(clazz.hasSuperclass){
        val superClass = clazz.getSuperclass
        findMethodInvoke(superClass, method)
      }else None
    }

  private def baseType(sType: Value): SootClass = sType match{
    case l : JimpleLocal if l.getType.isInstanceOf[RefType] =>
      l.getType.asInstanceOf[RefType].getSootClass
    case v : JimpleLocal if v.getType.isInstanceOf[ArrayType]=>
      // Arrays inherit Object methods such as clone and toString
      // We consider both as callins when invoked on arrays
      Scene.v().getSootClass("java.lang.Object")
    case v =>
      println(v)
      ???
  }

  private def fallbackOutEdgesInvoke(v : Value):Set[SootMethod] = v match{
    case v : JVirtualInvokeExpr =>
      // TODO: is base ever not a local?
      val base = v.getBase
      val reachingObjects = JimpleFlowdroidWrapper.subThingsOf(baseType(base))
      val ref: SootMethodRef = v.getMethodRef
      val out = reachingObjects.flatMap(findMethodInvoke(_, ref))
      Set(out.toList:_*).filter(m => !m.isAbstract)
    case i : JInterfaceInvokeExpr =>
      val base = i.getBase.asInstanceOf[JimpleLocal]
      val reachingObjects =
        JimpleFlowdroidWrapper.subThingsOf(base.getType.asInstanceOf[RefType].getSootClass)
      val ref: SootMethodRef = i.getMethodRef
      val out = reachingObjects.flatMap(findMethodInvoke(_, ref)).filter(m => !m.isAbstract)
      Set(out.toList:_*)
    case i : JSpecialInvokeExpr =>
      val m = i.getMethod
      assert(!m.isAbstract, "Special invoke of abstract method?")
      Set(m)
    case i : JStaticInvokeExpr =>
      val method = i.getMethod
      Set(method)
    case v => Set() //Non invoke methods have no edges
  }

  private def fallbackOutEdges(unit: soot.Unit): Set[SootMethod] = unit match{
    case j: JAssignStmt => fallbackOutEdgesInvoke(j.getRightOp)
    case j: JInvokeStmt => fallbackOutEdgesInvoke(j.getInvokeExpr)
    case _ => Set()
  }
  def edgesOutOf(unit: soot.Unit): Set[SootMethod] = {
    val out = cg.edgesOutOf(unit).asScala.map(e => e.tgt())
    if(out.isEmpty) {
      fallbackOutEdges(unit)
    } else out.toSet
  }
  def edgesOutOfMethod(method: SootMethod):Set[SootMethod] = {
    val cgOut = cg.edgesOutOf(method).asScala.map(e => e.tgt()).toSet
    if(method.hasActiveBody) {
      method.getActiveBody.getUnits.asScala.foldLeft(cgOut) {
        case (ccg, unit) if !cg.edgesOutOf(unit).hasNext => ccg ++ edgesOutOf(unit)
        case (ccg, _) => ccg
      }
    }else cgOut
  }
}

class CallGraphWrapper(cg: CallGraph) extends CallGraphProvider{
  def edgesInto(method : SootMethod): Set[(SootMethod,soot.Unit)] = {
    val out = cg.edgesInto(method).asScala.map(e => (e.src(),e.srcUnit()))
    out.toSet
  }

  def edgesOutOf(unit: soot.Unit): Set[SootMethod] = {
    val out = cg.edgesOutOf(unit).asScala.map(e => e.tgt())
    out.toSet
  }
  def edgesOutOfMethod(method: SootMethod):Set[SootMethod] = {
    cg.edgesOutOf(method).asScala.map(e => e.tgt()).toSet
  }
}

class JimpleFlowdroidWrapper(apkPath : String,
                             callGraphSource: CallGraphSource) extends IRWrapper[SootMethod, soot.Unit] {

  BounderSetupApplication.loadApk(apkPath, callGraphSource)


//  private var unitGraphCache : scala.collection.mutable.Map[Body, EnhancedUnitGraphFixed] =
//    scala.collection.mutable.Map()
  private var appMethodCache : scala.collection.mutable.Set[SootMethod] = scala.collection.mutable.Set()

  val resolver = new DefaultAppCodeResolver[SootMethod, soot.Unit](this)

  val callbacks: Set[SootMethod] = resolver.getCallbacks.flatMap{
    case JimpleMethodLoc(method) => Some(method)
  }

  var id = 0
  private val entryMethodTypeToLocal = mutable.HashMap[Type, Local]()
  def freshSootVar(t: Type,locals: Chain[Local], units: Chain[soot.Unit], globalField:SootField):Local = {
    if (entryMethodTypeToLocal.contains(t)){
      entryMethodTypeToLocal(t)
    }else {
      val tId = id
      id = id + 1
      val name = "tmplocal" + tId
      val newLocal = Jimple.v().newLocal(name, t)
      locals.add(newLocal)
      val assign = Jimple.v().newAssignStmt(Jimple.v.newStaticFieldRef(globalField.makeRef()), newLocal)
      units.add(assign)
      entryMethodTypeToLocal.addOne(t -> newLocal)
      newLocal
    }
  }
  private val fwkInstantiatedClasses = mutable.Set[SootClass]()

  private val initialClasses = Set("android.app.Activity", "androidx.fragment.app.Fragment",
    "android.app.Fragment", "android.view.View", "android.app.Application") //TODO:
  def canReflectiveRef(c: SootClass): Boolean = {

    val strName = JimpleFlowdroidWrapper.stringNameOfClass(c)
    if(initialClasses.contains(strName)){
      true
    }else if(c.hasSuperclass){
      canReflectiveRef(c.getSuperclass)
    }else{
      false
    }
  }

  def fwkInstantiate(entryMethod:SootMethod, c:SootClass,globalField:SootField):Unit = {
    val fwkCanInit = resolver.isFrameworkClass(JimpleFlowdroidWrapper.stringNameOfClass(c)) || canReflectiveRef(c)
    if(!fwkInstantiatedClasses.contains(c) && fwkCanInit) {
      val entryPointBody = entryMethod.getActiveBody
      val units = entryPointBody.getUnits
      val locals = entryPointBody.getLocals
      val recVar: Local = freshSootVar(c.getType, locals,units,globalField)
      val assignRec = Jimple.v().newAssignStmt(recVar, Jimple.v().newNewExpr(c.getType))
      units.add(assignRec)
      fwkInstantiatedClasses.add(c)
      val hierarchy: Hierarchy = Scene.v().getActiveHierarchy
//      val subclasses = hierarchy.getDirectSubclassesOf(c)
//      subclasses.asScala.foreach{c2 => fwkInstantiate(entryMethod, c2)}
    }
  }

  private val objectClazz = Scene.v().getSootClass("java.lang.Object")
  def getFwkObj(entryMethod: SootMethod, c:SootClass, globalField:SootField, instantiate:Boolean = true):Local = {
    if(instantiate){
      fwkInstantiate(entryMethod, c,globalField)
    }
    val entryPointBody = entryMethod.getActiveBody
    val units = entryPointBody.getUnits
    val locals: Chain[Local] = entryPointBody.getLocals
    val recVar: Local = freshSootVar(objectClazz.getType, locals,units,globalField)
    val ref: StaticFieldRef = Jimple.v().newStaticFieldRef(globalField.makeRef())
    val get = Jimple.v().newAssignStmt(recVar, ref)
    val castRecVar:Local = freshSootVar(c.getType, locals,units,globalField)
    units.add(get)
    val cast = Jimple.v().newAssignStmt(castRecVar, Jimple.v().newCastExpr(recVar, c.getType))
    units.add(cast)
//    val assignGlobal = Jimple.v().newAssignStmt(ref,recVar)
//    units.add(assignGlobal)
    castRecVar
  }
  def getFwkValue(entryMethod: SootMethod, t:Type, globalField:SootField):Local = t match {
    case v:RefType =>
      getFwkObj(entryMethod, v.getSootClass, globalField)
    case v =>
      ???
  }
  def addCallbackToMain(entryMethod: SootMethod, cb:SootMethod, globalField:SootField) = {
    val entryPointBody = entryMethod.getActiveBody
    val units = entryPointBody.getUnits
    val args = cb.getParameterTypes.asScala.map{paramType => getFwkValue(entryMethod, paramType, globalField)}
    //TODO: if non-void assign result to global field
    if (cb.isStatic) {
      val invoke = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(cb.makeRef, args.asJava))
      units.add(invoke)
    } else {
      val recVar = getFwkObj(entryMethod, cb.getDeclaringClass,  globalField)

      val invoke = Jimple.v().newInvokeStmt(Jimple.v()
        .newSpecialInvokeExpr(recVar, cb.makeRef(), args.asJava))
      units.add(invoke)
    }
  }


  def buildSparkCallGraph() = {
//    Scene.v().setEntryPoints(callbacks.toList.asJava)
    val appClasses: Set[SootClass] = getAppMethods(resolver).flatMap { a =>
      val cname = JimpleFlowdroidWrapper.stringNameOfClass(a.getDeclaringClass)
      if (!resolver.isFrameworkClass(cname))
        Some(a.getDeclaringClass)
      else None
    }
    appClasses.foreach { (c: SootClass) =>
      c.setApplicationClass()
    }

    val opt = Map(
      ("vta", "true"),
      ("enabled", "true"),
//      ("types-for-sites", "true"),
      //        ("field-based", "true"),
      //        ("simple-edges-bidirectional", "true"),
      //        ("geom-app-only", "true"),
      ("simulate-natives", "true"),
      ("propagator", "worklist"),
      ("verbose", "true"),
      ("on-fly-cg", "true"),
      ("merge-stringbuffer", "true")
//      ("dump-html","true") //TODO: disable for performance
//      ("lazy-pts", "true")
      //        ("set-impl", "double"),
      //        ("double-set-old", "hybrid"),
      //        ("double-set-new", "hybrid")
    )
//    CHATransformer.v().transform()
    val appMethodList: List[SootMethod] = resolver.appMethods.toList.map(v => v.asInstanceOf[JimpleMethodLoc].method)
    Scene.v().setReachableMethods(new ReachableMethods(Scene.v().getCallGraph, appMethodList.asJava))
    val reachable2 = Scene.v().getReachableMethods
    reachable2.update()

    Options.v().set_whole_program(true)
    Scene.v().addBasicClass(JimpleFlowdroidWrapper.cgEntryPointName,SootClass.HIERARCHY)
    val entryPoint = Scene.v().getSootClass(JimpleFlowdroidWrapper.cgEntryPointName)
    entryPoint.setApplicationClass()
    entryPoint.setInScene(true)

    entryPoint.setSuperclass(objectClazz)


    val globalField: SootField = Scene.v.makeSootField("global", objectClazz.getType,
      Modifier.PUBLIC.|(Modifier.STATIC))
    entryPoint.addField(globalField)
    val newMethodName: String = "main"
    val paramTypes = List[Type]().asJava
    val returnType = Scene.v().getType("void")
    val modifiers = Modifier.PUBLIC | Modifier.STATIC
    val exceptions = List[SootClass]().asJava
    val entryMethod: SootMethod = Scene.v().makeSootMethod(newMethodName, paramTypes, returnType, modifiers, exceptions)
    entryPoint.addMethod(entryMethod)
    entryMethod.setPhantom(false)
    val entryPointBody = Jimple.v().newBody(entryMethod)
    entryMethod.setActiveBody(entryPointBody)
    entryPointBody.insertIdentityStmts(entryPoint)
    callbacks.foreach { cb => addCallbackToMain(entryMethod, cb, globalField)}
    entryPointBody.getUnits.add(Jimple.v().newReturnVoidStmt())
//    entryPointBody.validate()
    Scene.v().setEntryPoints(List(entryMethod).asJava)
    SparkTransformer.v().transform("", opt.asJava)
  }

  val cg: CallGraphProvider = callGraphSource match{
    case SparkCallGraph =>
      buildSparkCallGraph()
      new CallGraphWrapper(Scene.v().getCallGraph)
    case CHACallGraph =>
      Scene.v().setEntryPoints(callbacks.toList.asJava)
      CHATransformer.v().transform()
      new CallGraphWrapper(Scene.v().getCallGraph)
    case AppOnlyCallGraph =>
      val chacg: CallGraph = Scene.v().getCallGraph
      new AppOnlyCallGraph(chacg, callbacks, this, resolver)
    case FlowdroidCallGraph => new CallGraphWrapper(Scene.v().getCallGraph)
    case PatchedFlowdroidCallGraph =>
      new PatchingCallGraphWrapper(Scene.v().getCallGraph, getAppMethods(resolver))
  }

  private def cmdToLoc(u : soot.Unit, containingMethod:SootMethod): AppLoc = {
    AppLoc(JimpleMethodLoc(containingMethod),JimpleLineLoc(u,containingMethod),false)
  }

  protected val getUnitGraph: Body => EnhancedUnitGraphFixed = Memo.mutableHashMapMemo {b =>
    // Soot EnhancedUnitGraph is not thread safe
    this.synchronized {
      new EnhancedUnitGraphFixed(b)
    }
  }
  protected def getAppMethods(resolver: AppCodeResolver):Set[SootMethod] = {
    if(appMethodCache.isEmpty) {
      val classes = Scene.v().getApplicationClasses
      classes.forEach(c =>
        if (resolver.isAppClass(c.getName))
           c.methodIterator().forEachRemaining(m => {
             var simulated:Boolean = false
             // simulated code tags added to flowdroid additions
             m.getTags.forEach(t =>
               simulated = simulated || t.isInstanceOf[SimulatedCodeElementTag])
             if(!simulated)
              appMethodCache.add(m)
           })
      )
    }
    appMethodCache.toSet
  }


  def getClassByName(className:String):Iterable[SootClass] = {
    if(Scene.v().containsClass(className))
      List(Scene.v().getSootClass(className))
    else {
      val nameMatcher = className.r
      val classOpt = Scene.v().getClasses.asScala.filter { c => nameMatcher.matches(c.getName) }
      classOpt
    }
  }
  override def findMethodLoc(className: String, methodName: String):Iterable[JimpleMethodLoc] = {
    val classesFound = getClassByName(className)
    val res = classesFound.flatMap { clazzFound =>
      val clazz = if (clazzFound.isPhantom) {
        None
      } else {
        Some(clazzFound)
      }
      val method: Option[SootMethod] = clazz.flatMap(a => try {
        val method1 = a.getMethod(methodName)
        Some(method1)
      } catch {
        case t: RuntimeException if t.getMessage.startsWith("No method") =>
          val mNameReg = methodName.r
          val sootM = clazz.map { c =>
            val mForC = c.getMethods.asScala
            mForC.find(m => mNameReg.matches(m.getName))
          }
          sootM.getOrElse(throw t)
        case t: Throwable => throw t
      })
      method.map(a => JimpleMethodLoc(a))
    }
    res
  }
  def findMethodLocRegex(className: String, methodName: Regex):Option[JimpleMethodLoc] = {
    val methodRegex: Regex = methodName
    val res: Iterable[SootClass] = getClassByName(className)
    assert(res.size != 1, s"Found wrong number (${res.size}) of classes for $className $methodName")
    val clazzFound = res.head
    val clazz = if(clazzFound.isPhantom){None} else {Some(clazzFound)}
    val method: Option[SootMethod] = clazz.flatMap(a => try{
      //      Some(a.getMethod(methodName))
      var methodsFound : List[SootMethod] = Nil
      a.getMethods.forEach{ m =>
        if (methodRegex.matches(m.getSubSignature))
          methodsFound = m::methodsFound
      }
      assert(methodsFound.size > 0, s"findMethodLoc found no methods matching regex ${methodName}")
      assert(methodsFound.size <2, s"findMethodLoc found multiple methods matching " +
        s"regex ${methodName} \n   methods ${methodsFound.mkString(",")}")
      Some(methodsFound.head)
    }catch{
      case t:RuntimeException if t.getMessage.startsWith("No method") =>
        None
      case t:Throwable => throw t
    })
    method.map(a=> JimpleMethodLoc(a))
  }
  override def getAllMethods: Iterable[MethodLoc] = {
    Scene.v().getApplicationClasses.asScala.flatMap(clazz => {
      clazz.getMethods.asScala
        .filter(!_.hasTag("SimulatedCodeElementTag")) // Remove simulated code elements from Flowdroid
        .map(JimpleMethodLoc)
    })
  }


  override def makeCmd(cmd: soot.Unit, method: SootMethod,
                       locOpt:Option[AppLoc] = None): CmdWrapper = JimpleFlowdroidWrapper.makeCmd(cmd,method,locOpt)

  override def degreeOut(cmd : AppLoc) = {
    val ll = cmd.line.asInstanceOf[JimpleLineLoc]
    val unitGraph = getUnitGraph(ll.method.retrieveActiveBody())
    unitGraph.getSuccsOf(ll.cmd).size()
  }

  override def degreeIn(cmd: AppLoc): Int = {
    val ll = cmd.line.asInstanceOf[JimpleLineLoc]
    val unitGraph = getUnitGraph(ll.method.retrieveActiveBody())
    unitGraph.getPredsOf(ll.cmd).size()
  }

  private val memLoopHeadOld = Memo.mutableHashMapMemo{(cmd:AppLoc) => {
    val ll = cmd.line.asInstanceOf[JimpleLineLoc]
    val unitGraph = getUnitGraph(ll.method.retrieveActiveBody())
    val scmd: soot.Unit = ll.cmd
    val predsOfTarget = unitGraph.getPredsOf(scmd)

    @tailrec
    def iFindCycle(workList:List[soot.Unit], visited: Set[soot.Unit]):Boolean =
      if(workList.isEmpty)
        false
      else {
        val head = workList.head
        val tail = workList.tail
        if(visited.contains(head))
          iFindCycle(tail,visited)
        else {
          val predsOfHead = unitGraph.getPredsOf(head)
          if (predsOfHead.contains(scmd))
            true
          else {
            val successors = unitGraph.getSuccsOf(head).asScala.toList
            iFindCycle(successors ++ tail, visited + head)
          }
        }
      }
    if (predsOfTarget.size() < 2){
      false
    }else {
      iFindCycle(unitGraph.getSuccsOf(scmd).asScala.toList, Set())
    }
  }}
  private val memoGetMethodLoops = Memo.mutableHashMapMemo{(m:SootMethod) =>
    val finder = new LoopFinder()
    finder.getLoops(m.getActiveBody).asScala.map(l => l.getHead)
  }
  override def isLoopHead(cmd: AppLoc): Boolean = {
    val ll = cmd.line.asInstanceOf[JimpleLineLoc]
    ll.cmd match{
      case s:Stmt => {
        val method = cmd.method.asInstanceOf[JimpleMethodLoc].method
        val loops: mutable.Set[Stmt] = memoGetMethodLoops(method)
        if(loops.isEmpty)
          false
        else {
          val out = loops.contains(s)
          out
        }
      }
      case i =>
        throw new IllegalStateException(s"Got $i which is not a Stmt, " +
          s"TODO: figure out when we would get a Unit that is not a Stmt here.")
    }
  }

  private val iTopoForMethod: SootMethod => Map[soot.Unit, Int] = Memo.mutableHashMapMemo {
    (method:SootMethod) => {
      val unitGraph: EnhancedUnitGraphFixed = getUnitGraph(method.retrieveActiveBody())
      val topo = new SlowPseudoTopologicalOrderer[soot.Unit]()
      val uList = topo.newList(unitGraph, false).asScala.zipWithIndex
      uList.toMap
    }

  }
  override def commandTopologicalOrder(cmdWrapper:CmdWrapper):Int = {
    cmdWrapper.getLoc match {
      case AppLoc(JimpleMethodLoc(_), JimpleLineLoc(cmd, sootMethod), _) => {
        val topo = iTopoForMethod(sootMethod)
        topo(cmd)
      }
      case v =>
        throw new IllegalStateException(s"Bad argument for commandTopologicalOrder ${v}")
    }
  }
  override def commandPredecessors(cmdWrapper : CmdWrapper):List[AppLoc] =
    cmdWrapper.getLoc match{
    case AppLoc(methodWrapper @ JimpleMethodLoc(_),JimpleLineLoc(cmd,sootMethod), true) => {
      val unitGraph = getUnitGraph(sootMethod.retrieveActiveBody())
      val predCommands = unitGraph.getPredsOf(cmd).asScala
      predCommands.map(cmd => AppLoc(methodWrapper,JimpleLineLoc(cmd,sootMethod), false)).toList
    }
    case v =>
        throw new IllegalStateException(s"Bad argument for command predecessor ${v}")
  }
  override def commandNext(cmdWrapper: CmdWrapper):List[AppLoc] =
    cmdWrapper.getLoc match{
      case AppLoc(method, line, _) => List(AppLoc(method,line,true))
      case _ =>
        throw new IllegalStateException("command after pre location doesn't exist")
    }

  private val iCmdAtLocation: AppLoc => CmdWrapper = Memo.mutableHashMapMemo {
    case loc@AppLoc(_, JimpleLineLoc(cmd, method), _) => makeCmd(cmd, method, Some(loc))
    case loc => throw new IllegalStateException(s"No command associated with location: ${loc}")
  }
  override def cmdAtLocation(loc: AppLoc):CmdWrapper = iCmdAtLocation(loc)

  protected def makeRVal(box:Value):RVal = JimpleFlowdroidWrapper.makeRVal(box)

  protected def makeVal(box: Value):RVal = JimpleFlowdroidWrapper.makeVal(box)

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
    val loc: Iterable[JimpleMethodLoc] = findMethodLoc(className, methodName)
    loc.flatMap(loc => {
      val activeBody = loc.method.retrieveActiveBody()
      val units: Iterable[soot.Unit] = activeBody.getUnits.asScala
      val unitsForLine = units.filter(a => a.getJavaSourceStartLineNumber == line)
      unitsForLine.map((a:soot.Unit) => AppLoc(loc, JimpleLineLoc(a,loc.method),true))
    })
  }

  def makeMethodTargets(source: MethodLoc): Set[MethodLoc] = {
    val edgesOut:Set[MethodLoc] =
      cg.edgesOutOfMethod(source.asInstanceOf[JimpleMethodLoc].method).map(JimpleMethodLoc)
    val withoutClInit:Set[MethodLoc] = edgesOut.filter{
      case JimpleMethodLoc(m) => m.getName != "<clinit>"
      case _ => throw new IllegalStateException()
    }
    withoutClInit
  }

  override def makeInvokeTargets(appLoc: AppLoc): UnresolvedMethodTarget = {
    val line = appLoc.line.asInstanceOf[JimpleLineLoc]
    val edgesOut = cg.edgesOutOf(line.cmd)

    // A class may be statically initialized at any location where it is first used
    // Soot adds a <clinit> edge to any static invoke site.
    // We assume that <clinit> is a callback for simplicity.
    // This is an unsound assumption but one that is unlikely to affect results of the analysis.
    // Note that handling <clinit> in a sound way for a flow sensitive analysis is difficult.
    // <clinit> for different classes can be interleved arbitrarily to resolve circular dependencies.
    val edgesWithoutClInit = edgesOut.filter{edge =>
      edge.getName != "<clinit>"
    }

    val mref = appLoc.line match {
      case JimpleLineLoc(cmd: JInvokeStmt, _) => cmd.getInvokeExpr.getMethodRef
      case JimpleLineLoc(cmd: JAssignStmt, _) if cmd.getRightOp.isInstanceOf[JVirtualInvokeExpr] =>
        cmd.getRightOp.asInstanceOf[JVirtualInvokeExpr].getMethodRef
      case JimpleLineLoc(cmd: JAssignStmt, _) if cmd.getRightOp.isInstanceOf[JInterfaceInvokeExpr] =>
        cmd.getRightOp.asInstanceOf[JInterfaceInvokeExpr].getMethodRef
      case JimpleLineLoc(cmd: JAssignStmt, _) if cmd.getRightOp.isInstanceOf[JSpecialInvokeExpr] =>
        cmd.getRightOp.asInstanceOf[JSpecialInvokeExpr].getMethodRef
      case JimpleLineLoc(cmd: JAssignStmt, _) if cmd.getRightOp.isInstanceOf[JStaticInvokeExpr] =>
        cmd.getRightOp.asInstanceOf[JStaticInvokeExpr].getMethodRef
      case t =>
        throw new IllegalArgumentException(s"Bad Location Type $t")
    }
    val declClass = mref.getDeclaringClass
    val clazzName = declClass.getName
    val name = mref.getSubSignature

    UnresolvedMethodTarget(clazzName, name.toString,edgesWithoutClInit.map(f => JimpleMethodLoc(f)))
  }

  def canAlias(type1: String, type2: String): Boolean = {
    val oneIsPrimitive = List(type1,type2).exists{
      case ClassHierarchyConstraints.Primitive() => true
      case _ => false
    }
    if(oneIsPrimitive)
      return false
    if(type1 == type2) true else {
      val hierarchy: Hierarchy = Scene.v().getActiveHierarchy
      assert(Scene.v().containsClass(type1), s"Type: $type1 not in soot scene")
      assert(Scene.v().containsClass(type2), s"Type: $type2 not in soot scene")
      val type1Soot = Scene.v().getSootClass(type1)
      val type2Soot = Scene.v().getSootClass(type2)
      val sub1 = JimpleFlowdroidWrapper.subThingsOf(type1Soot)
      val sub2 = JimpleFlowdroidWrapper.subThingsOf(type2Soot)
      sub1.exists(a => sub2.contains(a))
    }
  }

  override def getOverrideChain(method: MethodLoc): Seq[MethodLoc] = {
    val m = method.asInstanceOf[JimpleMethodLoc]
    val methodDeclClass = m.method.getDeclaringClass
    val methodSignature = m.method.getSubSignature
    val superclasses: util.List[SootClass] = Scene.v().getActiveHierarchy.getSuperclassesOf(methodDeclClass)
    val interfaces: Chain[SootClass] = methodDeclClass.getInterfaces
    val methods = (superclasses.iterator.asScala ++ interfaces.iterator.asScala)
      .filter(sootClass => sootClass.declaresMethod(methodSignature))
      .map( sootClass=> JimpleMethodLoc(sootClass.getMethod(methodSignature)))
    methods.toList
  }

  //TODO: check that this function covers all cases
  private val callSiteCache = mutable.HashMap[MethodLoc, Seq[AppLoc]]()
  override def appCallSites(method_in: MethodLoc, resolver:AppCodeResolver): Seq[AppLoc] = {
    val method = method_in.asInstanceOf[JimpleMethodLoc]
    callSiteCache.getOrElse(method, {
      val m = method.asInstanceOf[JimpleMethodLoc]
      val sootMethod = m.method
      val incomingEdges = cg.edgesInto(sootMethod)
      val appLocations: Seq[AppLoc] = incomingEdges.flatMap{
        case (method,unit) =>
          val className = JimpleFlowdroidWrapper.stringNameOfClass(method.getDeclaringClass)
          if (!resolver.isFrameworkClass(className)){
            Some(cmdToLoc(unit, method))
          }else None
      }.toSeq
      callSiteCache.put(method_in, appLocations)
      appLocations
    })
  }

  private val iMakeMethodReturns = Memo.mutableHashMapMemo {(method:MethodLoc)=>
    this.synchronized{
      val smethod = method.asInstanceOf[JimpleMethodLoc]
      val rets = mutable.ListBuffer[AppLoc]()
      try{
        smethod.method.getActiveBody()
      }catch{
        case t: Throwable =>
        //println(t)
      }
      if (smethod.method.hasActiveBody) {
        smethod.method.getActiveBody.getUnits.forEach((u: soot.Unit) => {
          if (u.isInstanceOf[JReturnStmt] || u.isInstanceOf[JReturnVoidStmt]) {
            val lineloc = JimpleLineLoc(u, smethod.method)
            rets.addOne(AppLoc(smethod, lineloc, false))
          }
        })
        rets.toList
      }else{
        // TODO: for some reason no active bodies for R or BuildConfig generated classes?
        // note: these typically don't have any meaningful implementation anyway
        val classString = smethod.method.getDeclaringClass.toString
        if (! (classString.contains(".R$") || classString.contains("BuildConfig") || classString.endsWith(".R"))){
          //TODO: figure out why some app methods don't have active bodies
          //        println(s"Method $method has no active body, consider adding it to FrameworkExtensions.txt")
        }
        List()
      }
    }
  }
  override def makeMethodRetuns(method: MethodLoc): List[AppLoc] = {
    iMakeMethodReturns(method)
  }

  override def getInterfaces: Set[String] = {
    val out = Scene.v().getClasses.asScala.filter(_.isInterface).toSet.map(JimpleFlowdroidWrapper.stringNameOfClass)
    out
  }

  override def getClassHierarchy: Map[String, Set[String]] = {
    val hierarchy: Hierarchy = Scene.v().getActiveHierarchy
    Scene.v().getClasses().asScala.foldLeft(Map[String, Set[String]]()){ (acc,v) =>
      val cname = JimpleFlowdroidWrapper.stringNameOfClass(v)
      val subclasses = if(v.isInterface()) {
        hierarchy.getImplementersOf(v)
      }else {
        try {
          hierarchy.getSubclassesOf(v)
        }catch {
          case _: NullPointerException =>
            assert(v.toString.contains("$$Lambda") || cname == JimpleFlowdroidWrapper.cgEntryPointName)
            List[SootClass]().asJava // Soot bug with lambdas
        }
      }
      val strSubClasses = subclasses.asScala.map(c =>
        JimpleFlowdroidWrapper.stringNameOfClass(c)).toSet + cname
      acc  + (cname -> strSubClasses)
    }
  }

  /**
   * NOTE: DO NOT USE Scene.v.getActiveHierarchy.{isSuperClassOf...,isSubClassOf...}
   *      Above methods always return true if a parent is a phantom class
   * Check if one class is a subtype of another
   * Also returns true if they are equal
   * @param type1 possible supertype
   * @param type2 possible subtype
   * @return if type2 is subtype or equal to type2
   */
  override def isSuperClass(type1: String, type2: String): Boolean = {
    val type1Soot = Scene.v().getSootClass(type1)
    val type2Soot = Scene.v().getSootClass(type2)
    val subclasses = Scene.v.getActiveHierarchy.getSubclassesOfIncluding(type1Soot)
    val res = subclasses.contains(type2Soot)
    res
  }
}

case class JimpleMethodLoc(method: SootMethod) extends MethodLoc {
  def string(clazz: SootClass):String = JimpleFlowdroidWrapper.stringNameOfClass(clazz)
  def string(t:Type) :String = JimpleFlowdroidWrapper.stringNameOfType(t)
  override def simpleName: String = {
//    val n = method.getName
    method.getSubSignature
  }

  override def bodyToString: String = if(method.hasActiveBody) method.getActiveBody.toString else ""

  override def classType: String = string(method.getDeclaringClass)

  // return type, receiver type, arg1, arg2 ...
  override def argTypes: List[String] = string(method.getReturnType)::
    classType::
    method.getParameterTypes.asScala.map(string).toList

  /**
   * None for reciever if static
   * @return list of args, [reciever, arg1,arg2 ...]
   */
  override def getArgs: List[Option[LocalWrapper]] = {
    val clazz = string(method.getDeclaringClass)
    val params =
      (0 until method.getParameterCount).map(ind =>
        Some(LocalWrapper("@parameter" + s"$ind", string(method.getParameterType(ind)))))
    val out = (if (method.isStatic) None else Some(LocalWrapper("@this",clazz)) ):: params.toList
    //TODO: this method is probably totally wrong, figure out arg names and how to convert type to string
    out
  }

  override def isStatic: Boolean = method.isStatic

  override def isInterface: Boolean = method.getDeclaringClass.isInterface
}
case class JimpleLineLoc(cmd: soot.Unit, method: SootMethod) extends LineLoc{
  override def toString: String = "line: " + cmd.getJavaSourceStartLineNumber() + " " + cmd.toString()
  def returnTypeIfReturn :Option[String] = cmd match{
    case cmd :JReturnVoidStmt => Some("void")
    case _ =>
      ???
  }

  override def lineNumber: Int = cmd.getJavaSourceStartLineNumber
}

