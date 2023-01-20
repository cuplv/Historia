package edu.colorado.plv.bounder.ir

import better.files.File
import edu.colorado.plv.bounder.BounderSetupApplication.{ApkSource, SourceType}

import java.util
import java.util.{Collections, Objects}
import edu.colorado.plv.bounder.ir.SootWrapper.cgEntryPointName
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, LSSpec, OAbsMsg, SetSignatureMatcher, Signature, SignatureMatcher, SubClassMatcher}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecSpace}
import edu.colorado.plv.bounder.lifestate.SpecSpace.allI
import edu.colorado.plv.bounder.{BounderSetupApplication, BounderUtil}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor._
import edu.colorado.plv.fixedsoot.{EnhancedUnitGraphFixed, SparkTransformerDBG}
import scalaz.Memo
import soot.jimple.internal._
import soot.jimple.spark.SparkTransformer
import soot.jimple.toolkits.callgraph.{CHATransformer, CallGraph, ReachableMethods, TopologicalOrderer}
import soot.jimple._
import soot.jimple.spark.pag.{AllocNode, Node, PAG}
import soot.jimple.spark.sets.{DoublePointsToSet, EmptyPointsToSet, HybridPointsToSet, P2SetVisitor}
import soot.jimple.toolkits.annotation.logic.LoopFinder
import soot.jimple.toolkits.pointer.{DumbPointerAnalysis, FullObjectSet}
import soot.options.Options
import soot.toolkits.graph.pdg.EnhancedUnitGraph
import soot.toolkits.graph.{PseudoTopologicalOrderer, SlowPseudoTopologicalOrderer, UnitGraph}
import soot.util.Chain
import soot.{AnySubType, ArrayType, Body, BooleanType, ByteType, CharType, DoubleType, EquivTo, FloatType, G, Hierarchy, IntType, Local, LongType, Modifier, PackManager, PointsToSet, RefType, Scene, ShortType, SootClass, SootField, SootMethod, SootMethodRef, Type, Value}
import upickle.default.{macroRW, ReadWriter => RW}

import scala.annotation.tailrec
import scala.collection.immutable.Queue
import scala.collection.{BitSet, MapView, mutable}
import scala.jdk.CollectionConverters._
import scala.util.matching.Regex

object SootWrapper{
  val cgEntryPointName:String = "CgEntryPoint___________a____b"
  def stringNameOfClass(m : SootClass): String = {
    val name = m.getName
//    s"${m.getPackageName}.${name}"
    name
  }
  def stringNameOfType(t : Type) : String = t match {
    case v:AnySubType =>
      throw new IllegalStateException("String name of type only applicable to single types")
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
      LocalWrapper(local.getName, SootWrapper.stringNameOfType(local.getType))
    case cast: JCastExpr =>
      val castType = SootWrapper.stringNameOfType(cast.getCastType)
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
      val declaringClass = SootWrapper.stringNameOfClass(staticRef.getFieldRef.declaringClass())
      val fieldName = staticRef.getFieldRef.name()
      val containedType = SootWrapper.stringNameOfType(staticRef.getFieldRef.`type`())
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
      val targetClassType = SootWrapper.stringNameOfType(i.getCheckType)
      val target = makeRVal(i.getOp).asInstanceOf[LocalWrapper]
      InstanceOf(targetClassType, target)
    case a : ArrayRef =>
      val baseVar = makeRVal(a.getBase)
      val index = makeRVal(a.getIndex)
      ArrayReference(baseVar, makeRVal(a.getIndex))
    case a : NewArrayExpr =>
      NewCommand(SootWrapper.stringNameOfType(a.getType))
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
    case s : JRemExpr => TopExpr(s.toString + " : JRemExpr")
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
                       loc:AppLoc): CmdWrapper = {
    cmd match{
      case cmd: AbstractDefinitionStmt if cmd.rightBox.isInstanceOf[JCaughtExceptionRef] =>
        val leftBox = makeVal(cmd.leftBox.getValue).asInstanceOf[LVal]
        var exceptionName:String = ""
        method.getActiveBody.getTraps.forEach{trap =>
          if(trap.getHandlerUnit == cmd) exceptionName = SootWrapper.stringNameOfClass(trap.getException)
        }
        val rightBox = CaughtException(exceptionName)
        AssignCmd(leftBox, rightBox, loc)
      case cmd: AbstractDefinitionStmt => {
        val leftBox = makeVal(cmd.leftBox.getValue).asInstanceOf[LVal]
        val rightBox = makeVal(cmd.rightBox.getValue)
        //assert(loc.line.asInstanceOf[JimpleLineLoc].cmd == cmd)
        AssignCmd(leftBox, rightBox,loc)
      }
      case cmd: JReturnStmt => {
        val box = makeVal(cmd.getOpBox.getValue)
        //assert(loc.line.asInstanceOf[JimpleLineLoc].cmd == cmd)
        ReturnCmd(Some(box), loc)
      }
      case cmd:JInvokeStmt => {
        val invokeval = makeVal(cmd.getInvokeExpr).asInstanceOf[Invoke]
        //val jll = loc.line.asInstanceOf[JimpleLineLoc].cmd
        //assert(jll.isInstanceOf[JLookupSwitchStmt] || jll == cmd)
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
        val targets = sw.getTargets.asScala.map (u => makeCmd (u, method, loc) ).toList
        makeRVal(sw.getKey) match {
          case key:LocalWrapper =>
            SwitchCmd (Some(key), targets, loc)
          case intConst:IntConst =>
            SwitchCmd(None, targets.drop(intConst.v),loc)
          case other => //I really hope the java compiler can't put other crap here?
            throw new IllegalStateException(s"${other} as expr in switch statement.")
        }
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
                       wrapper: SootWrapper,
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
    resolver.isFrameworkClass(SootWrapper.stringNameOfClass(c))).toSet
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
      val reachingObjects = SootWrapper.subThingsOf(baseType(base))
      val ref: SootMethodRef = v.getMethodRef
      val out = reachingObjects.flatMap(findMethodInvoke(_, ref))
      Set(out.toList:_*).filter(m => !m.isAbstract)
    case i : JInterfaceInvokeExpr =>
      val base = i.getBase.asInstanceOf[JimpleLocal]
      val reachingObjects =
        SootWrapper.subThingsOf(base.getType.asInstanceOf[RefType].getSootClass)
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
    val out = cg.edgesOutOf(unit).asScala.map(e => e.tgt()).toSet
    out
  }
  def edgesOutOfMethod(method: SootMethod):Set[SootMethod] = {
    cg.edgesOutOf(method).asScala.map(e => e.tgt()).toSet
  }
}

/**
 * Expose functionality of Soot/spark to analysis
 * //TODO: make this fully contain soot functionality
 * @param apkPath path to app under analysis
 * @param callGraphSource Spark app only, flowdroid, cha etc.
 * @param toOverride set of LSSpec or abstract messages to override
 *                   callbacks that may be missing (e.g. onResume so that onPause may be executed)
 */
class SootWrapper(apkPath : String,
                  toOverride:Set[_<:Any], //TODO: use more precise type
                  callGraphSource: CallGraphSource = SparkCallGraph,
                  sourceType:SourceType = ApkSource
                            ) extends IRWrapper[SootMethod, soot.Unit] {
  case class Messages(cbSize:Int, cbMsg:Int, matchedCb:Int, matchedCbRet:Int,
                      ciCallGraph:Int, matchedCiCallGraph:Int,
                      syntCi:Int, matchedSyntCi:Int)

  /**
   * print methods and points to regions for all classes containing the classFilter string
   * @param classFilter
   * @return
   */
  override def dumpDebug(classFilter:String): String= {
    val classes =
      Scene.v().getClasses.asScala.filter(c => c.getName.contains(classFilter) || c.getName.contains("CgEntryPoint"))
    val methods = classes.flatMap(c => c.getMethods.asScala)
    val stringBuilder = new StringBuilder()
    def varAndPtRegions(m:MethodLoc, v: LocalWrapper):String = {
      val ptRegions = pointsToSet(m,v)
      s"var: ${v.name}, ptRegions: $ptRegions"
    }
    methods.foreach(m => {
      if(m.hasActiveBody) {
        val vars = m.getActiveBody.getUnits.asScala.flatMap { c =>
          val methodLoc = JimpleMethodLoc(m)
          val ml = SootWrapper.makeCmd(c, m, AppLoc(methodLoc, JimpleLineLoc(c, m), true))
          ml match {
            case ReturnCmd(Some(returnVar: LocalWrapper), loc) => Set(varAndPtRegions(methodLoc, returnVar))
            case AssignCmd(target: LocalWrapper, source, loc) => Set(varAndPtRegions(methodLoc, target))
            case InvokeCmd(method, loc) => method.params.flatMap {
              case p: LocalWrapper => Some(varAndPtRegions(methodLoc, p))
              case _ => None
            }
            case If(b, trueLoc, loc) => Set.empty
            case NopCmd(loc) => Set.empty
            case SwitchCmd(key, targets, loc) => Set.empty
            case ThrowCmd(loc) => Set.empty
            case _ => Set.empty
          }
          //        s"${v.getName}:${pointsToSet(ml,lw)}"}
        }.toSet
        stringBuilder.append(s"=========${m.getDeclaringClass.getName} ${m.getName}\n${m.getActiveBody}\n ${vars.mkString("\n")}\n\n")
      }else{
        stringBuilder.append(s"=========${m.getDeclaringClass.getName} ${m.getName}\n  " +
          s"THE SOOT HAS DEEMED THIS METHOD TO HAVE NO ACTIVE BODY!!!\n\n")
      }
    })
    stringBuilder.toString()
  }
  object Messages{
    implicit val rw:RW[Messages] = macroRW
  }
  def getMessages(cfResolver:ControlFlowResolver[SootMethod, soot.Unit], spec:SpecSpace,
                  ch : ClassHierarchyConstraints):Messages ={

    val mFilter = (strm:String) => {
      !strm.contains("MainActivity") &&
        !strm.contains("com.example.createdestroy.R$") &&
        strm !=("com.example.createdestroy.R")
    }
    val cb = resolver.getCallbacks.filter{m =>
      val strm = m.classType
      mFilter(strm)
    }
    val allcalls = cb.flatMap(cfResolver.computeAllCalls(_,true))
    val callins: Set[MethodLoc] = allcalls.filter(c => resolver.isFrameworkClass(c.classType))
    val callinsNoToSTR = callins.filter(c => !c.simpleName.contains("toString()"))
    val allI = spec.allI
    val matchedCallins = callins.filter(c => allI.exists(i => i.contains(CIExit, Signature(c.classType, c.simpleName))(ch)))
    val matchedCallbacks = cb.flatMap(c =>
      allI.flatMap(i =>
        List(CBEnter,CBExit).flatMap{d =>
          if(i.contains(d,Signature(c.classType,c.simpleName))(ch)) Some((d,c)) else None
        }
      ))
    val cbsimp = cb.map(c => c.simpleName)
    val callinssimp = callins.map(c => c.simpleName)
    val matchedCallinssimp = matchedCallins.map(c => c.simpleName)
    val matchedCallbackssimp = matchedCallbacks.map(c => (c._1, c._2.simpleName))

    val syntCallinSites = getAppMethods(resolver).flatMap {
      case method:SootMethod => getUnitGraph(method.getActiveBody).asScala.flatMap{u =>
        if(mFilter(method.getDeclaringClass.getName) &&Scene.v().getCallGraph.edgesOutOf(u).hasNext &&
          u.toString().contains("(") && !u.toString().contains("newarray (")) {
          val loc = AppLoc(JimpleMethodLoc(method), JimpleLineLoc(u, method), false)
          val callinSet = resolver.resolveCallLocation(makeInvokeTargets(loc)).flatMap {
            case CallinMethodReturn(sig) => Some(sig)
            case CallinMethodInvoke(sig) => Some(sig)
            case GroupedCallinMethodInvoke(targetClasses, fmwName) => ???
            case GroupedCallinMethodReturn(targetClasses, fmwName) => ???
            case _ => None
          }
          if (callinSet.nonEmpty) {
//            val matchedBySpec = allI.filter(i => callinSet.exists(m => i.contains(CIExit, (m._1,m._2))(ch)))
            val matchedBySpec = callinSet.filter(c => allI.exists(i => i.contains(CIExit, c)(ch)))
            Some((method, u, matchedBySpec,callinSet))
          } else
            None
        }else None
      }
      case _ => ???
    }
    val syntCallinSitesInSpec = syntCallinSites.filter(_._3.nonEmpty)

    val callinCallGraphSize = syntCallinSites.toList.map(v => v._4.size).sum
    val matchedCallinCallGraphSize = syntCallinSites.toList.map(v => v._3.size).sum
//    val callinCallGraphSize =callins.size  // old count was based on total call graph callins
    Messages(cb.size, cb.size*2, matchedCb = matchedCallbacks.count(_._1 == CBEnter),
        matchedCbRet = matchedCallbacks.count(_._1 == CBExit),
      ciCallGraph = callinCallGraphSize, matchedCiCallGraph = matchedCallinCallGraphSize,
      syntCi = syntCallinSites.size, matchedSyntCi = syntCallinSitesInSpec.size)
  }


  BounderSetupApplication.loadApk(apkPath, sourceType)


//  private val preInstrumentationCha =
//    new ClassHierarchyConstraints(getClassHierarchy,getInterfaces)

  private val appMethodCache : scala.collection.mutable.Set[SootMethod] = scala.collection.mutable.Set()

  val resolver = new DefaultAppCodeResolver[SootMethod, soot.Unit](this)


  // ** Instrument framework methods to generate app only call graph **
  // TODO: factor these out into their own class
  private var id = 0
  private val entryMethodTypeToLocal = mutable.HashMap[(SootMethod,Type), Local]()
  def freshSootVar(method:SootMethod,t: Type,locals: Chain[Local]):Local = {
    if (entryMethodTypeToLocal.contains((method,t))){
      entryMethodTypeToLocal((method,t))
    }else {
      val tId = id
      id = id + 1
      val name = "tmplocal" + tId
      val newLocal = Jimple.v().newLocal(name, t)
      locals.add(newLocal)
//      val assign = Jimple.v().newAssignStmt(Jimple.v.newStaticFieldRef(globalField.makeRef()), newLocal)
//      units.add(assign)
      entryMethodTypeToLocal.addOne((method,t) -> newLocal)
      newLocal
    }
  }

  private def dummyClassForFrameworkClass(c:SootClass):SootClass = {
    val pkg = c.getPackageName
    val name = "Dummy_______" + c.getShortName
    val dummyClass = Scene.v().getSootClass(pkg + "." + name)
    dummyClass.setLibraryClass()
//    val someField: SootField = Scene.v.makeSootField("someField", objectClazz.getType,
//      Modifier.PUBLIC)
//    dummyClass.addField(someField)
    val dummyType = dummyClass.getType
    val anySubType = AnySubType.v(dummyType)
    dummyType.setAnySubType(anySubType)
//    dummyClass.setApplicationClass()
    dummyClass.setInScene(true)
    if(c.isInterface){
      dummyClass.addInterface(c)
      dummyClass.setSuperclass(objectClazz)
    }else{
      dummyClass.setSuperclass(c)
    }
    dummyClass.setModifiers(Modifier.PUBLIC)
    val methodsToImplement = c.getMethods.asScala
    methodsToImplement.foreach{ m =>
      if(m.isPublic) {
        val mName = m.getName
        val mParams = m.getParameterTypes
        val mRetT = m.getReturnType
        val mModifiers = m.getModifiers & ( ~Modifier.ABSTRACT)
        val newMethod = Scene.v().makeSootMethod(mName, mParams, mRetT, mModifiers)
        dummyClass.addMethod(newMethod)
        newMethod.setPhantom(false)
        val body = Jimple.v().newBody(newMethod)
        body.insertIdentityStmts(dummyClass)
        newMethod.setActiveBody(body)
        instrumentSootMethod(newMethod)
      }

    }
    val newMethodName: String = "<init>"
    val paramTypes = List[Type]().asJava
    val returnType = Scene.v().getType("void")
    val modifiers = Modifier.PUBLIC | Modifier.CONSTRUCTOR
    val exceptions = List[SootClass]().asJava
    val entryMethod: SootMethod = Scene.v().makeSootMethod(newMethodName,
      paramTypes, returnType, modifiers, exceptions)
    dummyClass.addMethod(entryMethod)

//    Scene.v().addBasicClass(pkg + "." + name,SootClass.HIERARCHY)
    Scene.v().addBasicClass(pkg + "." + name,SootClass.BODIES)
    dummyClass.validate()
    dummyClass
  }
  private def instrumentSootMethod(method: SootMethod, registerArgs:Boolean = true):Unit = {
    method.getDeclaringClass.setApplicationClass()
    method.setPhantom(false)
    if(!method.hasActiveBody){
      //TODO:============ create active body for methods that don't have one
      //TODO: does this work?
      //TODO: this may be the source of remaining cg imprecision?

      val entryPointBody = Jimple.v().newBody(method)
      if(!method.isConcrete()){
        // instrument native methods
        val mod = method.getModifiers & ( ~Modifier.NATIVE ) & ( ~ Modifier.ABSTRACT )
        method.setModifiers(mod)
      }
      method.setActiveBody(entryPointBody)
    }
    method.getDeclaringClass.setInScene(true)
    // Retrieve global field representing all values pointed to by the framework
    val entryPoint = Scene.v().getSootClass(SootWrapper.cgEntryPointName)
    val globalField = entryPoint.getFieldByName("global")
    assert(globalField.getType.toString == "java.lang.Object")

    val unitChain = method.getActiveBody.getUnits

    // Remove exceptions from body
    method.getActiveBody.getTraps.clear()

    unitChain.clear()
    method.getActiveBody.asInstanceOf[JimpleBody].insertIdentityStmts(method.getDeclaringClass)
    // Write receiver to global field
    if(!method.isStatic){
      val ident = unitChain.getFirst
      val receiver = ident.asInstanceOf[JIdentityStmt].getLeftOp
      assert(receiver.isInstanceOf[JimpleLocal])
      // Receiver added to global framework points to set
      if(registerArgs) {
        unitChain.add(
          Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(globalField.makeRef()), receiver)
        )
      }
    }
    // write all parameters to global field
    val parmIdents = unitChain.asScala.flatMap{
      case i:JIdentityStmt if i.getLeftOp.toString().contains(s"parameter") => Some(i)
      case _ => None
    }.toList

    if(registerArgs) {
      parmIdents.foreach { i =>
        val t = i.getRightOp.getType
        t match{
          case _:RefType =>
            unitChain.add(Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(globalField.makeRef()), i.getLeftOp))
          case _ =>
            ()
        }
      }
    }

    //read global field cast to correct type and return
    if(method.getReturnType.toString == "void"){
      unitChain.add(Jimple.v().newReturnVoidStmt())
    } else{
      // get global static field, cast to correct type and return
      val v = getFwkValue(method, method.getReturnType, globalField, false)
      unitChain.add(Jimple.v().newReturnStmt(v))
    }
    method.getActiveBody.validate()

  }
  private def instrumentCallins(): Unit ={
    Scene.v().getClasses.asScala.foreach{c =>
      if(!c.isInterface && resolver.isFrameworkClass(SootWrapper.stringNameOfClass(c))){
        c.getMethods.asScala.foreach { m =>
          // exclude synthetic entry point from instrumentation
          if((m.getDeclaringClass.getName != cgEntryPointName)) {
            //Don't write receiver of default constructor to global var
            instrumentSootMethod(m, m.getSubSignature != "void <init>()")
          }
        }
      }
    }


  }
  private val fwkInstantiatedClasses = mutable.Set[SootClass]()

  private val initialClasses = Set("android.app.Activity", "androidx.fragment.app.Fragment",
    "android.app.Fragment", "android.view.View", "android.app.Application","androidx.appcompat.app.AppCompatActivity") //TODO:
  /**
   * Classes that the android framework may create on its own.
   * These are things like fragments and activities that are declared in the XML file.
   * //TODO: an improved version of this would scan the xml file for references
   * @param c target class in the android app
   * @return true if the framework can reflectively initialize
   */
  def canReflectiveRef(c: SootClass): Boolean = {

    val strName = SootWrapper.stringNameOfClass(c)
    if(initialClasses.contains(strName)){
      true
    }else if(c.hasSuperclass){
      canReflectiveRef(c.getSuperclass)
    }else{
      false
    }
  }

  private def findInstantiable(c:SootClass):Option[SootClass] = {
    val ch = Scene.v().getActiveHierarchy
    if(c.isInterface || c.isAbstract){
      val sub = if(c.isInterface) ch.getDirectImplementersOf(c) else ch.getDirectSubclassesOf(c)
      sub.asScala.collectFirst{
        case subClass if findInstantiable(subClass).isDefined =>
          findInstantiable(subClass).get
      }
    }else
      Some(c)
  }
  private def fwkInstantiate(entryMethod:SootMethod, c:SootClass,globalField:SootField):Unit = {
    val fwkCanInit = resolver.isFrameworkClass(SootWrapper.stringNameOfClass(c)) || canReflectiveRef(c)
    if(fwkCanInit) {
      val entryPointBody = entryMethod.getActiveBody
      val units = entryPointBody.getUnits
      val locals = entryPointBody.getLocals
      val recVar: Local = freshSootVar(entryMethod,c.getType, locals)
      c.getType match{
        case _:RefType =>
          units.add(Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(globalField.makeRef()), recVar))
        case _ =>
          ()
      }
      findInstantiable(c).foreach { inst =>
        val assignRec = Jimple.v().newAssignStmt(recVar, Jimple.v().newNewExpr(inst.getType))
        units.add(assignRec)
      }
//      val hierarchy: Hierarchy = Scene.v().getActiveHierarchy
//      val subclasses = hierarchy.getDirectSubclassesOf(c)
//      subclasses.asScala.foreach{c2 => fwkInstantiate(entryMethod, c2)}
    }
  }

  private val objectClazz = Scene.v().getObjectType().getSootClass()
  private def getFwkObj(method: SootMethod, c:SootClass, globalField:SootField, instantiate:Boolean = true):Local = {
    if(instantiate){
      fwkInstantiate(method, c,globalField)
    }
    val body = method.getActiveBody
    val units = body.getUnits
    val locals: Chain[Local] = body.getLocals
    val recVar: Local = freshSootVar(method,objectClazz.getType, locals)
    val ref: StaticFieldRef = Jimple.v().newStaticFieldRef(globalField.makeRef())
    val get = Jimple.v().newAssignStmt(recVar, ref)
    //TODO: removed cast since it seems to be causing issues, see if this causes different issues
//    val castRecVar:Local = freshSootVar(method,c.getType, locals,units,globalField)
    units.add(get)
//    val cast = Jimple.v().newAssignStmt(castRecVar, Jimple.v().newCastExpr(recVar, c.getType))
//    units.add(cast)
    val assignGlobal = Jimple.v().newAssignStmt(ref,recVar)
    units.add(assignGlobal)
//    castRecVar
    recVar
  }
  private def localForPrim(method:SootMethod, t:Type, v:Value, globalField:SootField):Local = {
    val units = method.getActiveBody.getUnits
    val freshV = freshSootVar(method, t, method.getActiveBody.getLocals)
    units.add(Jimple.v().newAssignStmt(freshV, v))
    freshV
  }

  private def getFwkValue(entryMethod: SootMethod, t:Type, globalField:SootField, instantiate:Boolean):Local = t match {
    case v:RefType =>
      getFwkObj(entryMethod, v.getSootClass, globalField,instantiate)
    case v:IntType =>
      localForPrim(entryMethod,v, IntConstant.v(0), globalField)
    case v:BooleanType =>
      localForPrim(entryMethod,v, IntConstant.v(0), globalField)
    case v:FloatType =>
      localForPrim(entryMethod,v,FloatConstant.v(0.0.floatValue()), globalField)
    case v:DoubleType =>
      localForPrim(entryMethod,v, DoubleConstant.v(0.0), globalField)
    case v:LongType =>
      localForPrim(entryMethod,v,LongConstant.v(0.0.toLong), globalField)
    case v =>
      localForPrim(entryMethod,v, NullConstant.v(),globalField)
  }
  private def addCallbackToMain(entryMethod: SootMethod, cb:SootMethod, globalField:SootField) = {
    val entryPointBody = entryMethod.getActiveBody
    val units = entryPointBody.getUnits
    val args = cb.getParameterTypes.asScala.map{paramType => getFwkValue(entryMethod, paramType, globalField,true)}
    //TODO: if non-void assign result to global field
    if (cb.isStatic) {
      val invoke = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(cb.makeRef, args.asJava))
      units.add(invoke)
    } else {
      val inst = if(!fwkInstantiatedClasses.contains(cb.getDeclaringClass)) {
        fwkInstantiatedClasses.add(cb.getDeclaringClass)
        true
      }else false
      val recVar = getFwkObj(entryMethod, cb.getDeclaringClass,  globalField, inst)

      val invoke = Jimple.v().newInvokeStmt(Jimple.v()
        .newSpecialInvokeExpr(recVar, cb.makeRef(), args.asJava))
      units.add(invoke)
    }
  }


  def buildSparkCallGraph() = {
    //    Scene.v().setEntryPoints(callbacks.toList.asJava)
    val appClasses: Set[SootClass] = getAppMethods(resolver).flatMap { a =>
      val cname = SootWrapper.stringNameOfClass(a.getDeclaringClass)
      if (!resolver.isFrameworkClass(cname)) {
        Some(a.getDeclaringClass)
      } else None
    }
    appClasses.foreach { (c: SootClass) =>
      c.setApplicationClass()
    }


    val appMethodList: List[SootMethod] = resolver.appMethods.toList.map(v => v.asInstanceOf[JimpleMethodLoc].method)
    Scene.v().setReachableMethods(new ReachableMethods(Scene.v().getCallGraph, appMethodList.asJava))
    val reachable2 = Scene.v().getReachableMethods
    reachable2.update()

    Options.v().set_whole_program(true)
//    Scene.v().addBasicClass(JimpleFlowdroidWrapper.cgEntryPointName, SootClass.HIERARCHY)
    Scene.v().addBasicClass(SootWrapper.cgEntryPointName, SootClass.BODIES)
    val entryPoint = Scene.v().getSootClass(SootWrapper.cgEntryPointName)
    entryPoint.setApplicationClass()
    entryPoint.setInScene(true)

    entryPoint.setSuperclass(objectClazz)
//    Scene.v().setMainClass(entryPoint) // Seems to break things, not sure what this does

    // global field is static field that we instrument so that all framework values are written to and read from
    val globalField: SootField = Scene.v.makeSootField("global", objectClazz.getType,
      Modifier.PUBLIC.|(Modifier.STATIC))
    entryPoint.addField(globalField)

    // main method provides entry point for soot and calls all callbacks with values from the global field
    val newMethodName: String = "main"
    val paramTypes = List[Type](
      ArrayType.v(Scene.v().getSootClass("java.lang.String").getType,1)).asJava
    val returnType = Scene.v().getType("void")
    val modifiers = Modifier.PUBLIC | Modifier.STATIC
    val exceptions = List[SootClass]().asJava
    val entryMethod: SootMethod = Scene.v().makeSootMethod(newMethodName,
      paramTypes, returnType, modifiers, exceptions)
    entryPoint.addMethod(entryMethod)
    entryMethod.setPhantom(false)
    val entryPointBody = Jimple.v().newBody(entryMethod)
    entryMethod.setActiveBody(entryPointBody)
    entryPointBody.insertIdentityStmts(entryPoint)

    // allocLocal is a local variable to write all framework values to
    val allocLocal = Jimple.v().newLocal("alloc", objectClazz.getType)
    entryPointBody.getLocals.add(allocLocal)

    Scene.v().getClasses.asScala.toList.foreach{v =>
      if(resolver.isFrameworkClass(SootWrapper.stringNameOfClass(v))) {
        // if framework interface with no implementors, make a dummy implementor
        if (v.isInterface && Scene.v().getActiveHierarchy.getImplementersOf(v).size() == 0) {
          val dummy = dummyClassForFrameworkClass(v)
          entryPointBody.getUnits.add(
            Jimple.v().newAssignStmt(allocLocal, Jimple.v().newNewExpr(dummy.getType))
          )
          val initMethod = dummy.getMethod("void <init>()")
          entryPointBody.getUnits.add(
            Jimple.v().newInvokeStmt(Jimple.v()
              .newSpecialInvokeExpr(allocLocal, initMethod.makeRef()))
          )
          entryPointBody.getUnits.add(
            Jimple.v().newAssignStmt(
              Jimple.v().newStaticFieldRef(globalField.makeRef()), allocLocal)
          )
        }
      }
    }
    // create new instance of each framework type and assign to allocLocal
    Scene.v().getClasses.asScala.toList.foreach{ v =>
      if(resolver.isFrameworkClass(SootWrapper.stringNameOfClass(v)) && !v.isInterface){
        v.setApplicationClass()
        entryPointBody.getUnits.add(
          Jimple.v().newAssignStmt(allocLocal, Jimple.v().newNewExpr(v.getType))
        )
      }
    }

    // assing alloc local to global static field
    entryPointBody.getUnits.add(Jimple.v().newAssignStmt(Jimple.v()
      .newStaticFieldRef(globalField.makeRef()), allocLocal))



    overrideCallbacks()
    resolver.invalidateCallbacks()

    // add each callback to main method
    resolver.getCallbacks.flatMap{
      case JimpleMethodLoc(method) => Some(method)
    }.foreach { cb => addCallbackToMain(entryMethod, cb, globalField) }

    // return statement validate and set entry points for spark analysis
    entryPointBody.getUnits.add(Jimple.v().newReturnVoidStmt())
    entryPointBody.validate()


//    val c = Scene.v().loadClassAndSupport(JimpleFlowdroidWrapper.cgEntryPointName)
    // swap callin bodies out so that they only read/write values to the global field
    instrumentCallins()

    Scene.v().setEntryPoints(List(entryMethod).asJava)

    Scene.v().releaseActiveHierarchy()
    Scene.v().releasePointsToAnalysis()
    Scene.v().releaseReachableMethods()
    Scene.v().releaseCallGraph()
    Scene.v().releaseFastHierarchy()

    val opt = Map(
      //        ("vta", "true"),
      ("enabled", "true"),
      //      ("types-for-sites", "true"),
      //        ("field-based", "true"),
      //("simple-edges-bidirectional", "true"),
      //        ("geom-app-only", "true"),
//      ("geom-pta", "true"), // enable context sensitivity in spark pta
//      ("geom-trans","true"),
      //("simulate-natives", "false"),
      ("propagator", "worklist"),
//      ("propagator", "iter"), // Did not solve issue
      ("verbose", "true"),
      ("on-fly-cg", "true"),
      //("double-set-old", "hybrid"),
      //("double-set-new", "hybrid"),
//      ("set-impl", "double"),
      ("apponly","false"),
//      ("dump-html","true"), //TODO: disable for performance
      ("ignore-types", "false"),
      //("merge-stringbuffer", "true")
      //      ("lazy-pts", "true")
    )
    CHATransformer.v().transform()
    SparkTransformer.v().transform("", opt.asJava)
  }
  val preCallbacks: Set[SootMethod] = resolver.getCallbacks.flatMap{
    case JimpleMethodLoc(method) => Some(method)
  }
  val cg: CallGraphProvider = callGraphSource match{
    case SparkCallGraph =>
      buildSparkCallGraph()
      new CallGraphWrapper(Scene.v().getCallGraph)
    case CHACallGraph =>
      ??? //TODO: spark call graph unsound don't use
      Scene.v().setEntryPoints(preCallbacks.toList.asJava)
      CHATransformer.v().transform()
      new CallGraphWrapper(Scene.v().getCallGraph)
    case AppOnlyCallGraph =>
      ??? //TODO: not used in a long time, test well
      val chacg: CallGraph = Scene.v().getCallGraph
      new AppOnlyCallGraph(chacg, preCallbacks, this, resolver)
  }



  def getAllPtRegions():Map[Int,String] = {
    val pt = Scene.v().getPointsToAnalysis
    pt match{
      case _:DumbPointerAnalysis => Map()
      case v:PAG =>
        val out = mutable.HashMap[Int,String]()
        v.getAllocNodeNumberer.forEach(n => {
          val number = n.getNumber
          val typeName = SootWrapper.stringNameOfType(n.getType)
          assert(!out.contains(number) || out(number) == typeName, s"Malformed number $number for node ${n}")
          out.addOne(number, typeName)
        })
        v.allocSources().forEach(n => {
          val number = n.getNumber
          val typeName = SootWrapper.stringNameOfType(n.getType)
          assert(!out.contains(number) || out(number) == typeName, s"Malformed number $number for node ${n}")
          out.addOne(number, typeName)
        })
        out.toMap
      case _ =>
        throw new IllegalArgumentException()
    }
  }
  val cha =
    new ClassHierarchyConstraints(getClassHierarchy,getInterfaces,getAllPtRegions()) //TODO: get int values from pt for types

  override def getClassHierarchyConstraints:ClassHierarchyConstraints = cha
  // ** Override all overridable callbacks that affect spec **
  private def overrideCallbacks():Unit = {
    val ch = Scene.v.getActiveHierarchy
    val cha =
      new ClassHierarchyConstraints(getClassHierarchy,getInterfaces,getAllPtRegions())

    val appClasses: Set[String] = resolver.appMethods.map(m => m.classType)
    def findSuperMatching(sc:SootClass, sig:SignatureMatcher):Option[SootMethod] = {
      val sName = SootWrapper.stringNameOfClass(sc)
      val current = sc.getMethods.asScala.find{m =>
        val methodSignature = m.getSubSignature
        sig.matches(Signature(sName, methodSignature))(cha)
      }
      if(current.isEmpty && sc != Scene.v().getObjectType.getSootClass){
        findSuperMatching(sc.getSuperclass, sig)
      }else current
    }
    def overrideNonExistentCallback(c:SootClass, m:SootMethod):Unit = {
      val mName = m.getName
      val mod = m.getModifiers & (~ Modifier.ABSTRACT)
      val retType = m.getReturnType
      val parType = m.getParameterTypes
      val newMethod = Scene.v().makeSootMethod(mName, parType, retType, mod)

      c.addMethod(newMethod)
      val body = Jimple.v().newBody(newMethod)
      body.insertIdentityStmts(c)
      newMethod.setActiveBody(body)

      val units = body.getUnits
      val invExpr = Jimple.v().newSpecialInvokeExpr(body.getThisLocal, m.makeRef(),
        body.getParameterLocals)
      if(SootWrapper.stringNameOfType(retType) == "void") {
        val invCmd = Jimple.v().newInvokeStmt(invExpr)
        units.add(invCmd)
        units.add(Jimple.v().newReturnVoidStmt())
      }else{
        val tmpLocal = Jimple.v().newLocal("tmp__", retType)
        body.getLocals.add(tmpLocal)
        val assignCmd = Jimple.v().newAssignStmt(tmpLocal,invExpr)
        units.add(assignCmd)
        units.add(Jimple.v().newReturnStmt(tmpLocal))
      }
      body.validate()
    }
    def overrideAllCBForI(sig: LifeState.SignatureMatcher):Unit = {
      val baseTypes: Set[String] = sig match{
        case SubClassMatcher(baseSubtypeOf, sig, ident) => baseSubtypeOf
        case SetSignatureMatcher(sigSet) => sigSet.collect{
          case Signature(c,_) => c
        }
      }
      baseTypes.foreach{t =>
        val sc = Scene.v().getSootClass(t)
        val subClasses: List[SootClass] = try{
          (if(sc.isInterface) ch.getImplementersOf(sc) else
            ch.getSubclassesOf(sc)).asScala.toList
        } catch{
          case _:NullPointerException => List() // TODO: figure out why soot does this
        }
        val appClassesImplementing = subClasses
          .filter(sc2 => appClasses.contains(SootWrapper.stringNameOfClass(sc2)))
        appClassesImplementing.foreach{c =>
          val callbackExists = c.getMethods.asScala.exists{m =>
            sig.matchesSubSig(m.getSubSignature)
          }
          if(!callbackExists) {
            val superMethod = findSuperMatching(c, sig)
            superMethod.foreach(superMethod => overrideNonExistentCallback(c,superMethod))
            c.validate()
          }
        }
      }
    }
    val iSet = toOverride.flatMap{
      case s:LSSpec => allI(s,includeRhs = false)
      case m:OAbsMsg => Set(m)
      case v => throw new IllegalArgumentException(s"I don't know how to override methods matching $v")
    }
    iSet.foreach {
      case OAbsMsg(CBExit, sig, _) => overrideAllCBForI(sig)
      case OAbsMsg(CBEnter, sig, _) => overrideAllCBForI(sig)
      case _ => ()
    }
  }


  private def cmdToLoc(u : soot.Unit, containingMethod:SootMethod): AppLoc = {
    AppLoc(JimpleMethodLoc(containingMethod),JimpleLineLoc(u,containingMethod),false)
  }

  protected val getUnitGraph: Body => UnitGraph = Memo.mutableHashMapMemo {b =>
    // Method bodies are not thread safe
    b.synchronized {
      new EnhancedUnitGraphFixed(b)
    }
  }
  protected def getAppMethods(resolver: AppCodeResolver):Set[SootMethod] = {
    if(appMethodCache.isEmpty) {
      val classes = Scene.v().getApplicationClasses
      classes.forEach(c =>
        if (resolver.isAppClass(c.getName))
           c.methodIterator().forEachRemaining(m => {
              appMethodCache.add(m)
           })
      )
    }
    appMethodCache.toSet
  }


  def getClassByName(className:String):Iterable[SootClass] = {
    val foundClasses = if(Scene.v().containsClass(className))
      List(Scene.v().getSootClass(className))
    else {
      val nameMatcher = className.r
      val classOpt = Scene.v().getClasses.asScala.filter { c => nameMatcher.matches(c.getName) }
      classOpt
    }
    if(foundClasses.isEmpty){
      println("+++ Available classes:")
      Scene.v().getClasses.forEach{clazz =>
        println(s"  = ${clazz.getName}")
      }
      throw new IllegalArgumentException(s"No classes found matching: $className")
    }else foundClasses
  }
  override def findMethodLoc(sig:Signature):Iterable[JimpleMethodLoc] = {
    val className = sig.base
    val methodName = sig.methodSignature
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
    if(res.isEmpty){
      println("+++ Available methods:")
      classesFound.foreach{clazz =>
        println(s"  ==class ${clazz.getName}")
        clazz.getMethods.forEach{method =>
          println(s"    -method ${method.getSignature}")
        }
      }
      throw new IllegalArgumentException(s"method $methodName not found.")
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

  override def degreeOut(cmd : AppLoc): Int = {
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
      case s:Stmt =>
        val method = cmd.method.asInstanceOf[JimpleMethodLoc].method
        val loops: mutable.Set[Stmt] = memoGetMethodLoops(method)
        if(loops.isEmpty)
          false
        else {
          val out = loops.contains(s)
          out
        }
      case i =>
        throw new IllegalStateException(s"Got $i which is not a Stmt, " +
          s"TODO: figure out when we would get a Unit that is not a Stmt here.")
    }
  }

  private val iTopoForMethod: SootMethod => Map[soot.Unit, Int] = Memo.mutableHashMapMemo {
    (method:SootMethod) => {
      val unitGraph: UnitGraph = getUnitGraph(method.retrieveActiveBody())
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
      predCommands.map(cmd => AppLoc(methodWrapper,JimpleLineLoc(cmd,sootMethod), isPre = false)).toList
    }
    case v =>
        throw new IllegalStateException(s"Bad argument for command predecessor ${v}")
  }
  override def commandNext(cmdWrapper: CmdWrapper):List[AppLoc] =
    cmdWrapper.getLoc match{
      case AppLoc(method, line, _) => List(AppLoc(method,line,isPre = true))
      case _ =>
        throw new IllegalStateException("command after pre location doesn't exist")
    }

//  private val iCmdAtLocation: AppLoc => CmdWrapper = Memo.mutableHashMapMemo {
//    case loc@AppLoc(_, JimpleLineLoc(cmd, method), _) =>
//      SootWrapper.makeCmd(cmd, method, loc)
//    case loc => throw new IllegalStateException(s"No command associated with location: ${loc}")
//  }
//  override def cmdAtLocation(loc: AppLoc):CmdWrapper = iCmdAtLocation(loc)

  val cmdCache = mutable.HashMap[soot.SootMethod, mutable.HashMap[AppLoc, CmdWrapper]]()
  override def cmdAtLocation(loc:AppLoc):CmdWrapper = {
    val method = loc.method.asInstanceOf[JimpleMethodLoc].method
    val cmap:mutable.HashMap[AppLoc,CmdWrapper] = if(!cmdCache.contains(method)) {
      val cmap: mutable.HashMap[AppLoc, CmdWrapper] = mutable.HashMap[AppLoc, CmdWrapper]()
      cmdCache.addOne(method -> cmap)
      cmap
    }else{ cmdCache(method)}

    if(!cmap.contains(loc)) {
      val line = loc.line.asInstanceOf[JimpleLineLoc]
      cmap.addOne(loc -> SootWrapper.makeCmd(line.cmd,method,loc))
    }
    cmap(loc)
  }

  protected def makeRVal(box:Value):RVal = SootWrapper.makeRVal(box)

  protected def makeVal(box: Value):RVal = SootWrapper.makeVal(box)

  override def isMethodEntry(cmdWrapper: CmdWrapper): Boolean = cmdWrapper.getLoc match {
    case AppLoc(_, JimpleLineLoc(cmd,method),true) => {
      val unitBoxes = method.retrieveActiveBody().getUnits
      if(unitBoxes.size > 0){
        cmd.equals(unitBoxes.getFirst)
      }else {false}
    }
    case AppLoc(_, _,false) => false // exit of command is not entry let transfer one more time
    case _ => false
  }

  override def findLineInMethod(sig:Signature, line: Int): Iterable[AppLoc] = {
    val loc: Iterable[JimpleMethodLoc] = findMethodLoc(sig)
    loc.flatMap(loc => {
      val activeBody = loc.method.retrieveActiveBody()
      val units: Iterable[soot.Unit] = activeBody.getUnits.asScala
      val unitsForLine = units.filter(a => a.getJavaSourceStartLineNumber == line)
      unitsForLine.map((a:soot.Unit) => AppLoc(loc, JimpleLineLoc(a,loc.method),isPre = true))
    })
  }

  def findInMethod(className:String, methodName:String, toFind: CmdWrapper => Boolean):Iterable[AppLoc] = {
    val locations = for{
      clazz <- getClassByName(className)
      method <- clazz.getMethods().asScala
      loc <- method.getActiveBody.getUnits.asScala.map(cmd => cmdToLoc(cmd, method))
    } yield loc
    assert(locations.nonEmpty, s"Empty target locations for query.\n" +
      s"Searching for class: ${className}, method: ${methodName}")
    val out = locations.filter(al => toFind(cmdAtLocation(al)))
    if(out.isEmpty)
      println(s"Class: ${className} and method: ${methodName} found, but no commands match search criteria.\n " +
        s"Commands found: ${locations.map(l => s"   $l").mkString("\n")}")
    out
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

    //TODO: why is shared preferences dummy not getting to call site?
    val dbg = false // TODO: switch to false for exp run
    def dbgInvTargetTypes(inv: InvokeExpr):Unit = {
      val pt = Scene.v().getPointsToAnalysis
      inv match{
        case vi: JVirtualInvokeExpr =>
          val base = vi.getBase.asInstanceOf[JimpleLocal]
          val ro = pt.reachingObjects(base)
          val types = ro.possibleTypes()
          println(types)
        case ifi: JInterfaceInvokeExpr =>
          val base = ifi.getBase.asInstanceOf[JimpleLocal]
          val t = base.getType match{
            case r:RefType =>
              val isIface = r.getSootClass.isInterface
              val isAbstr = r.getSootClass.isAbstract
              val impl = if(isIface) {
                Scene.v().getActiveHierarchy.getDirectImplementersOf(r.getSootClass)
              } else {Scene.v().getActiveHierarchy.getDirectSubclassesOf(r.getSootClass)}
              println(impl)

          }
          val ro = pt.reachingObjects(base)
          val types = ro.possibleTypes()
          println(types)
        case _ =>
          ???
      }
    }
    if(dbg && edgesOut.isEmpty)
      line.cmd match{
        case v : JInvokeStmt =>
          val invExpr = v.getInvokeExpr
          dbgInvTargetTypes(invExpr)
          println(v)
          ???
        case v: JAssignStmt =>
          val left = v.getRightOp
          left match{
            case e: InvokeExpr =>
              dbgInvTargetTypes(e)
              ???
            case v =>
              println(v)
              ???
          }
        case v =>
          println(v)
          ???
      }
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
      val sub1 = SootWrapper.subThingsOf(type1Soot)
      val sub2 = SootWrapper.subThingsOf(type2Soot)
      sub1.exists(a => sub2.contains(a))
    }
  }

  override def getOverrideChain(method: MethodLoc): Seq[MethodLoc] = {
    val m = method.asInstanceOf[JimpleMethodLoc]
    val methodDeclClass = m.method.getDeclaringClass
    val methodSignature = m.method.getSubSignature
    val superclasses: util.List[SootClass] = Scene.v().getActiveHierarchy.getSuperclassesOf(methodDeclClass)
    val interfaces: Iterable[SootClass] = methodDeclClass.getInterfaces.asScala.flatMap{iface =>
      Scene.v().getActiveHierarchy.getSuperinterfacesOfIncluding(iface).asScala
    }
    val methods = (superclasses.iterator.asScala ++ interfaces)
      .filter(sootClass => sootClass.declaresMethod(methodSignature))
      .map( sootClass=> JimpleMethodLoc(sootClass.getMethod(methodSignature)))
    methods.toList
  }

  //TODO: check that this function covers all cases
  private val callSiteCache = mutable.HashMap[MethodLoc, Seq[AppLoc]]()
  override def appCallSites(method_in: MethodLoc, resolver:AppCodeResolver): Seq[AppLoc] = {
    if(method_in.simpleName == "void <clinit>()")
      return List()
    val method = method_in.asInstanceOf[JimpleMethodLoc]
    callSiteCache.getOrElse(method, {
      val m = method.asInstanceOf[JimpleMethodLoc]
      val sootMethod = m.method
      val incomingEdges = cg.edgesInto(sootMethod)
      val appLocations: Seq[AppLoc] = incomingEdges.flatMap{
        case (method,unit) =>
          val className = SootWrapper.stringNameOfClass(method.getDeclaringClass)
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
    val out = Scene.v().getClasses.asScala.filter(_.isInterface).toSet.map(SootWrapper.stringNameOfClass)
    out
  }

  private def getClassHierarchy: Map[String, Set[String]] = {
    val hierarchy: Hierarchy = Scene.v().getActiveHierarchy
    Scene.v().getClasses().asScala.foldLeft(Map[String, Set[String]]()){ (acc,v) =>
      val cname = SootWrapper.stringNameOfClass(v)
      val subclasses = if(v.isInterface()) {
        hierarchy.getImplementersOf(v)
      }else {
        try {
          hierarchy.getSubclassesOf(v)
        }catch {
          case _: NullPointerException =>
//            assert(v.toString.contains("$$Lambda") || cname == JimpleFlowdroidWrapper.cgEntryPointName)
            List[SootClass]().asJava // Soot bug with lambdas // also generated classes have no subclasses
        }
      }
      val strSubClasses = subclasses.asScala.map(c =>
        SootWrapper.stringNameOfClass(c)).toSet + cname
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

  private val jimpleGetBitSet : DoublePointsToSet =>BitSet = Memo.mutableHashMapMemo{ pt =>
    val out = mutable.BitSet()
    val oldSet = pt.getOldSet.asInstanceOf[HybridPointsToSet]
    val newSet = pt.getNewSet.asInstanceOf[HybridPointsToSet]
    List(oldSet,newSet).foreach(_.forall((n: Node) => out.add(n.getNumber)))
    out
  }

  override def pointsToSet(loc: MethodLoc, local: LocalWrapper): TypeSet = {
    if (ClassHierarchyConstraints.Primitive.matches(local.localType)){
      return PrimTypeSet(local.localType)
    }
    val sootMethod = loc.asInstanceOf[JimpleMethodLoc].method
    val pt = Scene.v().getPointsToAnalysis
    val ptSet: Option[Local] = if(local.name.contains("@parameter")) {
      val index = local.name.split("@parameter")(1).toInt
      val paramRef = sootMethod.getActiveBody.getParameterRefs.get(index)
      val paramAssign = sootMethod.getActiveBody.getUnits.asScala.flatMap{
        case j: JIdentityStmt if j.rightBox.getValue == paramRef =>
          Some(j.leftBox.getValue.asInstanceOf[Local])
        case _ => None
      }
      assert(paramAssign.size == 1)
      Some(paramAssign.head)
    } else {
      sootMethod.getActiveBody.getLocals.asScala.find(l => l.getName == local.name)
    }

    val reaching: PointsToSet = ptSet match{
      case Some(sootLocal) =>
        pt.reachingObjects(sootLocal)
      case None if local.name == "@this" =>
        try {
          pt.reachingObjects(sootMethod.getActiveBody.getThisLocal)
        }catch {
          case e:RuntimeException =>
            throw e
        }
      case None =>
        throw new IllegalStateException(s"No points to set for method: ${loc} and local: ${local}")
    }
    reaching match{
      case d:DoublePointsToSet =>
        BitTypeSet(jimpleGetBitSet(d))
      case e:EmptyPointsToSet =>
        EmptyTypeSet
      case _:FullObjectSet =>
        TopTypeSet
    }
  }

  override def getThisVar(methodLoc: Loc): Option[LocalWrapper] = {
    methodLoc.containingMethod.flatMap{getThisVar}
  }
  override def getThisVar(methodLoc: MethodLoc): Option[LocalWrapper] = {
    methodLoc match {
      case JimpleMethodLoc(method) if method.isStatic => None
      case JimpleMethodLoc(method) =>
        val l = method.getActiveBody.getThisLocal
        Some(LocalWrapper(l.getName, SootWrapper.stringNameOfType(l.getType)))
      case _ => throw new IllegalArgumentException()
    }
  }

  override def appCallbackMsgCount: Int = {
    //TODO:======
    ???
  }

  override def allMethodLocations(m: MethodLoc): Set[AppLoc] = m match{
    case m:JimpleMethodLoc =>
      if(m.method.hasActiveBody)
        m.method.getActiveBody.getUnits.asScala.map{u => cmdToLoc(u,m.method)}.toSet
      else Set.empty
    case _ => throw new IllegalArgumentException()
  }
}

case class JimpleMethodLoc(method: SootMethod) extends MethodLoc {
  def string(clazz: SootClass):String = SootWrapper.stringNameOfClass(clazz)
  def string(t:Type) :String = SootWrapper.stringNameOfType(t)
  override def simpleName: String = {
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
  lazy val cmdString: String = cmd.toString
  lazy val columnNumber = cmd.getJavaSourceStartColumnNumber
  override def toString: String = "line: " + cmd.getJavaSourceStartLineNumber + " " + cmdString
  def returnTypeIfReturn :Option[String] = cmd match{
    case cmd :JReturnVoidStmt => Some("void")
    case _ =>
      ???
  }

  override def hashCode(): Int =
    Objects.hash(cmd.getJavaSourceStartLineNumber, method.getName, method.getDeclaringClass.getName, cmd.getClass)

  def opEquiv(l1:EquivTo, l2:EquivTo): Boolean = {
    if(l1 eq l2)
      true
    else
      l1.equivTo(l2)
  }

  def isCmdEq(other:JimpleLineLoc):Boolean = {
    if (other.cmd.equals(cmd)){
      true
    } else if (other.cmd.getClass != cmd.getClass) {
      false
    }else if(cmd.isInstanceOf[JAssignStmt] && other.cmd.isInstanceOf[JAssignStmt]) {
      val a1 = cmd.asInstanceOf[JAssignStmt]
      val a2 = other.cmd.asInstanceOf[JAssignStmt]
      lazy val lhsEq = opEquiv(a1.getLeftOp,a2.getLeftOp)
      lazy val rhsEq = opEquiv(a1.getRightOp,a2.getRightOp)
      val res = lhsEq && rhsEq
      res
    }else if(cmd.isInstanceOf[JInvokeStmt] && other.cmd.isInstanceOf[JInvokeStmt]){

      val a1 = cmd.asInstanceOf[JInvokeStmt]
      val a2 = other.cmd.asInstanceOf[JInvokeStmt]
      val res = a1.getInvokeExpr.equivTo(a2.getInvokeExpr)
      res
    } else {
      other.cmdString == cmdString
    }
  }

  /**
   * Note: soot.Unit does not have reasonable implementation of .equals
   */
  override def equals(obj: Any): Boolean = obj match{
    case other: JimpleLineLoc =>
      if(this eq other)
        return true
      lazy val lineEq = other.cmd.getJavaSourceStartLineNumber == cmd.getJavaSourceStartLineNumber
      lazy val columnEq = other.columnNumber == columnNumber
      lazy val methodEq = method == other.method
      lazy val cmdEq:Boolean = other match {
        case other:JimpleLineLoc => isCmdEq(other)
        case other => other.cmdString == cmdString
      }
      val res = lineEq && columnEq && methodEq && cmdEq
      res
    case _ =>
      false
  }

  override def lineNumber: Int = cmd.getJavaSourceStartLineNumber

  override def containingMethod: MethodLoc = JimpleMethodLoc(method)

  override def isFirstLocInMethod: Boolean = {
    val unitBoxes = method.retrieveActiveBody().getUnits
    if(unitBoxes.size > 0){
      cmd.equals(unitBoxes.getFirst)
    }else {false}
  }
}

