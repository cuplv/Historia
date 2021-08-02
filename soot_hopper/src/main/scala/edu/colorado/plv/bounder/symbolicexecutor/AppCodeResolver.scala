package edu.colorado.plv.bounder.symbolicexecutor

import java.util.NoSuchElementException

import better.files.{File, Resource}
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodReturn, CmdWrapper, FieldReference, IRWrapper, InternalMethodReturn, Invoke, InvokeCmd, JimpleFlowdroidWrapper, JimpleMethodLoc, LineLoc, Loc, MethodLoc, SpecialInvoke, StaticInvoke, UnresolvedMethodTarget, VirtualInvoke}

import scala.annotation.tailrec
import scala.io.Source
import scala.util.matching.Regex
import scala.util.Random

trait AppCodeResolver {
  def isFrameworkClass(packageName:String):Boolean
  def isAppClass(fullClassName:String):Boolean
  def resolveCallLocation(tgt : UnresolvedMethodTarget): Set[Loc]
  def resolveCallbackExit(method : MethodLoc, retCmdLoc: Option[LineLoc]):Option[Loc]
  def resolveCallbackEntry(method: MethodLoc):Option[Loc]
  def getCallbacks: Set[MethodLoc]
}
object FrameworkExtensions{
  private val urlPos = List("FrameworkExtensions.txt",
    "/Resources/FrameworkExtensions.txt",
    "Resources/FrameworkExtensions.txt")
  private val frameworkExtPaths: Seq[String] = urlPos.flatMap{ p =>
    try {
      Some(Resource.getUrl(p).getPath)
    }catch {
      case _:Throwable=>
        None
    }
  }
  val extensionStrings: List[String] = JimpleFlowdroidWrapper.cgEntryPointName::
    urlPos.flatMap{ (frameworkExtPath:String) =>
//    val source = Source.fromFile(frameworkExtPath)
    try {
      val source = Resource.getAsString(frameworkExtPath)
      Some(source.split("\n").toList)
    }catch{
      case _:Throwable => None
    }
  }.head

  val extensionRegex: Regex = extensionStrings.mkString("|").r
}

class DefaultAppCodeResolver[M,C] (ir: IRWrapper[M,C]) extends AppCodeResolver {

  protected val excludedClasses = "dummyMainClass".r

  var appMethods = ir.getAllMethods.filter(m => !isFrameworkClass(m.classType)).toSet
  private def iGetCallbacks():Set[MethodLoc] = appMethods.filter(resolveCallbackEntry(_).isDefined)
  private var callbacks:Set[MethodLoc] = iGetCallbacks()
  override def getCallbacks:Set[MethodLoc] = callbacks
  def invalidateCallbacks() = {
    appMethods = ir.getAllMethods.filter(m => !isFrameworkClass(m.classType)).toSet
    callbacks = iGetCallbacks()
  }

  @tailrec
  final def sampleDeref():AppLoc = {
    def keepI(i:Invoke):Boolean = i match {
      case VirtualInvoke(_, _, targetMethod, _) => !targetMethod.contains("<init>")
      case SpecialInvoke(_, _, targetMethod, _) => !targetMethod.contains("<init>")
      case StaticInvoke(_, targetMethod, _) =>  !targetMethod.contains("<init>")
    }
    val randomMethodList = Random.shuffle(appMethods.toList)
    val m = randomMethodList.head

    // generate set of dereferences for method

    val returns = ir.makeMethodRetuns(m).toSet.map((v: AppLoc) => BounderUtil.cmdAtLocationNopIfUnknown(v,ir).mkPre)
    val derefs = BounderUtil.graphFixpoint[CmdWrapper, Set[AppLoc]](start = returns,Set(),Set(),
      next = n => ir.commandPredecessors(n).map((v: AppLoc) =>
        BounderUtil.cmdAtLocationNopIfUnknown(v,ir).mkPre).toSet,
      comp = {
        case (acc,v) =>
          val newLocs:Set[AppLoc] = ir.commandPredecessors(v).flatMap{v => ir.cmdAtLocation(v) match{
            case AssignCmd(_, i:SpecialInvoke, _) if keepI(i) => Some(v)
            case AssignCmd(_, i:VirtualInvoke, _) if keepI(i) => Some(v)
            case AssignCmd(_, i:FieldReference, _) => Some(v)
            case InvokeCmd(i:SpecialInvoke, _) if keepI(i) => Some(v)
            case InvokeCmd(i:VirtualInvoke,_) if keepI(i) => Some(v)
            case _ => None
          }}.toSet
          acc ++ newLocs
      },
      join = (a,b) => a.union(b)
    ).flatMap{ case (_,v) => v}.toSet.toList
    if(derefs.isEmpty){
      sampleDeref()
    }else {
      val shuf = Random.shuffle(derefs)
      val s = shuf.head
      if(s.line.lineNumber > 0)
        s
      else
        sampleDeref()
    }
  }

  def isFrameworkClass(fullClassName:String):Boolean = fullClassName match{
    case FrameworkExtensions.extensionRegex() =>
      true
    case _ =>
      false
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

  private val CLINIT = "void <clinit>()"
  override def resolveCallbackExit(method: MethodLoc, retCmdLoc: Option[LineLoc]): Option[Loc] = {
    if(method.simpleName == CLINIT){
      return Some(CallbackMethodReturn("java.lang.Object", CLINIT,method, retCmdLoc))
    }
    val overrides = ir.getOverrideChain(method)
    if(overrides.size == 1 && overrides.last.classType == "java.lang.Object" && overrides.last.simpleName == "<init>"){
      // Object init is not considered a callback
      return None
    }
    if (overrides.size > 0) {
      val leastPrecise: MethodLoc = overrides.last
//      Some(CallbackMethodReturn(leastPrecise.classType, leastPrecise.simpleName, method, retCmdLoc))
      //TODO: swapped out callback to contain target type instead of overridden type check that this works
      Some(CallbackMethodReturn(method.classType, leastPrecise.simpleName, method, retCmdLoc))
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
//      Some(CallbackMethodInvoke(leastPrecise.classType, leastPrecise.simpleName, method))
      Some(CallbackMethodInvoke(method.classType, leastPrecise.simpleName, method))
    } else None
  }
}