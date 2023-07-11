package edu.colorado.plv.bounder.ir

import better.files.File
import edu.colorado.plv.bounder.lifestate.LifeState.Signature
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.AppCodeResolver
import upickle.default.{macroRW, ReadWriter => RW}

import scala.collection.{BitSet, immutable}

//TODO: serialize IR and points to, This should be able to continue where other left off
//TODO: datatype for SerializedIR method

/**
 *
 * @param transitions map from post location to previous transitions
 */
case class SerializedIR(transitions: Map[AppLoc, Set[SerializedTransition]]) extends IRWrapper[String,CmdWrapper] {
  private val locToCmd: Map[Loc, CmdWrapper] = transitions.flatMap{
    case  (post, targets) => targets.flatMap{
      case CmdTransition(loc1, cmd) =>
        Set((loc1,cmd),(post,cmd))
      case _:NopTransition => Set.empty
    }
  }
  override def findMethodLoc(sig:Signature): Iterable[MethodLoc] = ???

  override def findLineInMethod(sig:Signature, line: Int): Iterable[AppLoc] = ???

  // TODO(Duke) implement this method
  override def commandPredecessors(cmdWrapper: CmdWrapper): List[AppLoc] = ???

  override def commandNext(cmdWrapper: CmdWrapper): List[AppLoc] = ???

  override def isMethodEntry(cmdWrapper: CmdWrapper): Boolean = ???

  override def cmdAtLocation(loc: AppLoc): CmdWrapper = {
    if(!locToCmd.contains(loc))
      throw new IllegalStateException(s"graph does not have location ${loc}")
    locToCmd(loc)
  }

  override def makeInvokeTargets(invoke: AppLoc): UnresolvedMethodTarget = ???

  // TODO: serialized methods
  override def getAllMethods: Seq[MethodLoc] = Seq()

  override def getOverrideChain(method: MethodLoc): Seq[MethodLoc] = ???

  override def appCallSites(method: MethodLoc, resolver: AppCodeResolver): Seq[AppLoc] = ???

  override def makeMethodRetuns(method: MethodLoc): List[AppLoc] = ???

  override def makeMethodTargets(source: MethodLoc): Set[MethodLoc] = ???

  override def isSuperClass(type1: String, type2: String): Boolean = ???

  override def degreeOut(cmd: AppLoc): Int = ???

  override def degreeIn(cmd: AppLoc): Int = ???

  override def getInterfaces: Set[String] = ???

  override def isLoopHead(cmd: AppLoc): Boolean = ???

  override def commandTopologicalOrder(cmdWrapper: CmdWrapper): Int = ???

  override def pointsToSet(loc: MethodLoc, local: LocalWrapper): TypeSet = TopTypeSet

  override def getThisVar(methodLoc: Loc): Option[LocalWrapper] = None

  override def getThisVar(methodLoc: MethodLoc): Option[LocalWrapper] = ???

  override def getClassHierarchyConstraints: ClassHierarchyConstraints = ???

  override def findInMethod(className: String, methodName: String, toFind: CmdWrapper => Boolean): Iterable[AppLoc] = ???

  override def dumpDebug(classFilter: String): String = ???

  override def allMethodLocations(m: MethodLoc): Set[AppLoc] = ???
}

/**
 *
 * @param clazz
 * @param name
 * @param args use "_" for receiver on static method
 */
case class SerializedIRMethodLoc(clazz:String, name:String, args:List[Option[LocalWrapper]]) extends MethodLoc {
  override def simpleName: String = name

  override def classType: String = clazz

  override def argTypes: List[String] = args.map(_.map(_.localType).getOrElse("void"))

  /**
   * None for return if void
   * None for reciever if static
   *
   * @return list of args, [return,reciever, arg1,arg2 ...]
   */
  override def getArgs: List[Option[LocalWrapper]] = args.map{
    case Some(LocalWrapper("_", _)) => None
    case Some(local@LocalWrapper(_, _)) => Some(local)
    case None => None
  }

  override def isStatic: Boolean = ???

  override def isInterface: Boolean = ???

  override def bodyToString: String = ???

  override def isNative(): Boolean = ???
}

object SerializedIRMethodLoc{
  implicit val rw = upickle.default.readwriter[ujson.Value].bimap[MethodLoc](
    x =>
      ujson.Arr(x.simpleName, x.classType, x.argTypes),
    json =>
      SerializedIRMethodLoc(json(0).str, json(1).str, ???)
  )
}


/**
 *
 * @param line syntactic line in source
 * @param column unique identifier
 */
case class SerializedIRLineLoc(line:Int, desc:String = "", column:Int = 0) extends LineLoc {

  override def lineNumber: Int = line

  override def containingMethod: MethodLoc = ???

  override def isFirstLocInMethod: Boolean = ???
}
object SerializedIRLineLoc{
  implicit val rw:RW[SerializedIRMethodLoc] = macroRW
}

sealed trait SerializedTransition{
  /**
   *
   * @return pre-location of current transition
   */
  def loc1:Loc
}
case class CmdTransition(loc1: Loc, cmd:CmdWrapper) extends SerializedTransition{
  val loc2:Loc = cmd.getLoc
}
case class NopTransition(loc1:Loc) extends SerializedTransition
//TODO: handle method and callback transitions

