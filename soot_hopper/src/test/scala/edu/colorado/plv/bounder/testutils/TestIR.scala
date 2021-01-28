package edu.colorado.plv.bounder.testutils

import edu.colorado.plv.bounder.ir.{AppLoc, CmdWrapper, IRWrapper, InvokeCmd, LineLoc, Loc, LocalWrapper, MethodLoc, UnresolvedMethodTarget}
import edu.colorado.plv.bounder.symbolicexecutor.AppCodeResolver

class TestIR(transitions: Set[TestTransition]) extends IRWrapper[String,String] {
  override def findMethodLoc(className: String, methodName: String): Option[MethodLoc] = ???

  override def findLineInMethod(className: String, methodName: String, line: Int): Iterable[AppLoc] = ???

  override def makeCmd(cmd: String, method: String, loc: Option[AppLoc]): CmdWrapper = ???

  override def commandPredecessors(cmdWrapper: CmdWrapper): List[AppLoc] = ???

  override def commandNext(cmdWrapper: CmdWrapper): List[AppLoc] = ???

  override def isMethodEntry(cmdWrapper: CmdWrapper): Boolean = ???

  override def cmdAtLocation(loc: AppLoc): CmdWrapper = {
    transitions.find( t => t match{
      case CmdTransition(_,_,l2) if (l2 == loc) => true
      case _ => false
      }
    ).map(_.asInstanceOf[CmdTransition].cmd).get
  }

  override def makeInvokeTargets(invoke: AppLoc): UnresolvedMethodTarget = ???

  override def getAllMethods: Seq[MethodLoc] = ???

  override def getOverrideChain(method: MethodLoc): Seq[MethodLoc] = ???

  override def appCallSites(method: MethodLoc, resolver: AppCodeResolver): Seq[AppLoc] = ???

  override def getClassHierarchy: Map[String, Set[String]] = ???

  override def canAlias(type1: String, type2: String): Boolean = true

  override def makeMethodRetuns(method: MethodLoc): List[AppLoc] = ???

  override def makeMethodTargets(source: MethodLoc): Set[MethodLoc] = ???

  override def isSuperClass(type1: String, type2: String): Boolean = ???

  override def degreeOut(cmd: AppLoc): Int = ???
}

/**
 *
 * @param clazz
 * @param name
 * @param args use "_" for receiver on static method
 */
case class TestIRMethodLoc(clazz:String, name:String, args:List[LocalWrapper]) extends MethodLoc {
  override def simpleName: String = name

  override def classType: String = clazz

  override def argTypes: List[String] = args.map(_.localType)

  /**
   * None for return if void
   * None for reciever if static
   *
   * @return list of args, [return,reciever, arg1,arg2 ...]
   */
  override def getArgs: List[Option[LocalWrapper]] = args.map{
    case LocalWrapper("_", _) => None
    case local@LocalWrapper(_, _) => Some(local)
  }

  override def isStatic: Boolean = ???

  override def isInterface: Boolean = ???
}
case class TestIRLineLoc(line:Int) extends LineLoc {

}

sealed trait TestTransition
case class CmdTransition(loc1: Loc, cmd:CmdWrapper , loc2:Loc) extends TestTransition
case class MethodTransition(loc1:Loc, loc2:Loc) extends TestTransition

case class TestMethod(methodLoc: TestIRMethodLoc, cmds: List[CmdWrapper])
