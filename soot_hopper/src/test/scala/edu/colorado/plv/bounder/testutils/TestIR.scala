package edu.colorado.plv.bounder.testutils

import edu.colorado.plv.bounder.ir.{AppLoc, CmdWrapper, IRWrapper, InvokeCmd, LineLoc, Loc, MethodLoc, UnresolvedMethodTarget}

class TestIR(transitions: Set[TestTransition]) extends IRWrapper[String,String] {
  override def findMethodLoc(className: String, methodName: String): Option[MethodLoc] = ???

  override def findLineInMethod(className: String, methodName: String, line: Int): Iterable[AppLoc] = ???

  override def makeCmd(cmd: String, method: String, loc: Option[AppLoc]): CmdWrapper = ???

  override def commandPredicessors(cmdWrapper: CmdWrapper): List[AppLoc] = ???

  override def commandNext(cmdWrapper: CmdWrapper): List[AppLoc] = ???

  override def isMethodEntry(cmdWrapper: CmdWrapper): Boolean = ???

  override def cmdAfterLocation(loc: AppLoc): CmdWrapper = ???

  override def cmdBeforeLocation(loc: AppLoc): CmdWrapper = transitions.find(t => t match{
    case CmdTransition(_,_,l2) if (l2 == loc) => true
    case _ => false
  }).map(_.asInstanceOf[CmdTransition].cmd).get

  override def makeInvokeTargets(invoke: AppLoc): Set[UnresolvedMethodTarget] = ???

  override def getAllMethods: Seq[MethodLoc] = ???

  override def getOverrideChain(method: MethodLoc): Seq[MethodLoc] = ???

  override def callSites(method: String): Seq[String] = ???

  override def makeMethodRetuns(method: MethodLoc): List[Loc] = ???

  override def getClassHierarchy: Map[String, Set[String]] = ???
}
case class TestIRMethodLoc(clazz:String, name:String) extends MethodLoc {
  override def simpleName: String = name

  override def classType: String = clazz

  override def argTypes: List[String] = ???
}
case class TestIRLineLoc(line:Int) extends LineLoc {

}

sealed trait TestTransition
case class CmdTransition(loc1: Loc, cmd:CmdWrapper , loc2:Loc) extends TestTransition
case class MethodTransition(loc1:Loc, loc2:Loc) extends TestTransition

case class TestMethod(methodLoc: TestIRMethodLoc, cmds: List[CmdWrapper])
