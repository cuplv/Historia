package edu.colorado.plv.bounder.testutils

import edu.colorado.plv.bounder.ir.{AppLoc, CmdWrapper, IRWrapper, InvokeCmd, Loc, MethodLoc, UnresolvedMethodTarget}

class TestIR(program: TestProgram) extends IRWrapper[String,String] {
  override def findMethodLoc(className: String, methodName: String): Option[MethodLoc] = ???

  override def findLineInMethod(className: String, methodName: String, line: Int): Iterable[AppLoc] = ???

  override def makeCmd(cmd: String, method: String, loc: Option[AppLoc]): CmdWrapper[String, String] = ???

  override def commandPredicessors(cmdWrapper: CmdWrapper[String, String]): List[AppLoc] = ???

  override def commandNext(cmdWrapper: CmdWrapper[String, String]): List[AppLoc] = ???

  override def isMethodEntry(cmdWrapper: CmdWrapper[String, String]): Boolean = ???

  override def cmdAfterLocation(loc: AppLoc): CmdWrapper[String, String] = ???

  override def cmdBeforeLocation(loc: AppLoc): CmdWrapper[String, String] = ???

  override def makeInvokeTargets(invoke: InvokeCmd[String, String]): Set[UnresolvedMethodTarget] = ???

  override def canAlias(type1: String, type2: String): Boolean = ???

  override def getAllMethods: Seq[MethodLoc] = ???

  override def getOverrideChain(method: MethodLoc): Seq[MethodLoc] = ???

  override def callSites(method: String): Seq[String] = ???
}
case class TestIRMethodLoc(name:String) extends MethodLoc {
  override def simpleName: String = ???

  override def classType: String = ???

  override def argTypes: List[String] = ???
}
case class TestIRLineLoc(line:Int) extends MethodLoc {
  override def simpleName: String = ???

  override def classType: String = ???

  override def argTypes: List[String] = ???
}

case class TestProgram(methods:List[TestMethod])
case class TestMethod(methodLoc: TestIRMethodLoc, cmds: List[CmdWrapper[String,String]])
