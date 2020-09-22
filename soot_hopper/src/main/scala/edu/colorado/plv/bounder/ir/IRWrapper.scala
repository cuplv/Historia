package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.symbolicexecutor.state.TypeConstraint

// Interface to handle all the messy parts of interacting with the underlying IR representation
/**
 * A class that translates from the underlying representation to a "cleaned" Ir
 * @tparam M Native method type for the underlying representation
 * @tparam C Command type for the underlying representation
 */
trait IRWrapper[M,C]{
  def getAllMethods : Iterable[MethodLoc]
  def getOverrideChain( method : MethodLoc) : Seq[MethodLoc]
  def findMethodLoc(className: String, methodName: String):Option[MethodLoc]
  def findLineInMethod(className:String, methodName:String, line:Int):Iterable[AppLoc]
  def makeCmd(cmd:C, method:M, loc:Option[AppLoc] = None): CmdWrapper[M,C]
  def commandPredicessors(cmdWrapper:CmdWrapper[M,C]): List[AppLoc]
  def commandNext(cmdWrapper:CmdWrapper[M,C]):List[AppLoc]

  /**
   * Is this the first command in containing method
   */
  def isMethodEntry(cmdWrapper: CmdWrapper[M,C]): Boolean
  def cmdAfterLocation(loc: AppLoc): CmdWrapper[M,C]
  def cmdBeforeLocation(loc:AppLoc): CmdWrapper[M,C]
  def makeInvokeTargets(invoke:InvokeCmd[M,C]):Set[UnresolvedMethodTarget]
  def callSites(method : M): Seq[C]
  def canAlias(type1:String, type2:String):Boolean
  def makeMethodRetuns(method: MethodLoc) : List[Loc]
}
sealed case class UnresolvedMethodTarget(clazz: String, methodName:String, loc:Option[MethodLoc])


sealed abstract class CmdWrapper[M,C](loc:AppLoc, wrapper: IRWrapper[M,C]){
  def getLoc: AppLoc = loc
}
case class ReturnVal[M,C](returnVar: LocalWrapper, loc:AppLoc, wrapper: IRWrapper[M,C]) extends CmdWrapper(loc,wrapper)
case class AssignCmd[M,C](target: LVal, source: RVal, loc:AppLoc, wrapper: IRWrapper[M,C]) extends CmdWrapper(loc,wrapper){
  override def toString:String = s"$target := $source"
}
case class InvokeCmd[M,C](method: Invoke[M,C], loc:AppLoc, wrapper:IRWrapper[M,C]) extends CmdWrapper(loc,wrapper)


abstract class MethodWrapper[M,C](decalringClass : String,
                                  returnType: String,
                                  simpleName:String,
                                  params:List[String], wrapper:IRWrapper[M,C])

// Things that can be used as expressions
trait RVal
// New only has type, constructor parameters go to the <init> method
case class NewCommand(className: String) extends RVal

sealed trait Invoke[M,C] extends RVal {
  def targetClass:String
  def targetMethod:String
  def params:List[LocalWrapper]
  def wrapper:IRWrapper[M,C]
  def targetOptional: Option[LocalWrapper]
  def receiverType:String =
    ???
  def paramTypes:List[String] =
    ???
}
/*VirtualInvoke is used when dynamic dispatch can change target*/
case class VirtualInvoke[M,C](target:LocalWrapper,
                         targetClass:String,
                         targetMethod:String,
                         params:List[LocalWrapper], wrapper: IRWrapper[M,C]) extends Invoke[M,C] {
  override def targetOptional: Option[LocalWrapper] = Some(target)
}
/*SpecialInvoke is used when the exact class target is known*/
case class SpecialInvoke[M,C](target:LocalWrapper,
                         targetClass:String,
                         targetMethod:String,
                         params:List[LocalWrapper], wrapper:IRWrapper[M,C]) extends Invoke[M,C] {
  override def targetOptional: Option[LocalWrapper] = Some(target)
}
case class StaticInvoke[M,C](targetClass:String,
                        targetMethod:String,
                        params:List[LocalWrapper], wrapper:IRWrapper[M,C])extends Invoke[M,C] {
  override def targetOptional: Option[LocalWrapper] = None
}

// Things that can be assigned to or used as expressins
trait LVal extends RVal
case class LocalWrapper(name:String, localType:String) extends LVal {
  override def toString:String = name
}
case class ParamWrapper(name:String) extends LVal
//case class FieldWrapper(name:String) extends LVal
case class ThisWrapper(className:String) extends LVal
case class FieldRef(base:LocalWrapper, containsType:String, declType:String, name:String) extends LVal{
  override def toString: String = s"${base}.${name}"
}