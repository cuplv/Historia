package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.symbolicexecutor.AppCodeResolver
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
  def makeCmd(cmd:C, method:M, loc:Option[AppLoc] = None): CmdWrapper
  def commandPredecessors(cmdWrapper:CmdWrapper): List[AppLoc]
  def commandNext(cmdWrapper:CmdWrapper):List[AppLoc]

  /**
   * Is this the first command in containing method
   */
  def isMethodEntry(cmdWrapper: CmdWrapper): Boolean
  def cmdAtLocation(loc:AppLoc) :CmdWrapper
  def makeInvokeTargets(invoke:AppLoc, upperTypeBound: Option[String]):UnresolvedMethodTarget
  def appCallSites(method : MethodLoc, resolver:AppCodeResolver): Seq[AppLoc]
  def makeMethodRetuns(method: MethodLoc) : List[AppLoc]
  def getClassHierarchy : Map[String, Set[String]]
  def canAlias(type1:String, type2:String):Boolean
  def getDirectMethodCalls(method: MethodLoc):Set[MethodLoc]
  def getDirectHeapOps(method:MethodLoc):Set[CmdWrapper]
}
sealed case class UnresolvedMethodTarget(clazz: String, methodName:String, loc:Set[MethodLoc])


/**
 *
 * @param loc location in app after command //TODO: it seems there should be a cleaner way to implement this
 */
sealed abstract class CmdWrapper(loc:AppLoc){
  def getLoc: AppLoc = loc
  def mkPre: CmdWrapper
}

/**
 *
 * @param returnVar None if void return otherwise local returned by cmd
 * @param loc
 */
case class ReturnCmd(returnVar: Option[RVal], loc:AppLoc) extends CmdWrapper(loc) {
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
  override def toString: String = s"return ${returnVar.getOrElse("")};"
}
case class AssignCmd(target: LVal, source: RVal, loc:AppLoc) extends CmdWrapper(loc){
  override def toString:String = s"$target := $source;"
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
}
case class InvokeCmd(method: Invoke, loc:AppLoc) extends CmdWrapper(loc) {
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
  override def toString: String = method.toString
}

case class If(b:RVal, loc:AppLoc) extends CmdWrapper(loc){
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
}

case class Eq(v1:RVal, v2:RVal) extends RVal
case class Ne(v1:RVal, v2:RVal) extends RVal
case class Gt(v1:RVal, v2:RVal) extends RVal

case class Cast(castT:String, local: LocalWrapper) extends RVal
case class Binop(v1:RVal, op: BinaryOperator, v2:RVal) extends RVal
sealed trait BinaryOperator
case object Mult extends BinaryOperator
case object Div extends BinaryOperator
case object Add extends BinaryOperator
case object Sub extends BinaryOperator


//abstract class MethodWrapper[M,C](decalringClass : String,
//                                  returnType: String,
//                                  simpleName:String,
//                                  params:List[String], wrapper:IRWrapper[M,C])

// Things that can be used as expressions
trait RVal
// New only has type, constructor parameters go to the <init> method
case class NewCommand(className: String) extends RVal
case object NullConst extends RVal
case class ConstVal(v:Any) extends RVal
case class IntConst(v:Int) extends RVal
case class StringConst(v:String) extends RVal
case class BoolConst(v:Boolean) extends RVal

sealed trait Invoke extends RVal {
  def targetClass:String
  def targetMethod:String
  def params:List[RVal]
  def targetOptional: Option[LocalWrapper]
  def paramTypes:List[String] =
    ???
}
/*VirtualInvoke is used when dynamic dispatch can change target*/
case class VirtualInvoke(target:LocalWrapper,
                         targetClass:String,
                         targetMethod:String,
                         params:List[RVal]) extends Invoke {
  override def targetOptional: Option[LocalWrapper] = Some(target)
}
/*SpecialInvoke is used when the exact class target is known*/
case class SpecialInvoke(target:LocalWrapper,
                         targetClass:String,
                         targetMethod:String,
                         params:List[RVal]) extends Invoke {
  override def targetOptional: Option[LocalWrapper] = Some(target)
}
case class StaticInvoke(targetClass:String,
                        targetMethod:String,
                        params:List[RVal])extends Invoke {
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