package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.symbolicexecutor.AppCodeResolver
import upickle.default.{ReadWriter => RW, macroRW}

// Interface to handle all the messy parts of interacting with the underlying IR representation
/**
 * A class that translates from the underlying representation to a "cleaned" Ir
 * @tparam M Native method type for the underlying representation
 * @tparam C Command type for the underlying representation
 */
trait IRWrapper[M,C]{
  def getAllMethods : Iterable[MethodLoc]
  def getOverrideChain( method : MethodLoc) : Seq[MethodLoc]
  def findMethodLoc(className: String, methodName: String):Iterable[MethodLoc]
  def findLineInMethod(className:String, methodName:String, line:Int):Iterable[AppLoc]
  def makeMethodTargets(source: MethodLoc): Set[MethodLoc]
  def makeCmd(cmd:C, method:M, loc:Option[AppLoc] = None): CmdWrapper
  def degreeOut(cmd: AppLoc):Int
  def degreeIn(cmd: AppLoc):Int
  def commandPredecessors(cmdWrapper:CmdWrapper): List[AppLoc]
  def commandNext(cmdWrapper:CmdWrapper):List[AppLoc]

  /**
   * Is this the first command in containing method
   */
  def isMethodEntry(cmdWrapper: CmdWrapper): Boolean
  def cmdAtLocation(loc:AppLoc) :CmdWrapper
  def makeInvokeTargets(invoke:AppLoc):UnresolvedMethodTarget
  def appCallSites(method : MethodLoc, resolver:AppCodeResolver): Seq[AppLoc]
  def makeMethodRetuns(method: MethodLoc) : List[AppLoc]
  def getClassHierarchy : Map[String, Set[String]]
  def canAlias(type1:String, type2:String):Boolean
  def isSuperClass(type1:String, type2:String):Boolean
}
// Ignore parts of the IR we haven't implemented while scanning for relevant method calls and heap access
final case class CmdNotImplemented(message:String) extends RuntimeException(message)
sealed case class UnresolvedMethodTarget(clazz: String, methodName:String, loc:Set[MethodLoc])


/**
 *
 * @param loc location in app after command //TODO: it seems there should be a cleaner way to implement this
 */
sealed abstract class CmdWrapper(loc:AppLoc){
  def getLoc: AppLoc = loc
  def mkPre: CmdWrapper
}
object CmdWrapper{
  implicit var rw:RW[CmdWrapper] = RW.merge(ThrowCmd.rw, AssignCmd.rw, ReturnCmd.rw, NopCmd.rw, InvokeCmd.rw,
    SwitchCmd.rw, If.rw)
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
object ReturnCmd{
  implicit var rw:RW[ReturnCmd] = macroRW
}
case class AssignCmd(target: LVal, source: RVal, loc:AppLoc) extends CmdWrapper(loc){
  override def toString:String = s"$target := $source;"
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
}
object AssignCmd{
  implicit var rw:RW[AssignCmd] = macroRW
}
case class InvokeCmd(method: Invoke, loc:AppLoc) extends CmdWrapper(loc) {
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
  override def toString: String = method.toString
}
object InvokeCmd{
  implicit var rw:RW[InvokeCmd] = macroRW
}

case class If(b:RVal, trueLoc:AppLoc, loc:AppLoc) extends CmdWrapper(loc){
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
}
object If{
  implicit var rw:RW[If] = macroRW
}

case class NopCmd(loc:AppLoc) extends CmdWrapper(loc){
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
}
object NopCmd{
  implicit var rw:RW[NopCmd] = macroRW
}

case class SwitchCmd(key: LocalWrapper, targets : List[CmdWrapper], loc:AppLoc)extends CmdWrapper(loc) {
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
}
object SwitchCmd{
  implicit var rw:RW[SwitchCmd] = macroRW
}

case class ThrowCmd(loc:AppLoc) extends CmdWrapper(loc){
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
}
object ThrowCmd{
  implicit var rw:RW[ThrowCmd] = macroRW
}

case class Cast(castT:String, local: RVal) extends RVal {
  override def isConst: Boolean = false
}
object Cast{
  implicit var rw:RW[Cast] = macroRW
}
case class Binop(v1:RVal, op: BinaryOperator, v2:RVal) extends RVal {
  override def isConst: Boolean = false
}
object Binop{
  implicit var rw:RW[Binop] = macroRW
}
sealed trait BinaryOperator
object BinaryOperator{
  implicit val rw:RW[BinaryOperator] = RW.merge(
    macroRW[Mult.type], macroRW[Div.type], macroRW[Add.type], macroRW[Sub.type], macroRW[Lt.type],
    macroRW[Le.type], macroRW[Eq.type], macroRW[Ne.type], macroRW[Ge.type]
  )
}
case object Mult extends BinaryOperator
case object Div extends BinaryOperator
case object Add extends BinaryOperator
case object Sub extends BinaryOperator
case object Lt extends BinaryOperator
case object Le extends BinaryOperator
case object Eq extends BinaryOperator
case object Ne extends BinaryOperator
case object Ge extends BinaryOperator

// Things that can be used as expressions
trait RVal{
  def isConst:Boolean
}
object RVal{
  implicit val rw:RW[RVal] = RW.merge(
    macroRW[ConstVal],LVal.rw, macroRW[BoolConst], Invoke.rw, macroRW[InstanceOf], macroRW[CaughtException],
    macroRW[StringConst],macroRW[IntConst],macroRW[NewCommand],macroRW[ClassConst], macroRW[ArrayLength],
    macroRW[Cast],macroRW[Binop],macroRW[NullConst.type],macroRW[TopExpr]
  )
}

/**
 * Currently unsupported rval treated as doing anything.
 * To add support for command, create an ast node and add it to the IRWrappers
 * @param str
 */
case class TopExpr(str:String) extends RVal {
  override def isConst: Boolean = false
}
// New only has type, constructor parameters go to the <init> method
case class NewCommand(className: String) extends RVal {
  override def isConst: Boolean = false
}
case object NullConst extends RVal {
  override def isConst: Boolean = true
}
case class ConstVal(v:String) extends RVal {
  override def isConst: Boolean = true
}
case class IntConst(v:Int) extends RVal {
  override def isConst: Boolean = true
}
case class StringConst(v:String) extends RVal {
  override def isConst: Boolean = true
}
case class BoolConst(v:Boolean) extends RVal {
  override def isConst: Boolean = true
}
case class InstanceOf(clazz:String, target: LocalWrapper) extends RVal {
  override def isConst: Boolean = false
}
case class ClassConst(clazz:String) extends RVal {
  override def isConst: Boolean = true
}
case class CaughtException(n:String) extends RVal {
  override def isConst: Boolean = false
}

case class ArrayLength(l:LocalWrapper) extends RVal {
  override def isConst: Boolean = false
}

sealed trait Invoke extends RVal {
  def targetClass:String
  def targetMethod:String
  def params:List[RVal]
  def targetOptional: Option[LocalWrapper]
  def paramTypes:List[String] =
    ???
}
object Invoke{
  implicit val rw:RW[Invoke] = RW.merge(macroRW[VirtualInvoke], macroRW[SpecialInvoke], macroRW[StaticInvoke])
}
/*VirtualInvoke is used when dynamic dispatch can change target*/
case class VirtualInvoke(target:LocalWrapper,
                         targetClass:String,
                         targetMethod:String,
                         params:List[RVal]) extends Invoke {
  override def targetOptional: Option[LocalWrapper] = Some(target)

  override def isConst: Boolean = false
}
/*SpecialInvoke is used when the exact class target is known*/
case class SpecialInvoke(target:LocalWrapper,
                         targetClass:String,
                         targetMethod:String,
                         params:List[RVal]) extends Invoke {
  override def targetOptional: Option[LocalWrapper] = Some(target)

  override def isConst: Boolean = false
}
case class StaticInvoke(targetClass:String,
                        targetMethod:String,
                        params:List[RVal])extends Invoke {
  override def targetOptional: Option[LocalWrapper] = None

  override def isConst: Boolean = false
}

// Things that can be assigned to or used as expressins
trait LVal extends RVal
object LVal{
  implicit val rw:RW[LVal] = RW.merge(
    FieldReference.rw,ParamWrapper.rw,StaticFieldReference.rw, ArrayReference.rw, LocalWrapper.rw, ThisWrapper.rw)
}

case class ArrayReference(base:RVal, index:RVal) extends LVal {
  override def isConst: Boolean = false
}
object ArrayReference{
  implicit val rw:RW[ArrayReference] = macroRW
}

case class LocalWrapper(name:String, localType:String) extends LVal {
  override def toString:String = name

  override def isConst: Boolean = false
}
object LocalWrapper{
  implicit val rw:RW[LocalWrapper] = macroRW
}

case class ParamWrapper(name:String) extends LVal {
  override def isConst: Boolean = false
}
object ParamWrapper{
  implicit val rw:RW[ParamWrapper] = macroRW
}

//case class FieldWrapper(name:String) extends LVal
case class ThisWrapper(className:String) extends LVal {
  override def isConst: Boolean = false
}

object ThisWrapper{
  implicit val rw:RW[ThisWrapper] = macroRW
}

case class FieldReference(base:LocalWrapper, containsType:String, declType:String, name:String) extends LVal{
  override def toString: String = s"${base}.${name}"

  override def isConst: Boolean = false
}
object FieldReference{
  implicit val rw:RW[FieldReference] = macroRW
}

case class StaticFieldReference(declaringClass: String,
                                fieldName: String, containedType:String) extends LVal {
  override def isConst: Boolean = false
}
object StaticFieldReference{
  implicit val rw:RW[StaticFieldReference] = macroRW
}