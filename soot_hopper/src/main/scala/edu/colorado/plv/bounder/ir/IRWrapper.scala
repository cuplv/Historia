package edu.colorado.plv.bounder.ir

// Interface to handle all the messy parts of interacting with the underlying IR representation
/**
 * A class that translates from the underlying representation to a "cleaned" Ir
 * @tparam M Native method type for the underlying representation
 * @tparam C Command type for the underlying representation
 */
trait IRWrapper[M,C]{
  def findMethodLoc(className: String, methodName: String):Option[MethodLoc]
  def findLineInMethod(className:String, methodName:String, line:Int):Iterable[Loc]
  def makeCmd(cmd:C, method:M, loc:Option[Loc] = None): CmdWrapper[M,C]
  def preds(cmdWrapper:CmdWrapper[M,C]): Set[CmdWrapper[M,C]]
  def isMethodEntry(cmdWrapper: CmdWrapper[M,C]): Boolean
  def makeMethod(method: M) : MethodWrapper[M,C]
  def makeLoc(cmd: C, method: M): Loc
  def makeCmd(loc: Loc): CmdWrapper[M,C]
}


abstract class CmdWrapper[M,C](loc:Loc, wrapper: IRWrapper[M,C]){
  def getLoc: Loc = loc
  def getWrapper = wrapper
}
case class ReturnVal[M,C](returnVar: LocalWrapper,loc:Loc, wrapper: IRWrapper[M,C]) extends CmdWrapper(loc,wrapper)
case class AssignCmd[M,C](target: LVal, source: RVal, loc:Loc, wrapper: IRWrapper[M,C]) extends CmdWrapper(loc,wrapper)
case class InvokeCmd[M,C](method: Invoke, loc:Loc, wrapper:IRWrapper[M,C]) extends CmdWrapper(loc,wrapper)


abstract class MethodWrapper[M,C](methodType: MethodType,
                                  decalringClass : String,
                                  returnType: String,
                                  simpleName:String,
                                  params:List[String], wrapper:IRWrapper[M,C])

trait MethodType
case object CallinMethod // Framework method invoked by application
case class CallbackMethod(firstFrameworkOverride: String) // Can be invoked by application or framework
case object InternalMethod // Can only be invoked by application


// Things that can be used as expressions
trait RVal
case class NewCommand(className: String, params: List[RVal]) extends RVal
trait Invoke extends RVal
/*VirtualInvoke is used when dynamic dispatch can change target*/
case class VirtualInvoke(target:LocalWrapper,
                         targetClass:String,
                         targetMethod:String,
                         params:List[LocalWrapper]) extends Invoke
/*SpecialInvoke is used when the exact class target is known*/
case class SpecialInvoke(target:LocalWrapper,
                         targetClass:String,
                         targetMethod:String,
                         params:List[LocalWrapper]) extends Invoke
case class StaticInvoke(targetClass:String,
                        targetMethod:String,
                        params:List[LocalWrapper])extends RVal

// Things that can be assigned to or used as expressins
trait LVal extends RVal
case class LocalWrapper(name:String) extends LVal
case class ParamWrapper(name:String) extends LVal
case class FieldWrapper(name:String) extends LVal