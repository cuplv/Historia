package edu.colorado.plv.bounder.ir

import better.files.File
import edu.colorado.plv.bounder.lifestate.LifeState.Signature
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.AppCodeResolver
import upickle.default.{macroRW, ReadWriter => RW}

import scala.collection.BitSet

// Interface to handle all the messy parts of interacting with the underlying IR representation
/**
 * A class that translates from the underlying representation to a "cleaned" Ir
 * @tparam M Native method type for the underlying representation
 * @tparam C Command type for the underlying representation
 */
trait IRWrapper[M,C]{
  def allMethodLocations(m: MethodLoc): Set[AppLoc]

  def dumpDebug(classFilter:String):String
  def getThisVar(methodLoc: Loc): Option[LocalWrapper]
  def getThisVar(methodLoc: MethodLoc): Option[LocalWrapper]

  def getInterfaces: Set[String]

  def getAllMethods : Iterable[MethodLoc]
  def getOverrideChain( method : MethodLoc) : Seq[MethodLoc]
  def findMethodLoc(sig:Signature):Iterable[MethodLoc]
  def findLineInMethod(sig:Signature, line:Int):Iterable[AppLoc]
  def findInMethod(className:String, methodName:String, toFind: CmdWrapper => Boolean):Iterable[AppLoc]

  /**
   * @param source a method in the application
   * @return set of methods that source may call at runtime
   */
  def makeMethodTargets(source: MethodLoc): Set[MethodLoc]
  def degreeOut(cmd: AppLoc):Int
  def degreeIn(cmd: AppLoc):Int
  def isLoopHead(cmd:AppLoc):Boolean

  // points to analysis
  def pointsToSet(loc:MethodLoc, local: LocalWrapper):TypeSet

  def commandTopologicalOrder(cmdWrapper:CmdWrapper):Int
  def commandPredecessors(cmdWrapper:CmdWrapper): List[AppLoc]
  def commandNext(cmdWrapper:CmdWrapper):List[AppLoc]

//  /**
//   * Is this the first command in containing method
//   */
  def isMethodEntry(cmdWrapper: CmdWrapper): Boolean
  def cmdAtLocation(loc:AppLoc) :CmdWrapper
  def makeInvokeTargets(invoke:AppLoc):UnresolvedMethodTarget
  def appCallSites(method : MethodLoc, resolver:AppCodeResolver): Seq[AppLoc]
  def makeMethodRetuns(method: MethodLoc) : List[AppLoc]

  def getClassHierarchyConstraints:ClassHierarchyConstraints
  @deprecated
  def canAlias(type1:String, type2:String):Boolean
  def isSuperClass(type1:String, type2:String):Boolean
//  def fwkPossibleCallbackMsgCount:Int
//  def fwkPossibleCallinMsgCount:Int
  def appCallbackMsgCount:Int
//  def appCallinMsgCount:Int
//  def specFwk
}
// Ignore parts of the IR we haven't implemented while scanning for relevant method calls and heap access
final case class CmdNotImplemented(message:String) extends RuntimeException(message)
sealed case class UnresolvedMethodTarget(clazz: String, methodName:String, loc:Set[MethodLoc])


sealed abstract class TypeSet{
  def union(other:TypeSet):TypeSet
  def intersect(other:TypeSet):TypeSet
  def intersectNonEmpty(other:TypeSet):Boolean
  def isEmpty:Boolean

  /**
   * Get set of integers representing types that can inhabit this type set
   * @return None if top type set Some otherwise
   */
  def getValues:Option[Set[Int]]
  def contains(i:Int):Boolean
  def contains(other:TypeSet):Boolean
  /**
   * Create new type set where type must be a subtype of one of the values in 'types'
   * TODO: this is a slow operation, test if we actually need it
   * @param types set of types where this value must be a subtype of at least one
   * @param ch ClassHierarchyConstraints used to resolve subtypes
   * @return new constrained subtype
   */
  def filterSubTypeOf(types:Set[String])(implicit ch:ClassHierarchyConstraints):TypeSet
}

object TypeSet{
//  implicit var rw:RW[TypeSet] = RW.merge(macroRW[TopTypeSet.type], BitTypeSet.rw,
//    macroRW[EmptyTypeSet.type], PrimTypeSet.rw) //===================
  val Prim = "PrimTypeSet:(.*)".r
  val Bit = "BitTypeSet:(.*)".r
  implicit var rw:RW[TypeSet] = upickle.default.readwriter[String].bimap[TypeSet](
    ts => ts match {
      case TopTypeSet => "TopTypeSet"
      case EmptyTypeSet => "EmptyTypeSet"
      case PrimTypeSet(name) => s"PrimTypeSet:${name}"
      case BitTypeSet(s) if s.isEmpty => "EmptyTypeSet"
      case BitTypeSet(s) =>
        s"BitTypeSet:${s.mkString(",")}"
    }
    ,
    s => s match {
      case "TopTypeSet" => TopTypeSet
      case "EmptyTypeSet" => EmptyTypeSet
      case Prim(prim) => PrimTypeSet(prim)
      case Bit(bv) => BitTypeSet(BitSet.fromSpecific(bv.split(",").map(_.toInt)))
    }
    )
}
case object TopTypeSet extends TypeSet {
  override def intersect(other: TypeSet): TypeSet = other

  override def isEmpty: Boolean = false

  override def getValues: Option[Set[Int]] = None

  override def contains(other: TypeSet): Boolean = true

  override def filterSubTypeOf(types: Set[String])(implicit ch:ClassHierarchyConstraints): TypeSet =
    this //TODO: this probably loses precision
  override def intersectNonEmpty(other: TypeSet): Boolean = true

  override def contains(i: Int): Boolean = true

  override def union(other: TypeSet): TypeSet = TopTypeSet
}
case object EmptyTypeSet extends TypeSet{
  override def intersect(other: TypeSet): TypeSet = EmptyTypeSet

  override def isEmpty: Boolean = true

  override def getValues: Option[Set[Int]] = Some(Set())

  override def contains(other: TypeSet): Boolean = other match{
    case EmptyTypeSet => true
    case _ => false
  }

  override def filterSubTypeOf(types: Set[String])(implicit ch:ClassHierarchyConstraints): TypeSet = EmptyTypeSet

  override def intersectNonEmpty(other: TypeSet): Boolean = false

  override def contains(i: Int): Boolean = false

  override def union(other: TypeSet): TypeSet = other
}

case object PrimTypeSet{
  implicit var rw:RW[PrimTypeSet] = macroRW
}
case class PrimTypeSet(name:String) extends TypeSet {
  override def intersect(other: TypeSet): TypeSet = if(contains(other)) this else EmptyTypeSet

  override def union(other:TypeSet):TypeSet = other match {
    case TopTypeSet => TopTypeSet
    case EmptyTypeSet => this
    case PrimTypeSet(otherName) if otherName == name => this
    case ts => throw new IllegalArgumentException(s"cannot union primitive type set with: ${ts}")
  }

  override def isEmpty: Boolean = false

  /**
   * Get set of integers representing types that can inhabit this type set
   *
   * @return None if top type set Some otherwise
   */
  override def getValues: Option[Set[Int]] = {
    val primInd = ClassHierarchyConstraints.primitiveTypes.indexOf(name)
    Some(Set(-primInd))
  }
  override def contains(other: TypeSet): Boolean = other match{
    case PrimTypeSet(otherName) if name == otherName => true
    case EmptyTypeSet => true
    case _ => false
  }

  override def filterSubTypeOf(types: Set[String])(implicit ch: ClassHierarchyConstraints): TypeSet =
    if(types.contains(name)) this else EmptyTypeSet


  override def intersectNonEmpty(other: TypeSet): Boolean = !intersect(other).isEmpty

  override def contains(i: Int): Boolean = false
}
object BitTypeSet{
  implicit var rw:RW[BitTypeSet] = upickle.default.readwriter[String].bimap[BitTypeSet](
    {
      case BitTypeSet(s) => ??? //s.mkString(",")
    }
    ,
    {
      str => BitTypeSet(BitSet.fromSpecific(str.split(",").map(_.toInt)))
    }
  )
}
case class BitTypeSet(s:BitSet) extends TypeSet {
  override def toString: String = s"{${s.take(5).mkString(",")}${if(s.size > 5) " ..." else ""}}"
  def stringRep(ch:ClassHierarchyConstraints):String =
    "{" + s.take(3).map(ch.intToString).mkString(",") + "}"
  override def intersect(other: TypeSet): TypeSet = other match{
    case BitTypeSet(otherS) => BitTypeSet(s.intersect(otherS))
    case TopTypeSet => this
    case PrimTypeSet(_) => EmptyTypeSet
    case EmptyTypeSet => EmptyTypeSet
  }

  override def isEmpty: Boolean = s.isEmpty

  override def getValues: Option[Set[Int]] = {
    Some(s.toSet)
  }


  override def contains(other: TypeSet): Boolean = other match{
    case EmptyTypeSet => true
    case PrimTypeSet(_) => false
    case TopTypeSet => false
    case BitTypeSet(otherS) => otherS.subsetOf(s)
  }

  override def filterSubTypeOf(types: Set[String])(implicit ch:ClassHierarchyConstraints): TypeSet = {
    if(types.contains("_")){
      return this
    }
    val newSet = s.filter { v =>
      val strName = ch.intToString(v)
      val supers = ch.getSupertypesOf(strName)
      types.exists(supers.contains)
    }
    BitTypeSet(newSet)
  }
  override def intersectNonEmpty(other: TypeSet): Boolean = !intersect(other).isEmpty

  override def contains(i: Int): Boolean = s.contains(i)

  override def union(other: TypeSet): TypeSet = other match {
    case TopTypeSet => TopTypeSet
    case EmptyTypeSet => this
    case p:PrimTypeSet => throw new IllegalArgumentException(s"Cannot union with primitive type set: ${this} + ${p}")
    case BitTypeSet(otherS) => BitTypeSet(s.union(otherS))
  }
}


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
    SwitchCmd.rw, Goto.rw)
}

/**
 *
 * @param returnVar None if void return otherwise local returned by cmd
 * @param loc location of command in app
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

case class Goto(b:RVal, trueLoc:AppLoc, loc:AppLoc) extends CmdWrapper(loc){
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
}
object Goto{
  implicit var rw:RW[Goto] = macroRW
}

case class NopCmd(loc:AppLoc) extends CmdWrapper(loc){
  override def mkPre: CmdWrapper = this.copy(loc=loc.copy(isPre = true))
}
object NopCmd{
  implicit var rw:RW[NopCmd] = macroRW
}


/**
 *
 * @param key variable being switched if exists (sometimes is a const???)
 * @param targets
 * @param loc location in app after command //TODO: it seems there should be a cleaner way to implement this
 */
case class SwitchCmd(key: Option[LocalWrapper], targets : List[CmdWrapper], loc:AppLoc) extends CmdWrapper(loc) {
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
 * @param str string representation of ommitted command for debugging
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
  def targetSignature:Signature
  def params:List[RVal]
  def targetOptional: Option[LocalWrapper]
}
object Invoke{
  implicit val rw:RW[Invoke] = RW.merge(macroRW[VirtualInvoke], macroRW[SpecialInvoke], macroRW[StaticInvoke])
}
/*VirtualInvoke is used when dynamic dispatch can change target*/
case class VirtualInvoke(target:LocalWrapper,
                         targetClass:String,
                         targetMethod:String,
                         params:List[RVal]) extends Invoke {
  override def targetSignature: Signature = Signature(targetClass, targetMethod)
  override def targetOptional: Option[LocalWrapper] = Some(target)

  override def isConst: Boolean = false
}
/*SpecialInvoke is used when the exact class target is known*/
case class SpecialInvoke(target:LocalWrapper,
                         targetClass:String,
                         targetMethod:String,
                         params:List[RVal]) extends Invoke {
  override def targetSignature: Signature = Signature(targetClass, targetMethod)
  override def targetOptional: Option[LocalWrapper] = Some(target)

  override def isConst: Boolean = false
}
case class StaticInvoke(targetClass:String,
                        targetMethod:String,
                        params:List[RVal])extends Invoke {
  override def targetSignature: Signature = Signature(targetClass, targetMethod)
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

  //Locals are uniquely identified by name, soot often gives conflicting type info breaking type comparison
  override def equals(other:Any):Boolean = other match{
    case LocalWrapper(oName, _) =>
      name == oName
    case _ => false
  }
  override def hashCode(): Int = name.hashCode
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