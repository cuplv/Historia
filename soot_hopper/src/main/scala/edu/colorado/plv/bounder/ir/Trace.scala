package edu.colorado.plv.bounder.ir
import upickle.default.{ReadWriter => RW, macroRW}


object Trace {

}
sealed trait MessageType
object MessageType{
  implicit var rw:RW[MessageType] = RW.merge(macroRW[CIEnter.type],  macroRW[CIExit.type],
    macroRW[CBEnter.type], macroRW[CBExit.type])
}
case object CIEnter extends MessageType
case object CIExit extends MessageType
case object CBEnter extends MessageType
case object CBExit extends MessageType

sealed trait Method {
  def name : String
  def fwkSig : Option[(String,String)]
}
case class AppMethod(name: String, declaringType: String, fwkOverride : Option[FwkMethod]) extends Method{
  override def fwkSig: Option[(String, String)] = fwkOverride.flatMap(_.fwkSig)
}
case class FwkMethod(name: String, declaringType : String) extends Method{
  override def fwkSig: Option[(String, String)] = Some(name,declaringType)
}

case class TMessage(mType : MessageType, method: Method, args: List[TVal]){
  def fwkSig = method.fwkSig
}
sealed trait TVal
case class TAddr(i:Int) extends TVal
case object TNullVal extends TVal
