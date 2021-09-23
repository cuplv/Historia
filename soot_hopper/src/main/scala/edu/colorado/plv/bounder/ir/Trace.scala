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
object Method{
  implicit var rw:RW[Method] = RW.merge(AppMethod.rw, FwkMethod.rw)
}
case class AppMethod(name: String, declaringType: String, fwkOverride : Option[FwkMethod]) extends Method{
  override def fwkSig: Option[(String, String)] = fwkOverride.flatMap(_.fwkSig)
}
object AppMethod{
  implicit var rw:RW[AppMethod] = macroRW
}
case class FwkMethod(name: String, declaringType : String) extends Method{
  override def fwkSig: Option[(String, String)] = Some(name,declaringType)
}
object FwkMethod{
  implicit var rw:RW[FwkMethod] = macroRW
}

sealed trait TraceElement
object TraceElement{
  implicit var rw:RW[TraceElement] = RW.merge(TNew.rw, TMessage.rw)
}

case class TNew(v:TVal) extends TraceElement
object TNew{
  implicit var rw:RW[TNew] = macroRW
}
case class TMessage(mType : MessageType, method: Method, args: List[TVal]) extends TraceElement {
  def fwkSig = method.fwkSig
}
object TMessage{
  implicit var rw:RW[TMessage] = macroRW
}
sealed trait TVal
object TVal{
  implicit var rw:RW[TVal] = RW.merge(macroRW[TAddr], macroRW[TNullVal.type])
}
case class TAddr(i:Int) extends TVal
case object TNullVal extends TVal


case class WitnessExplanation(past:List[TraceElement])
object WitnessExplanation{
  implicit var rw:RW[WitnessExplanation] = macroRW
}
