package edu.colorado.plv.bounder.ir


object Trace {

}
sealed trait MessageType
case object CIEnter extends MessageType
case object CIExit extends MessageType
case object CBEnter extends MessageType
case object CBExit extends MessageType

sealed trait Method {
  def name : String
}
case class AppMethod(retType : String,
                     name: String,
                     argTypes: List[String], declaringType: String, fwkOverride : Option[FwkMethod]) extends Method
case class FwkMethod(retType : String, name: String, argTypes: List[String], declaringType : String) extends Method

case class Message(mType : MessageType, method: Method)
