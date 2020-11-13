package edu.colorado.plv.bounder.ir

/**
 * A source code location
 * TODO: find a way to make the type system enforce locations are not used cross wrapper implementations
 */
trait Loc{
  def containingMethod:String = this match{
    case AppLoc(method, _,_) => method.toString
    case _ => ""
  }
  def msgSig : Option[String]
}

/**
 * A method definition overridden by the IR wrapper implementation
 */
trait MethodLoc {
  def simpleName: String
  def classType: String
  def argTypes: List[String]
  // TODO: handle params
  // def argNames:List[String]
}
trait LineLoc

/**
 * Represents a command location inside the application
 * @param method object representing containing method in app
 * @param line object representing containing line in app
 * @param isPre //TODO: I think this is before/after cmd?
 */
case class AppLoc(method: MethodLoc, line: LineLoc, isPre:Boolean) extends Loc {
  override def toString: String = line.toString()
  override def msgSig = None
}

case class CallinMethodReturn(fmwClazz : String, fmwName:String) extends Loc {
  override def toString:String = "[CI Ret] " + fmwName

  override def msgSig: Option[String] = Some(s"[CI Ret] ${fmwClazz} ${fmwName}" )
}
case class CallinMethodInvoke(fmwClazz : String, fmwName:String) extends Loc {
  override def toString:String = "[CI Inv] " + fmwName

  override def msgSig: Option[String] = Some(s"[CI Inv] ${fmwClazz} ${fmwName}")
}
case class CallbackMethodInvoke(fmwClazz: String, fmwName: String, loc:MethodLoc) extends Loc {
  override def msgSig: Option[String] = Some(s"[CB Inv] ${fmwClazz} ${fmwName}")
}
// post state of return on callback
case class CallbackMethodReturn(fmwClazz: String, fmwName:String, loc:MethodLoc, line:Option[LineLoc]) extends Loc {
  override def msgSig: Option[String] = Some(s"")
}

case class InternalMethodInvoke(clazz:String, name:String, loc:MethodLoc) extends Loc {
  override def msgSig: Option[String] = None
}
case class InternalMethodReturn(clazz:String, name:String, loc:MethodLoc) extends Loc {
  override def msgSig: Option[String] = None
}
