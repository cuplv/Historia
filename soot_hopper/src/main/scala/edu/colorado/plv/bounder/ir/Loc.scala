package edu.colorado.plv.bounder.ir
import upickle.default.write
import upickle.default.{ReadWriter => RW, macroRW}

/**
 * A source code location
 * TODO: find a way to make the type system enforce locations are not used cross wrapper implementations
 */
sealed trait Loc{
  def containingMethod:String = this match{
    case AppLoc(method, _,_) => method.toString
    case _ => ""
  }
  def msgSig : Option[String]
  def toString:String
}
object Loc{
  implicit val rw:RW[Loc] = RW.merge(macroRW[CallbackMethodInvoke], macroRW[CallinMethodReturn],
    AppLoc.rw, macroRW[CallbackMethodReturn], macroRW[InternalMethodReturn], macroRW[CallinMethodInvoke],
    macroRW[InternalMethodInvoke]
  )
}

/**
 * A method definition overridden by the IR wrapper implementation
 */
trait MethodLoc {
  def simpleName: String
  def classType: String
  def argTypes: List[String]

  /**
   * No return since call site has that info
   * None for reciever if static
   * @return list of args, [reciever, arg1,arg2 ...]
   */
  def getArgs : List[Option[LocalWrapper]]
  def isStatic:Boolean
  def isInterface:Boolean
}
object MethodLoc {
  implicit val rw:RW[MethodLoc] = upickle.default.readwriter[ujson.Value].bimap[MethodLoc](
    x => ujson.Arr(x.simpleName, x.classType, x.argTypes, x.getArgs.map(v => write(v))),
    _ => {
      throw new IllegalStateException("Deserialization of state must be done on serialized IR")
    }
  )
}

trait LineLoc
object LineLoc{
  implicit val rw:RW[LineLoc] = upickle.default.readwriter[ujson.Value].bimap[LineLoc](
    x => ujson.write(System.identityHashCode(x)),
    _ => {
      throw new IllegalStateException("Deserialization of state must be done on serialized IR")
    }
  )
}

/**
 * Represents a command location inside the application
 * @param method object representing containing method in app
 * @param line object representing containing line in app
 * @param isPre //TODO: I think this is before/after cmd?
 */
case class AppLoc(method: MethodLoc, line: LineLoc, isPre:Boolean) extends Loc {
  override def toString: String = (if(isPre) "pre-" else "post-" ) + line.toString()
  override def msgSig = None
}
object AppLoc{
  implicit val rw:RW[AppLoc] = macroRW
}

case class CallinMethodReturn(fmwClazz : String, fmwName:String) extends Loc {
  override def toString:String = "[CI Ret] " + fmwName

  override def msgSig: Option[String] = Some(s"[CI Ret] ${fmwClazz} ${fmwName}" )
}
object CallinMethodReturn{
  implicit val rw:RW[CallinMethodReturn] = macroRW
}

case class CallinMethodInvoke(fmwClazz : String, fmwName:String) extends Loc {
  override def toString:String = "[CI Inv] " + fmwName

  override def msgSig: Option[String] = Some(s"[CI Inv] ${fmwClazz} ${fmwName}")
}
object CallinMethodInvoke{
  implicit val rw:RW[CallinMethodInvoke] = macroRW
}

case class CallbackMethodInvoke(fmwClazz: String, fmwName: String, loc:MethodLoc) extends Loc {
  override def toString:String = "[CB Inv] " + fmwName
  override def msgSig: Option[String] = Some(s"[CB Inv] ${fmwClazz} ${fmwName}")
}
object CallbackMethodInvoke{
  implicit val rw:RW[CallbackMethodInvoke] = macroRW
}

// post state of return on callback
case class CallbackMethodReturn(fmwClazz: String, fmwName:String, loc:MethodLoc, line:Option[LineLoc]) extends Loc {
  override def toString:String = "[CB Ret] " + fmwName
  override def msgSig: Option[String] = Some(s"")
}
object CallbackMethodReturn{
  implicit val rw:RW[CallbackMethodReturn] = macroRW
}

case class InternalMethodInvoke(clazz:String, name:String, loc:MethodLoc) extends Loc {
  override def msgSig: Option[String] = None
}
object InternalMethodInvoke{
  implicit val rw:RW[InternalMethodInvoke] = macroRW
}

case class InternalMethodReturn(clazz:String, name:String, loc:MethodLoc) extends Loc {
  override def msgSig: Option[String] = None
}
object InternalMethodReturn{
  implicit val rw:RW[InternalMethodReturn] = macroRW
}
