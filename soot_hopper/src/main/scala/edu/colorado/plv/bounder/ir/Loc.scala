package edu.colorado.plv.bounder.ir
import upickle.default.{read, write}
import upickle.default.{macroRW, ReadWriter => RW}

import scala.util.matching.Regex

/**
 * A source code location
 * TODO: find a way to make the type system enforce locations are not used cross wrapper implementations
 */
sealed trait Loc{
  def containingMethod:Option[MethodLoc] = this match{
    case AppLoc(method, _,_) => Some(method)
    case _ => None
  }
  def msgSig : Option[String]
  def toString:String
}
object Loc{
  implicit val rw:RW[Loc] = RW.merge(macroRW[CallbackMethodInvoke], macroRW[CallinMethodReturn],
    AppLoc.rw, macroRW[CallbackMethodReturn], macroRW[InternalMethodReturn], macroRW[CallinMethodInvoke],
    macroRW[InternalMethodInvoke], GroupedCallinMethodReturn.rw, GroupedCallinMethodInvoke.rw
  )
}

/**
 * A method definition overridden by the IR wrapper implementation
 */
trait MethodLoc {
  def simpleName: String
  def classType: String
  def argTypes: List[String]
  def bodyToString: String

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
  private val rmQuotes: Regex = "^\"(.*)\"$".r
  implicit val rw:RW[MethodLoc] = upickle.default.readwriter[ujson.Value].bimap[MethodLoc](
    x => ujson.Arr(x.simpleName, x.classType, x.argTypes, x.getArgs.map(v => write(v))),
    json => {
      val name = json.arr(0).str
      val clazz = json.arr(1).str
      val args = json.arr(3).arr.map { v =>
        val v0 = ujson.read(v.str)
        if (v0.arr.isEmpty) {
          None
        } else {
          val name = v0(0).obj("name").str
          val t = v0(0).obj("localType").str
          Some(LocalWrapper(name, t))
        }
      }.toList
      TestIRMethodLoc(clazz, name, args)
    }
  )
}

trait LineLoc
object LineLoc{
  implicit val rw:RW[LineLoc] = upickle.default.readwriter[ujson.Value].bimap[LineLoc](
    x =>
      ujson.Obj("id" -> System.identityHashCode(x), "str" -> x.toString),
    json => json match {
      case ujson.Str(v) => TestIRLineLoc (v.toInt,"")
      case ujson.Obj(v) => TestIRLineLoc (v("id").num.toInt, v("str").str)
      case v => throw new IllegalArgumentException(s"Cannot parse $v as LineLoc")
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
  override def msgSig = Some(s"[Int] ${method.simpleName}")
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

case class GroupedCallinMethodInvoke(targetClasses: Set[String], fmwName:String) extends Loc {
  override def toString:String = "[CI Inv merge] " + fmwName
  override def msgSig: Option[String] = Some(s"[CI Inv] ${targetClasses.head} ${fmwName}")
}
object GroupedCallinMethodInvoke{
  implicit val rw:RW[GroupedCallinMethodInvoke] = macroRW
}

//TODO: could probably merge this with the CallinMethod classes
case class GroupedCallinMethodReturn(targetClasses: Set[String], fmwName:String) extends Loc {
  override def toString:String = "[CI Ret merge] " + fmwName
  override def msgSig: Option[String] = Some(s"[CI Ret] ${targetClasses.head} ${fmwName}")
}
object GroupedCallinMethodReturn{
  implicit val rw:RW[GroupedCallinMethodReturn] = macroRW
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
