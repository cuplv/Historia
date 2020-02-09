package edu.colorado.plv.bounder.ir

/**
 * A source code location
 * TODO: find a way to make the type system enforce locations are not used cross wrapper implementations
 */
sealed trait Loc{
  def containingMethod:String = this match{
    case AppLoc(method, _,_) => method.toString
    case _ => ""
  }
}

/**
 * A method definition overridden by the IR wrapper implementation
 */
trait MethodLoc
case class CallinMethodLoc() extends MethodLoc
trait LineLoc
case class AppLoc(method: MethodLoc, line: LineLoc, isPre:Boolean) extends Loc {
  override def toString: String = line.toString()
}

//sealed trait MethodReference
// Framework method invoked by application
case class CallinMethodReturn(fmwClazz : String, fmwName:String) extends Loc {
  override def toString:String = "[CI Ret] " + fmwName
}
case class CallinMethodInvoke(fmwClazz : String, fmwName:String) extends Loc {
  override def toString:String = "[CI Inv] " + fmwName
}
case class CallbackMethodReturn(fmwClazz: String, fmwName:String, loc:MethodLoc) extends Loc
// Can only be invoked by application
case class InternalMethodReturn(clazz:String, name:String, loc:MethodLoc) extends Loc
