package edu.colorado.plv.bounder.state

object State {
  private var id:Int = -1
  def getId():Int = {
    id = id + 1
    id
  }
}
sealed trait Val
//TODO: why no apparant nullval in hopper?
case object TopVal extends Val
case object NullVal extends Val

/**
 * Val that is instantiated from a subtype of className
 */
case class ObjSubtypeVal(className:String) extends Val{
  val id = State.getId()
}

sealed trait Var
case class StackVar(name : String) extends Var