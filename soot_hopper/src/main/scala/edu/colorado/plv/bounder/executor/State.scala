package edu.colorado.plv.bounder.executor

import edu.colorado.plv.bounder.executor.State.{Address, IObject, MetaVal}

object State {
  trait MetaVal
  case object Null extends MetaVal
  case class Address(v:Int) extends MetaVal

  case class IObject(valType:String, fields: Map[String,MetaVal])
  def initialState(initialActivity: String): State = {
    def fields = ???
    State(Map(initialActivity->Address(1)), Map(Address(1)->IObject(initialActivity, fields)))
  }
}

/**
 *
 * @param registered mapping from concrete app types to addresses
 */
case class State(registered: Map[String, Address], heap: Map[Address, IObject])


// Representation of state before and after executing a block
// Maps params to values
// Maps heap locations reachable from params
case class ParamState(rec : Int, state: State) {

}