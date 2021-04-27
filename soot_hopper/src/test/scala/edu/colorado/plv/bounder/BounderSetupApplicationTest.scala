package edu.colorado.plv.bounder

import better.files.Resource
import edu.colorado.plv.bounder.ir.{BitTypeSet, JimpleFlowdroidWrapper, TopTypeSet, TypeSet}
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.symbolicexecutor.{FlowdroidCallGraph, SparkCallGraph}
import edu.colorado.plv.bounder.symbolicexecutor.state.{ClassType, DBPathNode, IntVal, PureExpr, PureVar, State, SubclassOf, TypeConstraint}
import org.scalatest.funsuite.AnyFunSuite
import soot.Scene
import upickle.default._

import scala.collection.BitSet

class BounderSetupApplicationTest extends AnyFunSuite {
  val trikita_apk = getClass.getResource("/trikita.slide_4.apk").getPath
  assert(trikita_apk != null)
  test("Load apk loads an apk.") {
    BounderSetupApplication.loadApk(trikita_apk, SparkCallGraph)
    val gotSize = Scene.v().getClasses().size
    assert( gotSize > 2000 )
  }
  test("LSRegex"){
    def m(s:String):String= {
      s match {
        case LifeState.LSBoolConst(_) => "bool"
        case LifeState.LSVar(v) => s"var:$v"
        case LifeState.LSAnyVal() => "any"
        case _ => "NONE"
      }
    }
    assert(m("@true") == "bool")
    assert(m("_") == "any")
    assert(m("A_") == "var:A_")
    assert(LifeState.LSVar.matches("A9"))
    assert(!LifeState.LSVar.matches("0"))
    assert(!LifeState.LSVar.matches("_"))
    assert(!LifeState.LSVar.matches("@null"))
  }

  test("State serialization"){
    val v: List[PureExpr] = List(IntVal(3), PureVar(7))
    val serialized = write(v)
    val deserialized = read[List[PureExpr]](serialized)
    assert(v === deserialized)

    val topStateSer = write[State](State.topState)
    val stateRead: State = read[State](topStateSer)
    assert(stateRead == State.topState)

//    val bTS = BoundedTypeSet(Some("Object"), None, Set())
    val bTS:TypeSet = TopTypeSet
    val sbts = write(bTS)
    val s2 = State.topState.copy(typeConstraints =
      Map(PureVar(1) -> bTS))
    val s2ser = write(s2)
    val s2deser = read[State](s2ser)
    assert(s2 == s2deser)
  }

  private val js = (name:String) => ujson.Value(Resource.getAsString(name)).obj
//  test("Deserialize old json loc with system identity hash code only"){
//    val v = read[DBPathNode](js("TestStates/badJson"))
//    println(v)
//  }
}
