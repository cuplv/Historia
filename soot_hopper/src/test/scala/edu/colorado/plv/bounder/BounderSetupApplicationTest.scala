package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.symbolicexecutor.FlowdroidCallGraph
import edu.colorado.plv.bounder.symbolicexecutor.state.{ClassType, IntVal, PureExpr, PureVal, PureVar, State, SubclassOf, TypeConstraint}
import org.scalatest.funsuite.AnyFunSuite
import soot.Scene
import upickle.default._

class BounderSetupApplicationTest extends AnyFunSuite {
  val trikita_apk = getClass.getResource("/trikita.slide_4.apk").getPath
  assert(trikita_apk != null)
  test("Load apk loads an apk.") {

    BounderSetupApplication.loadApk(trikita_apk, FlowdroidCallGraph)
    val gotSize = Scene.v().getClasses().size
    assert( gotSize > 2000 )
    //TODO: individual java file loading so unit tests are easier
//    BounderSetupApplication.loadClass("/Users/shawnmeier/Desktop/Test.java")
//    val testClass = Scene.v().getClasses.asScala.filter(a => a.getName == "Test")
//    ???
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
    // TODO: state serialization for better dbg support
    val v: List[PureExpr] = List(SubclassOf("foo"), ClassType("bar"), IntVal(3), PureVar(7))
    val serialized = write(v)
    val deserialized = read[List[PureExpr]](serialized)
    assert(v === deserialized)
  }
}
