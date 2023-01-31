package edu.colorado.plv.bounder

import better.files.Resource
import edu.colorado.plv.bounder.BounderSetupApplication.JarSource
import edu.colorado.plv.bounder.ir.{BitTypeSet, SootWrapper, TopTypeSet, TypeSet}
import edu.colorado.plv.bounder.lifestate.{LSExpParser, LifeState}
import edu.colorado.plv.bounder.symbolicexecutor.SparkCallGraph
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoolVal, ClassType, DBPathNode, IntVal, NamedPureVar, PureExpr, PureVar, State, SubclassOf, TopVal, TypeConstraint}
import org.scalatest.funsuite.AnyFunSuite
import soot.Scene
import upickle.default._

import scala.collection.BitSet

class BounderSetupApplicationTest extends AnyFunSuite {
  val trikita_apk = getClass.getResource("/trikita.slide_4.apk").getPath
  assert(trikita_apk != null)
  test("Load apk loads an apk.") {
    BounderSetupApplication.loadApk(trikita_apk)
    val gotSize = Scene.v().getClasses().size
    assert( gotSize > 2000 )
  }
  test("LSRegex"){
    //    def m(s:String):String= {
    //      s match {
    //        case LifeState.LSBoolConst(_) => "bool"
    //        case LifeState.LSVar(v) => s"var:$v"
    //        case LifeState.LSAnyVal() => "any"
    //        case _ => "NONE"
    //      }
    //    }
    val m: String => PureExpr = LSExpParser.convert
    assert(m("@true") == BoolVal(true))
    assert(m("A_") == NamedPureVar("A_"))
    assert(LSExpParser.LSVarReg.matches("A9"))
    assert(!LSExpParser.LSVarReg.matches("0"))
    assert(!LSExpParser.LSVarReg.matches("_"))
    assert(!LSExpParser.LSVarReg.matches("@null"))
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
    val s2 = State.topState.copy(sf = State.topState.sf.copy(typeConstraints =
      Map(PureVar(1) -> bTS)))
    val s2ser = write(s2)
    val s2deser = read[State](s2ser)
    assert(s2 == s2deser)
  }

  private val js = (name:String) => ujson.Value(Resource.getAsString(name)).obj
//  test("Deserialize old json loc with system identity hash code only"){
//    val v = read[DBPathNode](js("TestStates/badJson"))
//    println(v)
//  }

  val simple_jar = getClass.getResource("/JarTest.jar").getPath
  test("Load Class file"){
    BounderSetupApplication.loadApk(simple_jar, sourceType = JarSource)
    assert(Scene.v().getMainClass.getName == "JarTest")
  }
}
