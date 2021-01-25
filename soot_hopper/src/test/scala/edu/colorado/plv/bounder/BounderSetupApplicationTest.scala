package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.symbolicexecutor.FlowdroidCallGraph
import org.scalatest.funsuite.AnyFunSuite
import soot.Scene

import scala.jdk.CollectionConverters._

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
}
