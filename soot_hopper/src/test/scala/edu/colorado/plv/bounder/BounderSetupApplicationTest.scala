package edu.colorado.plv.bounder

import soot.Scene
import scala.jdk.CollectionConverters._

class BounderSetupApplicationTest extends org.scalatest.FunSuite {
  val trikita_apk = getClass.getResource("/trikita.slide_4.apk").getPath
  assert(trikita_apk != null)
  test("Load apk loads an apk.") {

    BounderSetupApplication.loadApk(trikita_apk)
    val gotSize = Scene.v().getClasses().size
    assert( gotSize === 2060 )
    //TODO: individual java file loading so unit tests are easier
//    BounderSetupApplication.loadClass("/Users/shawnmeier/Desktop/Test.java")
//    val testClass = Scene.v().getClasses.asScala.filter(a => a.getName == "Test")
//    ???
  }
}
