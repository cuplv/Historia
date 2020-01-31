package edu.colorado.plv.bounder

import soot.Scene

class BounderSetupApplicationTest extends org.scalatest.FunSuite {
  val trikita_apk = getClass.getResource("/trikita.slide_4.apk").getPath
  assert(trikita_apk != null)
  test("Load apk loads an apk.") {

    BounderSetupApplication.loadApk(trikita_apk)
    val gotSize = Scene.v().getClasses().size
    assert( gotSize === 4871 )
  }
}
