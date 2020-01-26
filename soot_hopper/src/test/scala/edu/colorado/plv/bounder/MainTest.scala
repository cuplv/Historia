package edu.colorado.plv.bounder

class MainTest extends org.scalatest.FunSuite {
  val trikita_apk = getClass.getResource("/trikita.slide_4.apk").getPath
  assert(trikita_apk != null)
  test("Load apk loads an apk.") {
    Main.loadApk(trikita_apk)
  }
}
