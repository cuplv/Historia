package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.SetupApplication

class SootUtilsTest extends org.scalatest.FunSuite {
  val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
  assert(test_interproc_1 != null)
  SetupApplication.loadApk(test_interproc_1)

  test("findMethodLoc should find a location based on a classname and line number."){
    val res = SootUtils.findMethodLoc(
      "com.example.test_interproc_1.MainActivity", "java.lang.String objectString()")
    assert(res.isDefined)

  }

  test("findMethodLoc should return none if the class or method does not exist"){
    val res: Option[JimpleMethodLoc] = SootUtils.findMethodLoc("non.existant.class","33")
    assert(!res.isDefined)
    val res2 = SootUtils.findMethodLoc(
      "com.example.test_interproc_1.MainActivity", "java.lang.String ctString()")
    assert(!res2.isDefined)
  }

  test("findLineInMethod should find a UnitLoc"){
    val res = SootUtils.findMethodLoc(
      "com.example.test_interproc_1.MainActivity", "java.lang.String objectString()")

    val locs = SootUtils.findLineInMethod(21, res.get)
    assert(locs.size > 0)
  }
}
