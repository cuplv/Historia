package edu.colorado.plv.bounder.testutils

import org.scalatest.funsuite.AnyFunSuite
import MkApk.jenvVersionIsValid

class MkApkTest extends AnyFunSuite{
  test("jenvVersionIsValid only accepts alphanumeric or - or . characters") {
    val validVersions = List(
      "1.8",
      "1.8.0.352",
      "system",
      "openjdk64-1.8.0.352",
      "OpEnJdK64-1.8-Test-.",
    )
    val invalidVersions = List(
      "1.8*",
      "system;whoami",
      "sys tem",
      "system|cat",
      "sႸsŧɐო",
    )
    for (v <- validVersions) assert(jenvVersionIsValid(v), s"for version $v")
    for (v <- invalidVersions) assert(!jenvVersionIsValid(v), s"for version $v")
  }
}
