package edu.colorado.plv.bounder.ir

import org.scalatest.funsuite.AnyFunSuite

import scala.util.Success


class IRParserTest extends AnyFunSuite {
  test("Parse a java reflective style name"){
    val name = "Lde/danoeh/antennapod/core/service/GpodnetSyncService;"
    val parser = new IRParser
    val res = parser.parseAll(parser.reflectiveRef, name).get
    assert(res == ClazzRef(List("de", "danoeh","antennapod","core","service"),
      "GpodnetSyncService"))
    assert(res.sootString == "de.danoeh.antennapod.core.service.GpodnetSyncService")

    val name2 = "Lde/danoeh/antennapod/core/util/NetworkUtils;"
    val res2 = IRParser.parseReflectiveRef(name2)
    assert(res2.sootString == "de.danoeh.antennapod.core.util.NetworkUtils")
    val res3 = IRParser.parseReflectiveRef("Lde/danoeh/antennapod/core/gpoddernet/model/GpodnetEpisodeAction$Action;")
    assert(res3.sootString == "de.danoeh.antennapod.core.gpoddernet.model.GpodnetEpisodeAction$Action")

    val name4 = "[Loo/o;"
    val res4 = IRParser.parseReflectiveRef(name4)
    assert(res4.sootString == "oo.o[]")

    val name5 = "[C"
    val res5 = IRParser.parseReflectiveRef(name5)
    assert(res5.sootString == "char[]")

    val name6 = "Lcom/teamdc/stephendiniz/autoaway/Activity_Filtering;"
    val res6 = IRParser.parseReflectiveRef(name6)
    assert(res6.sootString == "com.teamdc.stephendiniz.autoaway.Activity_Filtering")

    val name7 = "I"
    val res7 = IRParser.parseReflectiveRef(name7)
    assert(res7.sootString == "int")

    val name8 = "Ifoo/bar/Baz;"
    val res8 = IRParser.parseReflectiveRef(name8)
    assert(res8.sootString == "foo.bar.Baz")

    val name9 = "J"
    val res9 = IRParser.parseReflectiveRef(name9)
    assert(res9.sootString == "long")
  }
}
