package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.BounderSetupApplication
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, NI}
import edu.colorado.plv.bounder.lifestate.{SpecSpace, TestSignatures}
import edu.colorado.plv.bounder.symbolicexecutor.state.{Qry, State}
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, SymbolicExecutorConfig, TransferFunctions}
import soot.SootMethod

class SootUtilsTest extends org.scalatest.FunSuite {
  val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
  assert(test_interproc_1 != null)
  BounderSetupApplication.loadApk(test_interproc_1)

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

  /**
   * Find a predecessor of a location such that b is true
   * @param l list of locations
   * @param b functon of location that returns true when desired location is found
   * @return
   */
  def iterPredUntil(l:List[Loc], config: SymbolicExecutorConfig[SootMethod, soot.Unit], b : Loc=>Boolean):Option[Loc] =
    l.find(b) match {
      case Some(v) => Some(v)
      case None =>
        val pred: List[Loc] = l.flatMap(config.c.resolvePredicessors(_, State.topState))
        iterPredUntil(pred, config,b)
    }
  test("iterate transitions in real apk"){

    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val testSpec = LSSpec(NI(TestSignatures.Activity_onResume_entry, TestSignatures.Activity_onPause_exit),
      TestSignatures.Activity_onPause_entry) // TODO: fill in spec details for test
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set(testSpec)))
    val config: SymbolicExecutorConfig[SootMethod, soot.Unit] = SymbolicExecutorConfig(
      stepLimit = Some(50), w,resolver,transfer, printProgress = true, z3Timeout = Some(30))
    val query = Qry.makeReceiverNonNull(config, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val l = query.loc
    assert(l.isInstanceOf[AppLoc])

    val entryloc = iterPredUntil(List(l), config, {
      case curLoc@AppLoc(method, line, true) =>
        println(curLoc)
        w.isMethodEntry(w.cmdAfterLocation(curLoc))
      case l@AppLoc(method, line, false) => println(l);false
      case l => println(l);false
    })
    ???

//    w.cmdBeforeLocation()

  }
}
