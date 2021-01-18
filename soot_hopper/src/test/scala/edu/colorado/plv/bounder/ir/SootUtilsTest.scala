package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.BounderSetupApplication
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, NI}
import edu.colorado.plv.bounder.lifestate.{SpecSpace, SpecSignatures}
import edu.colorado.plv.bounder.symbolicexecutor.state.{Qry, State}
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, SymbolicExecutorConfig, TransferFunctions}
import soot.SootMethod

import scala.annotation.tailrec

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

  @tailrec
  /**
   * Find a predecessor of a location such that b is true
   * @param l list of locations
   * @param b functon of location that returns true when desired location is found
   * @return
   */
  private def iterPredUntil(l:Set[Loc], config: SymbolicExecutorConfig[SootMethod, soot.Unit], b : Loc=>Boolean, count:Int):Option[Loc] = {
    if (count == 0) {
      return None
    }
    println(l)
    l.find(b) match {
      case Some(v) => Some(v)
      case None =>
        val pred: Set[Loc] = l.flatMap(config.c.resolvePredicessors(_, State.topState))
        if(pred.isEmpty)
          None
        else
          iterPredUntil(pred, config,b, count-1)
    }
  }

  test("iterate transitions in real apk onPause"){

    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val testSpec = LSSpec(NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit),
      SpecSignatures.Activity_onPause_entry) // TODO: fill in spec details for test
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set(testSpec)))
    val config: SymbolicExecutorConfig[SootMethod, soot.Unit] = SymbolicExecutorConfig(
      stepLimit = Some(50), w,resolver,transfer, printProgress = true, z3Timeout = Some(30))
    val query = Qry.makeReceiverNonNull(config, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val l = query.loc
    assert(l.isInstanceOf[AppLoc])

    val entryloc = iterPredUntil(Set(l), config, {
      case CallbackMethodInvoke(_,_,_) => true
      case l => false
    }, 12)
    assert(entryloc.isDefined)

    println("---")
    val retPause = iterPredUntil(Set(l), config, {
      case CallbackMethodReturn(_,name,_,_) if name.contains("onPause") => true
      case _ => false
    },20)
    assert(retPause.isDefined)
  }
  test("iterate to parameter assignments onCreate"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val testSpec = LSSpec(NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit),
      SpecSignatures.Activity_onPause_entry) // TODO: fill in spec details for test
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set(testSpec)))
    val config: SymbolicExecutorConfig[SootMethod, soot.Unit] = SymbolicExecutorConfig(
      stepLimit = Some(50), w,resolver,transfer, printProgress = true, z3Timeout = Some(30))
    val query = Qry.makeReach(config, w,
      "com.example.test_interproc_2.MainActivity",
      "void onCreate(android.os.Bundle)",16)
    val l = query.loc
    assert(l.isInstanceOf[AppLoc])

    val entryloc = iterPredUntil(Set(l), config, {
      case CallbackMethodInvoke(_,_,_) => true
      case l@AppLoc(a,b,false) =>
        println(a)
        println(b)
        val cmd = w.cmdAtLocation(l)
        println(cmd)
        false
      case l => false
    }, 12)
    assert(entryloc.isDefined)

  }
}
