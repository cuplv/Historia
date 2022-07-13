package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.BounderSetupApplication
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, NS}
import edu.colorado.plv.bounder.lifestate.{SpecSignatures, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state._
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, ControlFlowResolver, DefaultAppCodeResolver, FlowdroidCallGraph, SparkCallGraph, SymbolicExecutor, SymbolicExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

import scala.annotation.tailrec

class SootUtilsTest extends AnyFunSuite {


  test("findMethodLoc should find a location based on a classname and line number."){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
    assert(test_interproc_1 != null)
    BounderSetupApplication.loadApk(test_interproc_1, SparkCallGraph)
    val res = SootUtils.findMethodLoc(
      "com.example.test_interproc_1.MainActivity", "java.lang.String objectString()")
    assert(res.isDefined)
  }

  test("findMethodLoc should return none if the class or method does not exist"){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
    assert(test_interproc_1 != null)
    BounderSetupApplication.loadApk(test_interproc_1, SparkCallGraph)
    val res: Option[JimpleMethodLoc] = SootUtils.findMethodLoc("non.existant.class", "33")
    assert(!res.isDefined)
    val res2 = SootUtils.findMethodLoc(
      "com.example.test_interproc_1.MainActivity", "java.lang.String ctString()")
    assert(!res2.isDefined)
  }

  test("findLineInMethod should find a UnitLoc"){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
    assert(test_interproc_1 != null)
    BounderSetupApplication.loadApk(test_interproc_1, SparkCallGraph)
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
  private def iterPredUntil[M,C](l:Set[Loc],
                            resolver:ControlFlowResolver[M,C],
                            b : Loc=>Boolean,
                            state: State,
                            count:Int):Option[Loc] = {
    if (count == 0) {
      return None
    }
    println(l)
    l.find(b) match {
      case Some(v) => Some(v)
      case None =>
        val pred: Set[Loc] = l.flatMap(resolver.resolvePredicessors(_, state))
        if(pred.isEmpty)
          None
        else
          iterPredUntil(pred, resolver,b,state, count-1)
    }
  }

  test("iterate transitions in real apk onPause"){
    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, SparkCallGraph, Set())
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val testSpec = LSSpec("a"::Nil, Nil, NS(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit),
      SpecSignatures.Activity_onPause_entry)
    val config: SymbolicExecutorConfig[SootMethod, soot.Unit] = SymbolicExecutorConfig(
      stepLimit = 50, w, new SpecSpace(Set(testSpec)), printProgress = true, z3Timeout = Some(30))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeReceiverNonNull(symbolicExecutor,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()", 27)
    val l = query.find {
      case LiveQry(s, _) if s.callStack.head.exitLoc.isInstanceOf[CallbackMethodReturn] => true
      case _ => false
    }.get.loc


    val entryloc = iterPredUntil(Set(l), symbolicExecutor.controlFlowResolver, {
      case CallbackMethodInvoke(_, _, _) => true
      case l => false
    }, State.topState, 12)
    assert(entryloc.isDefined)

    println("---")
    val tr = AbstractTrace(SpecSignatures.Activity_onPause_entry::Nil, Map()) //TODO: fix this test==== probably need spec
    val retPause = iterPredUntil(Set(l), symbolicExecutor.controlFlowResolver, {
      case CallbackMethodReturn(_, name, _, _) if name.contains("onPause") => true
      case _ => false
    }, State.topState.copy(sf =
      State.topState.sf.copy(traceAbstraction = tr)), 20)
    assert(retPause.isDefined)
  }
  test("iterate to parameter assignments onCreate"){

    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new JimpleFlowdroidWrapper(test_interproc_1, SparkCallGraph, Set())
    val testSpec = LSSpec("a"::Nil, Nil, NS(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit),
      SpecSignatures.Activity_onPause_entry) // TODO: fill in spec details for test
    val config: SymbolicExecutorConfig[SootMethod, soot.Unit] = SymbolicExecutorConfig(
      stepLimit = 50, w, new SpecSpace(Set(testSpec)), printProgress = true, z3Timeout = Some(30))
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeReach(symbolicExecutor,
      "com.example.test_interproc_2.MainActivity",
      "void onCreate(android.os.Bundle)", 16)

    val l = query.find {
      case LiveQry(s, _) if s.callStack.head.exitLoc.isInstanceOf[CallbackMethodReturn] => true
      case _ => false
    }.get.loc

    val entryloc = iterPredUntil(Set(l), symbolicExecutor.controlFlowResolver, {
      case CallbackMethodInvoke(_, _, _) => true
      case l@AppLoc(a, b, false) =>
        val cmd = w.cmdAtLocation(l)
        false
      case l => false
    }, State.topState, 12)
    assert(entryloc.isDefined)
  }
}
