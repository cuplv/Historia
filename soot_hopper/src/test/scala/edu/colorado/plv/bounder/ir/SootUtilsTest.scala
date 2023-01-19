package edu.colorado.plv.bounder.ir

import edu.colorado.plv.bounder.BounderSetupApplication
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, NS, Signature}
import edu.colorado.plv.bounder.lifestate.{SpecSignatures, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state._
import edu.colorado.plv.bounder.symbolicexecutor.{AbstractInterpreter, ControlFlowResolver, DefaultAppCodeResolver, SparkCallGraph, ExecutorConfig, TransferFunctions}
import org.scalatest.funsuite.AnyFunSuite
import soot.SootMethod

import scala.annotation.tailrec

class SootUtilsTest extends AnyFunSuite {


  test("findMethodLoc should find a location based on a classname and line number."){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
    assert(test_interproc_1 != null)
    BounderSetupApplication.loadApk(test_interproc_1)
    val res = SootUtils.findMethodLoc(
      "com.example.test_interproc_1.MainActivity", "java.lang.String objectString()")
    assert(res.isDefined)
  }

  test("findMethodLoc should return none if the class or method does not exist"){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
    assert(test_interproc_1 != null)
    BounderSetupApplication.loadApk(test_interproc_1)
    val res: Option[JimpleMethodLoc] = SootUtils.findMethodLoc("non.existant.class", "33")
    assert(!res.isDefined)
    val res2 = SootUtils.findMethodLoc(
      "com.example.test_interproc_1.MainActivity", "java.lang.String ctString()")
    assert(!res2.isDefined)
  }

  test("findLineInMethod should find a UnitLoc"){
    val test_interproc_1 = getClass.getResource("/test_interproc_1.apk").getPath()
    assert(test_interproc_1 != null)
    BounderSetupApplication.loadApk(test_interproc_1)
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
    val w = new SootWrapper(test_interproc_1, Set())
//    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val a = NamedPureVar("a")
    val testSpec = LSSpec(a::Nil, Nil, NS(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit),
      SpecSignatures.Activity_onPause_entry)
    val config: ExecutorConfig[SootMethod, soot.Unit] = ExecutorConfig(
      stepLimit = 50, w, new SpecSpace(Set(testSpec)), printAAProgress = true, z3Timeout = Some(30))
    val symbolicExecutor = config.getAbstractInterpreter
    val query = Qry.makeReceiverNonNull(symbolicExecutor,
      Signature("com.example.test_interproc_2.MainActivity", "void onPause()"), 27)
    val l = query.find {
      case Qry(s, _,Live) if s.callStack.head.exitLoc.isInstanceOf[CallbackMethodReturn] => true
      case _ => false
    }.get.loc


    val entryloc = iterPredUntil(Set(l), symbolicExecutor.controlFlowResolver, {
      case _:CallbackMethodInvoke => true
      case l => false
    }, State.topState, 12)
    assert(entryloc.isDefined)

    val op_x = SpecSignatures.Activity_onPause_entry.copy(lsVars = TopVal::NamedPureVar("b")::Nil)
    val tr = AbstractTrace(op_x::Nil)
    val retPause = iterPredUntil(Set(l), symbolicExecutor.controlFlowResolver, {
      case CallbackMethodReturn(sig, _, _) if sig.methodSignature.contains("onPause") => true
      case _ => false
    }, State.topState.copy(sf =
      State.topState.sf.copy(traceAbstraction = tr)), 20)
    assert(retPause.isDefined)
  }
  test("iterate to parameter assignments onCreate"){
    val a = NamedPureVar("a")

    val test_interproc_1: String = getClass.getResource("/test_interproc_2.apk").getPath()
    assert(test_interproc_1 != null)
    val w = new SootWrapper(test_interproc_1, Set())
    val testSpec = LSSpec(a::Nil, Nil, NS(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit),
      SpecSignatures.Activity_onPause_entry) // TODO: fill in spec details for test
    val config: ExecutorConfig[SootMethod, soot.Unit] = ExecutorConfig(
      stepLimit = 50, w, new SpecSpace(Set(testSpec)), printAAProgress = true, z3Timeout = Some(30))
    val symbolicExecutor = config.getAbstractInterpreter
    val query = Qry.makeReach(symbolicExecutor,
      Signature("com.example.test_interproc_2.MainActivity", "void onCreate(android.os.Bundle)"), 16)

    val l = query.find {
      case Qry(s, _,Live) if s.callStack.head.exitLoc.isInstanceOf[CallbackMethodReturn] => true
      case _ => false
    }.get.loc

    val entryloc = iterPredUntil(Set(l), symbolicExecutor.controlFlowResolver, {
      case _:CallbackMethodInvoke => true
      case l@AppLoc(_, _, false) =>
        val cmd = w.cmdAtLocation(l)
        false
      case l => false
    }, State.topState, 12)
    assert(entryloc.isDefined)
  }
}
