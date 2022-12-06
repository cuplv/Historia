package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.lifestate.LifeState.{LSAnyPred, LSSpec}
import edu.colorado.plv.bounder.lifestate.{SpecSignatures, SpecSpace}
import edu.colorado.plv.bounder.solver.Z3StateSolver
import edu.colorado.plv.bounder.symbolicexecutor.state.{MemoryOutputMode, NamedPureVar, TopVal}
import edu.colorado.plv.bounder.synthesis.SynthTestUtil.{cha, targetIze, toConcGraph, witTreeFromMsgList}
import org.scalatest.funsuite.AnyFunSuite

class EnumModelGeneratorTest extends AnyFunSuite {

  val a = NamedPureVar("a")
  val f = NamedPureVar("f")
  val l = NamedPureVar("l")
  val s = NamedPureVar("s")
  val t = NamedPureVar("t")
  val v = NamedPureVar("v")
  val a_onCreate = SpecSignatures.Activity_onCreate_entry
  val a_onDestroy = SpecSignatures.Activity_onDestroy_exit
  val s_a_subscribe = SpecSignatures.RxJava_subscribe_exit.copy(lsVars = s::TopVal::a::Nil)
  val s_unsubscribe = SpecSignatures.RxJava_unsubscribe_exit
  val t_create = SpecSignatures.RxJava_create_exit
  val a_call = SpecSignatures.RxJava_call_entry.copy(lsVars = TopVal::a::Nil)

  ignore("Encode Node Reachability motivating example - ConcGraph"){
    implicit val ord = new DummyOrd
    implicit val outputMode = MemoryOutputMode
    //TODO: may need to declare vars distinct
    val unreachSeq = toConcGraph(
      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, s_unsubscribe, a_call)))
    val reachSeq = toConcGraph(
      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, a_call)))
    val gen = new EnumModelGenerator()
    val spec = new SpecSpace(Set(
      LSSpec(a::Nil,Nil,  LSAnyPred , a_call)
    ), matcherSpace = Set())
    implicit val solver = new Z3StateSolver(cha)
    val res = gen.learnRulesFromConcGraph(Set(unreachSeq), Set(reachSeq), spec)
    ???



  }
  ignore("Encode Node Reachability motivating example - witTree"){
    implicit val ord = new DummyOrd
    implicit val outputMode = MemoryOutputMode
    //TODO: may need to declare vars distinct
    val unreachSeq = SynthTestUtil.witTreeFromMsgList(
      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, s_unsubscribe, a_call)))
    val reachSeq = witTreeFromMsgList(
      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, a_call)))
    val gen = new EnumModelGenerator()
    val spec = new SpecSpace(Set(
      LSSpec(a::Nil,Nil,  LSAnyPred , a_call)
    ), matcherSpace = Set())
    val res = gen.learnRulesFromExamples(unreachSeq, reachSeq, spec)
    ???



  }

}
