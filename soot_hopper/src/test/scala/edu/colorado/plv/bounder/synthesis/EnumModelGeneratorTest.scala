package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.lifestate.LifeState.{Exists, LSSpec, NS, UComb}
import edu.colorado.plv.bounder.lifestate.{SpecSignatures, SpecSpace}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{MemoryOutputMode, NamedPureVar, TopVal}
import edu.colorado.plv.bounder.synthesis.SynthTestUtil.{hierarchy, intToClass, targetIze, witTreeFromMsgList}
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

  test("Encode Node Reachability motivating example"){
    implicit val ord = new DummyOrd
    implicit val outputMode = MemoryOutputMode
    //TODO: may need to declare vars distinct
    val unreachSeq = SynthTestUtil.witTreeFromMsgList(
      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, s_unsubscribe, a_call)))
    val reachSeq = witTreeFromMsgList(
      targetIze(List(a_onCreate, t_create, s_a_subscribe,a_onDestroy, a_call)))
    val cha = new ClassHierarchyConstraints(hierarchy,Set("java.lang.Runnable"),intToClass)
    val gen = new Z3ModelGenerator(cha)
    val spec = new SpecSpace(Set(
      LSSpec(a::Nil,Nil,  UComb("call", a_onDestroy::Exists(s::l::Nil,NS(s_a_subscribe, s_unsubscribe))::Nil) , a_call)
    ))
    val res = gen.learnRulesFromExamples(unreachSeq, reachSeq, spec)
    ???



  }

}
