package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.ir.{CBEnter, CallbackMethodInvoke, LocalWrapper, TestIRMethodLoc}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, LSPred, NS, Once, PredicateSpace, SetSignatureMatcher, SignatureMatcher}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, CallStackFrame, NamedPureVar, PureVar, Qry, StackVar, State, StateFormula}
import org.scalatest.funsuite.AnyFunSuite

class Z3ModelGeneratorTest extends AnyFunSuite {

  implicit def set2SigMat(s:Set[(String,String)]):SignatureMatcher = SetSignatureMatcher(s)
  val fooMethod = TestIRMethodLoc("","foo", List(Some(LocalWrapper("@this","Object"))))
  test("Encode Node Reachability"){
    // TODO: implement model generator
    val a = NamedPureVar("a")
    val gen = new Z3ModelGenerator(???)
    val dummyLoc = CallbackMethodInvoke(tgtClazz = "",
      fmwName="void foo()", fooMethod)
    val pureVar = PureVar(1)
    val frame = CallStackFrame(dummyLoc, None, Map(StackVar("this") -> pureVar))
    val state = State(StateFormula(List(frame), Map(), Set(),Map(),AbstractTrace(Nil)),0)
    val qryR1 = Qry(state, dummyLoc, ???)

    val barPred = Once(CBEnter,Set(("","void bar()")), List(a))
    val fooPred = Once(CBEnter,Set(("","void foo()")), List(a))
    val pred = barPred

    val theta = Map(
      "a" -> pureVar
    )
    val predSpace = new PredicateSpace(Set(fooPred, barPred))
    ???

  }
}
