package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.ir.{CBEnter, CallbackMethodInvoke, LocalWrapper}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSPred, NI, PredicateSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallStackFrame, PureVar, SomeQry, StackVar, State}
import edu.colorado.plv.bounder.testutils.TestIRMethodLoc

class Z3ModelGeneratorTest extends org.scalatest.FunSuite {

  val fooMethod = TestIRMethodLoc("","foo", List(LocalWrapper("@this","Object")))
  test("Encode Node Reachability"){
    val gen = new Z3ModelGenerator()
    val dummyLoc = CallbackMethodInvoke(fmwClazz = "",
      fmwName="void foo()", fooMethod)
    val pureVar = PureVar(State.getId())
    val frame = CallStackFrame(dummyLoc, None, Map(StackVar("this") -> pureVar))
    val state = State(List(frame), Map(), Set(), Set())
    val qryR1 = SomeQry(state, dummyLoc)

    val barPred = I(CBEnter,Set(("","void bar()")), List("a"))
    val fooPred = I(CBEnter,Set(("","void foo()")), List("a"))
    val pred = barPred

    val theta = Map(
      "a" -> pureVar
    )
    val predSpace = new PredicateSpace(Set(fooPred, barPred))
    gen.encodeNodeReachability(qryR1, pred, theta, predSpace)

  }
}
