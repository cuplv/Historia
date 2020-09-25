package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.ir.CallbackMethodInvoke
import edu.colorado.plv.bounder.lifestate.LifeState.{AND, I, LSPred, NI, PredicateSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallStackFrame, PureVar, SomeQry, StackVar, State}
import edu.colorado.plv.bounder.testutils.TestIRMethodLoc

class Z3ModelGeneratorTest extends org.scalatest.FunSuite {
  test("Simple"){
    //TODO: Delete this later, just a place to experiment with z3
    val gen = new Z3ModelGenerator()
    gen.testSimple()
  }

  test("Encode Node Reachability"){
    val gen = new Z3ModelGenerator()
    val dummyLoc = CallbackMethodInvoke(fmwClazz = "",
      fmwName="void foo()", TestIRMethodLoc("foo"))
    val pureVar = PureVar()
    val frame = CallStackFrame(dummyLoc, None, Map(StackVar("this", "MainActivity") -> pureVar))
    val state = State(List(), Map(), Set(), Set())
    val qryR1 = SomeQry(state, dummyLoc)

    val barPred = I(Set("[CB Inv] void bar()"), List("a"))
    val fooPred = I(Set("[CB Inv] void foo()"), List("a"))
    val pred = barPred

    val theta = Map(
      "a" -> pureVar
    )
    val predSpace = new PredicateSpace(Set(fooPred, barPred))
    gen.encodeNodeReachability(qryR1, pred, theta, predSpace)

  }
}
