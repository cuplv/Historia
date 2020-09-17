package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.ir.CallbackMethodInvoke
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState.{AND, I, LSPred, NI, PredicateSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{PureVar, Qry, ReachingGraph, SomeQry, State, ThisPtEdge}
import edu.colorado.plv.bounder.testutils.{TestIRMethodLoc}

class Z3ModelGeneratorTest extends org.scalatest.FunSuite {
  //test("Synthesize a simple model from example traces.") {
  //  val posTrace = List(
  //    TraceMessage("Cb Enter onPause", 3,true),
  //    TraceMessage("Cb Exit onResume", 3, false),
  //    TraceMessage("CB Enter onResume",3,true),
  //    TraceMessage("xmlreg",3,false)
  //  )

  //  val gen = new Z3ModelGenerator()
  //  val res = gen.learnRulesFromExamples(Set(posTrace),
  //    Set(), List(TraceMessage("Cb Enter onPause", 3,true)))
  //}
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
    val state = State(List(), Map(ThisPtEdge() -> pureVar), Set(), Set())
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
