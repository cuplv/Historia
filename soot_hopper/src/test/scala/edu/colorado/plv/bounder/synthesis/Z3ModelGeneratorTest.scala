package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.ir.{CBEnter, CallbackMethodInvoke, LocalWrapper, TestIRMethodLoc}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSPred, NI, PredicateSpace, SetSignatureMatcher, SignatureMatcher}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, CallStackFrame, LiveQry, PureVar, StackVar, State, StateFormula}
import org.scalatest.funsuite.AnyFunSuite

class Z3ModelGeneratorTest extends AnyFunSuite {

  implicit def set2SigMat(s:Set[(String,String)]):SignatureMatcher = SetSignatureMatcher(s)
  val fooMethod = TestIRMethodLoc("","foo", List(Some(LocalWrapper("@this","Object"))))
  ignore("Encode Node Reachability"){
    // TODO: implement model generator
    val gen = new Z3ModelGenerator()
    val dummyLoc = CallbackMethodInvoke(tgtClazz = "",
      fmwName="void foo()", fooMethod)
    val pureVar = PureVar(1)
    val frame = CallStackFrame(dummyLoc, None, Map(StackVar("this") -> pureVar))
    val state = State(StateFormula(List(frame), Map(), Set(),Map(),AbstractTrace(Nil, Map())),0)
    val qryR1 = LiveQry(state, dummyLoc)

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
