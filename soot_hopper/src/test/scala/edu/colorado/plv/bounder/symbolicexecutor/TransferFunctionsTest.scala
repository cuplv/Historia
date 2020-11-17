package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CBEnter, CallbackMethodInvoke, CallbackMethodReturn, LocalWrapper, NewCommand}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSAbsBind, LSFalse, LSPred, LSSpec, LSTrue, NI, Not, Or}
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.symbolicexecutor.state.{CallStackFrame, Equals, NotEquals, NullVal, PureConstraint, PureVar, StackVar, State, TraceAbstraction}
import edu.colorado.plv.bounder.testutils.{CmdTransition, MethodTransition, TestIR, TestIRLineLoc, TestIRMethodLoc}

class TransferFunctionsTest extends org.scalatest.FunSuite {
  test("Transfer assign local") {
    val fooMethod = TestIRMethodLoc("foo")
    val preloc = AppLoc(fooMethod,TestIRLineLoc(1), isPre=true)
    val postloc = AppLoc(fooMethod,TestIRLineLoc(1), isPre=false)
    val cmd = AssignCmd(LocalWrapper("bar",""),NewCommand(""),postloc)
    val ir = new TestIR(Set(CmdTransition(preloc, cmd, postloc)))
    val tr = new TransferFunctions(ir, new SpecSpace(Set()))
    val nullPv = PureVar()
    val post = State(
      CallStackFrame(CallbackMethodReturn("","foo",fooMethod, None), None, Map(StackVar("bar") -> nullPv))::Nil,
      heapConstraints = Map(),
      pureFormula = Set(PureConstraint(nullPv,Equals, NullVal)), Set())
    val prestate: Set[State] = tr.transfer(post,preloc, postloc)
    assert(prestate.size == 1)
    val formula = prestate.head.pureFormula
    assert(formula.contains(PureConstraint(nullPv,Equals, NullVal)))
    assert(formula.contains(PureConstraint(nullPv,NotEquals, NullVal)))
  }
  test("Add matcher and phi abstraction when crossing callback entry") {
    val fooMethod = TestIRMethodLoc("foo")
    val preloc = CallbackMethodInvoke("","foo", fooMethod) // Transition to just before foo is invoked
    val postloc = AppLoc(fooMethod,TestIRLineLoc(1), isPre=true)
    val ir = new TestIR(Set(MethodTransition(preloc, postloc)))
    val spec = LSSpec( //  I(cb a.bar()) <= I(cb a.foo())
      I(CBEnter, Set(("","bar")),"_"::"a"::Nil),
      I(CBEnter, Set(("","foo")),"_"::"a"::Nil))
    val tr = new TransferFunctions(ir, new SpecSpace(Set(spec)))
    val recPv = PureVar()
    val post = State(
      CallStackFrame(CallbackMethodReturn("","foo",fooMethod, None), None, Map(StackVar("this") -> recPv))::Nil,
      heapConstraints = Map(),
      pureFormula = Set(),
      traceAbstraction = Set())
    println(s"post: ${post.toString}")
    val prestate: Set[State] = tr.transfer(post,preloc, postloc)
    println(s"pre: ${prestate.toString}")
    assert(prestate.size == 1)
    val formula = prestate.head.traceAbstraction
    //assert(formula.contains(LSAbstraction(I(CBEnter, Set(("","bar")), "_"::"a"::Nil), Map("a"->recPv))))

    val stack = prestate.head.callStack
    assert(stack.size == 0)
  }
  test("Discharge I(m1^) phi abstraction when post state must generate m1^ for previous transition") {
    val fooMethod = TestIRMethodLoc("foo")
    val preloc = CallbackMethodInvoke("","foo", fooMethod) // Transition to just before foo is invoked
    val postloc = AppLoc(fooMethod,TestIRLineLoc(1), isPre=true)
    val ir = new TestIR(Set(MethodTransition(preloc, postloc)))
    val tr = new TransferFunctions(ir, new SpecSpace(Set()))
    val recPv = PureVar()
    ???
    //val post = State(
    //  CallStackFrame(CallbackMethodReturn("","foo",fooMethod, None), None, Map(StackVar("this") -> recPv))::Nil,
    //  heapConstraints = Map(),
    //  pureFormula = Set(),
    //  traceAbstraction = Set(LSAbstraction(I(CBEnter, Set(("","foo")), "_"::"a"::Nil), Map("a"->recPv))))
    //println(s"post: ${post.toString}")
    //val prestate: Set[State] = tr.transfer(post,preloc, postloc)
    //println(s"post: ${prestate.toString}")
    //assert(prestate.size == 1)
    //val formula = prestate.head.traceAbstraction
    ////TODO: find better way to inspect abstract test results
    //assert(formula.size == 1)
    //assert(formula.head.isInstanceOf[LSAbstraction])
    //assert(formula.head.asInstanceOf[LSAbstraction].pred.isInstanceOf[Or])
  }
}
