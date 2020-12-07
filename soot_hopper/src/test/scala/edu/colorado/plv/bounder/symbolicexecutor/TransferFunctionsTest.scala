package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CBEnter, CBExit, CallbackMethodInvoke, CallbackMethodReturn, CmdWrapper, Loc, LocalWrapper, NewCommand}
import edu.colorado.plv.bounder.lifestate.LifeState.{I, LSSpec}
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbsAnd, AbsArrow, AbsEq, AbsFormula, CallStackFrame, Equals, NotEquals, NullVal, PureConstraint, PureVar, StackVar, State, TraceAbstraction}
import edu.colorado.plv.bounder.testutils.{CmdTransition, MethodTransition, TestIR, TestIRLineLoc, TestIRMethodLoc}

class TransferFunctionsTest extends org.scalatest.FunSuite {
  def absContains(contained:TraceAbstraction, result:TraceAbstraction):Boolean = result match{
    case r if r == contained => true
    case AbsAnd(l,r) => absContains(contained,l) || absContains(contained,r)
    case AbsEq(_,_) => false
    case AbsFormula(_) => false
    case AbsArrow(p,_) => absContains(contained,p)
    case _ => ???
  }
  def testCmdTransfer(cmd:AppLoc => CmdWrapper, post:State, testIRMethod: TestIRMethodLoc):Set[State] = {
    val preloc = AppLoc(testIRMethod,TestIRLineLoc(1), isPre=true)
    val postloc = AppLoc(testIRMethod,TestIRLineLoc(1), isPre=false)
    val ir = new TestIR(Set(CmdTransition(preloc, cmd(postloc), postloc)))
    val tr = new TransferFunctions(ir, new SpecSpace(Set()))
    tr.transfer(post,preloc, postloc)
  }
  //TODO: test transfer function where field is assigned and base may or may not be aliased, when does this happen?
  // pre: a^.out -> b1^
  // post: (a^.out -> c^* d^.out -> e^) OR (a^.out -> c^ AND a^=d^ AND c^=d^)
  test("Transfer assign new local") {
    val cmd= (loc:AppLoc) => AssignCmd(LocalWrapper("bar","Object"),NewCommand("String"),loc)
    val fooMethod = TestIRMethodLoc("","foo")
    val nullPv = PureVar()
    val post = State(
      CallStackFrame(CallbackMethodReturn("","foo",fooMethod, None), None, Map(StackVar("bar") -> nullPv))::Nil,
      heapConstraints = Map(),
      pureFormula = Set(PureConstraint(nullPv,Equals, NullVal)), Set())
    val prestate: Set[State] = testCmdTransfer(cmd, post,fooMethod)
    println(s"poststate: $post")
    println(s"prestate: ${prestate}")
    assert(prestate.size == 1)
    val formula = prestate.head.pureFormula
    assert(formula.contains(PureConstraint(nullPv,Equals, NullVal)))
    assert(formula.contains(PureConstraint(nullPv,NotEquals, NullVal)))
  }
  test("Transfer assign local local") {
    val cmd= (loc:AppLoc) => AssignCmd(LocalWrapper("bar","Object"),LocalWrapper("baz","String"),loc)
    val fooMethod = TestIRMethodLoc("","foo")
    val nullPv = PureVar()
    val post = State(
      CallStackFrame(CallbackMethodReturn("","foo",fooMethod, None), None, Map(StackVar("bar") -> nullPv))::Nil,
      heapConstraints = Map(),
      pureFormula = Set(PureConstraint(nullPv,Equals, NullVal)), Set())
    val prestate: Set[State] = testCmdTransfer(cmd, post,fooMethod)
    println(s"poststate: $post")
    println(s"prestate: ${prestate}")
    assert(prestate.size == 1)
    val formula = prestate.head.pureFormula
    assert(formula.contains(PureConstraint(nullPv,Equals, NullVal)))
    assert(prestate.head.callStack.head.locals.contains(StackVar("baz")))
    assert(!prestate.head.callStack.head.locals.contains(StackVar("bar")))
  }
  private val iFooA: I = I(CBEnter, Set(("", "foo")), "_" :: "a" :: Nil)
  test("Add matcher and phi abstraction when crossing callback entry") {
    val fooMethod = TestIRMethodLoc("","foo")
    val preloc = CallbackMethodInvoke("","foo", fooMethod) // Transition to just before foo is invoked
    val postloc = AppLoc(fooMethod,TestIRLineLoc(1), isPre=true)
    val ir = new TestIR(Set(MethodTransition(preloc, postloc)))
    val lhs = I(CBEnter, Set(("", "bar")), "_" :: "a" :: Nil)
    //  I(cb a.bar()) <= I(cb a.foo())
    val spec = LSSpec(
      lhs,
      iFooA)
    val tr = new TransferFunctions(ir, new SpecSpace(Set(spec)))
    val recPv = PureVar()
    val otheri = AbsFormula(I(CBExit, Set(("a","a")), "b"::Nil))
    val post = State(
      CallStackFrame(CallbackMethodReturn("","foo",fooMethod, None), None, Map(StackVar("this") -> recPv))::Nil,
      heapConstraints = Map(),
      pureFormula = Set(),
      traceAbstraction = Set(otheri))
    println(s"post: ${post.toString}")
    val prestate: Set[State] = tr.transfer(post,preloc, postloc)
    println(s"pre: ${prestate.toString}")
    assert(prestate.size == 1)
    val formula = prestate.head.traceAbstraction
    assert(formula.exists(p => absContains(AbsEq("a",recPv),p)))
    assert(formula.exists(p => absContains(AbsFormula(lhs),p)))
    assert(formula.exists(p => absContains(otheri, p)))

    val stack = prestate.head.callStack
    assert(stack.isEmpty)
  }
  test("Discharge I(m1^) phi abstraction when post state must generate m1^ for previous transition") {
    val fooMethod = TestIRMethodLoc("","foo")
    val preloc = CallbackMethodInvoke("","foo", fooMethod) // Transition to just before foo is invoked
    val postloc = AppLoc(fooMethod,TestIRLineLoc(1), isPre=true)
    val ir = new TestIR(Set(MethodTransition(preloc, postloc)))
    val tr = new TransferFunctions(ir, new SpecSpace(Set(LSSpec(iFooA,iFooA.copy(signatures = Set(("bbb","bbb")))))))
    val recPv = PureVar()
    val post = State(
      CallStackFrame(CallbackMethodReturn("","foo",fooMethod, None), None, Map(StackVar("this") -> recPv))::Nil,
      heapConstraints = Map(),
      pureFormula = Set(),
      traceAbstraction = Set(AbsAnd(AbsFormula(iFooA), AbsEq("a",recPv))))
    println(s"post: ${post.toString}")
    val prestate: Set[State] = tr.transfer(post,preloc, postloc)
    println(s"pre: ${prestate.toString}")
    val formula = prestate.head.traceAbstraction
    assert(formula.exists(p => absContains(AbsEq("a",recPv),p)))
    //TODO: Simplification does not yet discharge in this case, should it?
  }
}
