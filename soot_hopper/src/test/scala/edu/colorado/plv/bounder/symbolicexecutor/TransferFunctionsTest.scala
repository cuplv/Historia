package edu.colorado.plv.bounder.symbolicexecutor

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CBEnter, CBExit, CallbackMethodInvoke, CallbackMethodReturn, CmdWrapper, FieldRef, Loc, LocalWrapper, NewCommand, NullConst}
import edu.colorado.plv.bounder.lifestate.LifeState.{I, LSSpec}
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbsAnd, AbsArrow, AbsEq, AbsFormula, AbstractTrace, CallStackFrame, Equals, FieldPtEdge, NotEquals, NullVal, PureConstraint, PureVar, StackVar, State, TraceAbstractionArrow}
import edu.colorado.plv.bounder.testutils.{CmdTransition, MethodTransition, TestIR, TestIRLineLoc, TestIRMethodLoc}

class TransferFunctionsTest extends org.scalatest.FunSuite {
  def absContains(contained:AbstractTrace, result:TraceAbstractionArrow):Boolean = result match{
    case AbsArrow(result, _) => absContains(contained, result)
  }
  def absContains(contained:AbstractTrace, result:AbstractTrace):Boolean = result match{
    case r if r == contained => true
    case AbsAnd(l,r) => absContains(contained,l) || absContains(contained,r)
    case AbsEq(_,_) => false
    case AbsFormula(_) => false
    case _ => ???
  }
  def testCmdTransfer(cmd:AppLoc => CmdWrapper, post:State, testIRMethod: TestIRMethodLoc):Set[State] = {
    val preloc = AppLoc(testIRMethod,TestIRLineLoc(1), isPre=true)
    val postloc = AppLoc(testIRMethod,TestIRLineLoc(1), isPre=false)
    val ir = new TestIR(Set(CmdTransition(preloc, cmd(postloc), postloc)))
    val tr = new TransferFunctions(ir, new SpecSpace(Set()))
    tr.transfer(post,preloc, postloc)
  }
  //Test transfer function where field is assigned and base may or may not be aliased
  // pre: a^.out -> b1^
  // post: (a^.out -> c^* d^.out -> e^) OR (a^.out -> c^ AND a^=d^ AND c^=d^)
  val fooMethod = TestIRMethodLoc("","foo", List(LocalWrapper("@this","Object")))
  val fooMethodReturn = CallbackMethodReturn("", "foo", fooMethod, None)
  test("Transfer may or may not alias") {
    val cmd = (loc:AppLoc) => {
      val thisLocal = LocalWrapper("@this", "Object")
      AssignCmd(FieldRef(thisLocal, "Object", "Object", "o"), NullConst, loc)
    }
    val basePv = PureVar(State.getId())
    val otherPv = PureVar(State.getId())
    val post = State(CallStackFrame(fooMethodReturn, None, Map(StackVar("@this") -> basePv))::Nil,
      heapConstraints = Map(FieldPtEdge(otherPv, "o") -> NullVal),
      pureFormula = Set(),
      traceAbstraction = Set()
    )
    val pre = testCmdTransfer(cmd, post, fooMethod)
    println(s"pre: ${pre})")
    println(s"post: ${post}")
    assert(pre.size == 2)
    assert(1 == pre.count(state =>
      state.heapConstraints.size == 1
      && state.pureFormula.contains(PureConstraint(basePv,NotEquals, otherPv))))
    assert(pre.count(state => state.heapConstraints.isEmpty) == 1)
  }
  test("Transfer assign new local") {
    val cmd= (loc:AppLoc) => AssignCmd(LocalWrapper("bar","Object"),NewCommand("String"),loc)
    val nullPv = PureVar(State.getId())
    val post = State(
      CallStackFrame(fooMethodReturn, None, Map(StackVar("bar") -> nullPv))::Nil,
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
    val nullPv = PureVar(State.getId())
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
    val preloc = CallbackMethodInvoke("","foo", fooMethod) // Transition to just before foo is invoked
    val postloc = AppLoc(fooMethod,TestIRLineLoc(1), isPre=true)
    val ir = new TestIR(Set(MethodTransition(preloc, postloc)))
    val lhs = I(CBEnter, Set(("", "bar")), "_" :: "a" :: Nil)
    //  I(cb a.bar()) <= I(cb a.foo())
    val spec = LSSpec(
      lhs,
      iFooA)
    val tr = new TransferFunctions(ir, new SpecSpace(Set(spec)))
    val recPv = PureVar(State.getId())
    val otheri = AbsFormula(I(CBExit, Set(("a","a")), "b"::Nil))
    val post = State(
      CallStackFrame(CallbackMethodReturn("","foo",fooMethod, None), None, Map(StackVar("@this") -> recPv))::Nil,
      heapConstraints = Map(),
      pureFormula = Set(),
      traceAbstraction = Set(AbsArrow(otheri,Nil)))

    println(s"post: ${post.toString}")
    println(s"preloc: ${preloc}")
    println(s"postloc: ${postloc}")
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
    val preloc = CallbackMethodInvoke("","foo", fooMethod) // Transition to just before foo is invoked
    val postloc = AppLoc(fooMethod,TestIRLineLoc(1), isPre=true)
    val ir = new TestIR(Set(MethodTransition(preloc, postloc)))
    val tr = new TransferFunctions(ir, new SpecSpace(Set(LSSpec(iFooA,iFooA.copy(signatures = Set(("bbb","bbb")))))))
    val recPv = PureVar(State.getId())
    val post = State(
      CallStackFrame(CallbackMethodReturn("","foo",fooMethod, None), None, Map(StackVar("@this") -> recPv))::Nil,
      heapConstraints = Map(),
      pureFormula = Set(),
      traceAbstraction = Set(AbsArrow(AbsAnd(AbsFormula(iFooA), AbsEq("a",recPv)), Nil)))
    println(s"post: ${post.toString}")
    val prestate: Set[State] = tr.transfer(post,preloc, postloc)
    println(s"pre: ${prestate.toString}")
    val formula = prestate.head.traceAbstraction
    assert(formula.exists(p => absContains(AbsEq("a",recPv),p)))
    //TODO: Simplification does not yet discharge in this case, should it?
  }
}
