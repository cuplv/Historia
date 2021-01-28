package edu.colorado.plv.bounder.solver

import com.microsoft.z3._
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.{I, NI, Not, Or}
import edu.colorado.plv.bounder.symbolicexecutor.state._
import edu.colorado.plv.bounder.testutils.{TestIRLineLoc, TestIRMethodLoc}
import org.scalatest.funsuite.AnyFunSuite

class Z3StateSolverTest extends AnyFunSuite {
  val fooMethod = TestIRMethodLoc("","foo", List(LocalWrapper("@this","Object")))
  val dummyLoc = CallbackMethodInvoke(fmwClazz = "",
    fmwName="void foo()", fooMethod)
  val v = PureVar(State.getId())
  val frame = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> v))
  val state = State.topState
  test("null not null") {
  val statesolver = getStateSolver

    val v2 = PureVar(State.getId())
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal), PureConstraint(v2, Equals, NullVal))
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints,Set(),0)
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)
  }
  test("alias") {
  val statesolver = getStateSolver

    val v2 = PureVar(State.getId())
    val v3 = PureVar(State.getId())
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal),
      PureConstraint(v3, Equals, NullVal))
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints + PureConstraint(v2, Equals, v3),Set(),0)
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)
  }
  test("Separate fields imply base must not be aliased a^.f->b^ * c^.f->b^ AND a^=c^ (<=> false)") {
  val statesolver = getStateSolver

    val v2 = PureVar(State.getId())
    val v3 = PureVar(State.getId())
    val v4 = PureVar(State.getId())
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v, Equals, v2)), Set(),0)
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)

    // v3 and v4 on the right side of the points to can be aliased
    val unrefutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4)), Set(),0)
    val simplifyResult2 = statesolver.simplify(unrefutableState)
    assert(simplifyResult2.isDefined)
  }
  //TODO: group equal pure vars for type check
  test("aliased object implies fields must be aliased refuted by type constraints") {
    val statesolver = getStateSolver

    // aliased and contradictory types of field
    val v2 = PureVar(State.getId())
    val v3 = PureVar(State.getId())
    val v4 = PureVar(State.getId())
    val constraints = Set(
      PureConstraint(v3, Equals, v4),
      PureConstraint(v3, TypeComp, SubclassOf("String")),
      PureConstraint(v4, TypeComp, SubclassOf("Foo"))
    )
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3),constraints, Set(),0)
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)

    // aliased and consistent field type constraints
    val constraints2 = Set(
      PureConstraint(v3, Equals, v4),
      PureConstraint(v3, TypeComp, SubclassOf("String")),
      PureConstraint(v4, TypeComp, SubclassOf("java.lang.Object"))
    )
    val state = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),constraints2, Set(),0)
    val simplifyResult2 = statesolver.simplify(state)
    assert(simplifyResult2.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) && a == p1 (<==>true)") {
    val statesolver = getStateSolver

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val niBarBaz = NI(i,i2)
    val p1 = PureVar(State.getId())
    val abs1 = AbstractTrace(niBarBaz, Nil, Map("a"->p1))
    val state1 = State(Nil, Map(),Set(), Set(abs1),0)
    val res1 = statesolver.simplify(state1)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) |> I(a.bar()) (<==>true)") {
    val statesolver = getStateSolver

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val niBarBaz = NI(i,i2)
//    val abs1 = AbsArrow(AbsFormula(niBarBaz), i::Nil)
    val abs1 = AbstractTrace(niBarBaz, i::Nil, Map())
    val state1 = State(Nil, Map(),Set(), Set(abs1),0)
    val res1 = statesolver.simplify(state1)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)") {
    val statesolver = getStateSolver

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i,i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId())
    val p2 = PureVar(State.getId())

    // NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)
    val abs1 = AbstractTrace(niBarBaz,i3::Nil, Map("a"->p1, "b"->p1))
//    AbsAnd(AbsAnd(AbsFormula(niBarBaz), AbsEq("a",p1)), AbsEq("b",p1)),
    val state1 = State(Nil, Map(),Set(), Set(abs1),0)
    println(s"state: ${state1}")
    val res1 = statesolver.simplify(state1, Some(20)) //TODO: remove limit
    assert(!res1.isDefined)

    //TODO: more tests
    // [NI(m1^,m2^) OR (NOT NI(m1^,m2^)) ] AND (a |->a^) => TRUE
    val pred2 = Or(NI(i,i2),Not(NI(i,i2)))
    //val state2 = State(Nil, Map(),Set(), Set(LSAbstraction(pred2, Map("a"-> p1))))
    //val res2 = statesolver.simplify(state2)
    //assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) && a == p1 && c == p1 (<=> true)") {
    val stateSolver = getStateSolver

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId())
    val p2 = PureVar(State.getId())

    // NI(a.bar(),a.baz()) |> I(c.bar()) && a == p1 && c == p1 (<=> true)
    val abs2 = AbstractTrace(niBarBaz,i4::Nil, Map("a"->p1, "c"->p1) )
    val state2 = State(Nil,Map(),Set(), Set(abs2),0)
    val res2 = stateSolver.simplify(state2)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(b.baz()) |> I(c.bar()) (<=> true) ") {
    val statesolver = getStateSolver

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId())

    // NI(a.bar(),a.baz()) |> I(c.bar()) ; i(b.baz()
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1, "c"->p1))
    val state2 = State(Nil,Map(),Set(), Set(niaa),0)
    val res2 = statesolver.simplify(state2, Some(20)) //TODO: remove dbg limit
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) ; I(c.bar()) ; I(b.baz()) && a = b = c (<=> false) ") {
    val statesolver = getStateSolver

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId())

    // NI(a.bar(),a.baz()) |> I(a.bar());I(a.baz())
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1, "c"->p1, "b"->p1))
    val state2 = State(Nil,Map(),Set(), Set(niaa),0)
    val res2 = statesolver.simplify(state2, Some(20))
    assert(res2.isEmpty)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = c (<=> true) ") {
    val statesolver = getStateSolver

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId())
    val p2 = PureVar(State.getId())

    // NI(a.bar(),a.baz()) |> I(c.bar()) ; I(b.baz())
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1, "c"->p1, "b"->p2))
    val state2 = State(Nil,Map(),Set(), Set(niaa),0)
    val res2 = statesolver.simplify(state2)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = b (<=> false) ") {
    val statesolver = getStateSolver

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId())
    val p2 = PureVar(State.getId())

    // NI(a.bar(),a.baz()) |> I(c.bar()) |> i(b.baz()
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1,"b"->p1, "c"->p2))
    val state2 = State(Nil,Map(),Set(), Set(niaa),0)
    val res2 = statesolver.simplify(state2)
    assert(res2.isEmpty)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(a.bar()),  NI(a.foo(),a.baz()) |> I(a.foo()) (<=> true) ") {
    val statesolver = getStateSolver

    // Lifestate atoms for next few tests
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibaz = I(CBEnter, Set(("", "baz")), "a" :: Nil)
    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val t1 = AbstractTrace(NI(ibar,ibaz), ibar::Nil, Map())
    val t2 = AbstractTrace(NI(ifoo,ibaz), ifoo::Nil, Map())
    val s = state.copy(traceAbstraction = Set(t1,t2))
    val res = statesolver.simplify(s, Some(20))
    assert(res.isDefined)
  }
  test("Vacuous NI(a,a) spec") {
    val statesolver = getStateSolver

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "b" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBar = NI(i, i)

    // pure vars for next few tests
    val p1 = PureVar(State.getId())
    val p2 = PureVar(State.getId())
    //NI(a.bar(),a.bar()) (<=> true)
    // Note that this should be the same as I(a.bar())
    val nia = AbstractTrace(niBarBar, Nil, Map())
    val res0 = statesolver.simplify(state.copy(traceAbstraction = Set(nia)))
    assert(res0.isDefined)

    //NI(a.bar(),a.bar()) |> I(b.bar()) && a = b (<=> true)
    val niaa = AbstractTrace(niBarBar, i4::Nil, Map("a"->p1,"b"->p1))
    val res1 = statesolver.simplify(state.copy(traceAbstraction = Set(niaa)))
    assert(res1.isDefined)
  }
  test("Subsumption of stack"){
    val statesolver = getStateSolver

    val p1 = PureVar(State.getId())
    val p2 = PureVar(State.getId())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val state = State(CallStackFrame(loc,None,Map(StackVar("x") -> p1))::Nil, Map(),Set(),Set(),0)
    val state_ = state.copy(callStack = CallStackFrame(loc, None, Map(
      StackVar("x") -> p1,
      StackVar("y") -> p2
    ))::Nil)
    assert(statesolver.canSubsume(state,state_))
    assert(!statesolver.canSubsume(state_,state))

  }
  test("Subsumption of abstract traces") {
    val statesolver = getStateSolver

    val p1 = PureVar(State.getId())
    val p2 = PureVar(State.getId())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val state = State(CallStackFrame(loc,None,Map(StackVar("x") -> p1))::Nil, Map(),Set(),Set(),0)
    val state2 = state.copy(callStack =
      state.callStack.head.copy(locals=Map(StackVar("x") -> p1, StackVar("y")->p2))::Nil)
    assert(statesolver.canSubsume(state,state))
    assert(statesolver.canSubsume(state,state2))
    assert(!statesolver.canSubsume(state2,state))

    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibarc = I(CBEnter, Set(("", "bar")), "c" :: Nil)
    val ifooc = I(CBEnter, Set(("", "foo")), "c" :: Nil)

    val baseTrace1 = AbstractTrace(ifoo, Nil, Map("a"->p1))
    val arrowTrace1 = AbstractTrace(ifoo, ibarc::Nil, Map("a"->p1))
    val state_ = state.copy(traceAbstraction = Set(baseTrace1))
    val state__ = state.copy(traceAbstraction = Set(arrowTrace1))

    // State I(a.foo())|>empty should subsume itself

    assert(statesolver.canSubsume(state_,state_))
    // I(a.foo()) can subsume I(a.foo()) |> a.bar()
    assert(statesolver.canSubsume(state_,state__, Some(5)))

    val baseTrace = AbstractTrace(NI(ifoo,ibar), Nil, Map("a"->p1))
    val state3_ = state.copy(traceAbstraction = Set(baseTrace))

    // NI(a.foo(), a.bar()) can subsume itself
    val res = statesolver.canSubsume(state3_, state3_)
    assert(res)

    val state3__ = state.copy(traceAbstraction =
      Set(AbstractTrace(NI(ifoo,ibar), ibarc::Nil, Map("a"->p1))))
    // NI(a.foo(), a.bar()) can subsume NI(a.foo(), a.bar()) |> c.bar()
    assert(statesolver.canSubsume(state3_,state3__))

    // NI(a.foo(), a.bar()) cannot subsume NI(a.foo(), a.bar()) |> c.foo() /\ a==c
    // ifooc::Nil
    val fooBarArrowFoo = state.copy(
      traceAbstraction = Set(AbstractTrace(NI(ifoo,ibar), ifooc::Nil, Map("a"->p1, "c"->p1))))
    val resfoobarfoo = statesolver.canSubsume(state3_, fooBarArrowFoo)
    assert(!resfoobarfoo)

    // NI(a.foo(), a.bar()), I(a.foo()) should be subsumed by NI(a.foo(), a.bar())
    val s_foo_bar_foo = state.copy(traceAbstraction =
      Set(AbstractTrace(NI(ifoo,ibar), Nil, Map("a"->p1, "c"->p1)),
        AbstractTrace(ifooc,Nil, Map())))
    val s_foo_bar = state.copy(traceAbstraction = Set(AbstractTrace(NI(ifoo,ibar), Nil, Map("a"->p1))))
    assert(statesolver.canSubsume(s_foo_bar, s_foo_bar_foo))

    // Extra trace constraint prevents subsumption
    val res2 = statesolver.canSubsume(s_foo_bar_foo, s_foo_bar,Some(10))
    assert(!res2)

  }
  test("Refute trace with multi arg and multi var (bad arg fun skolemization caused bug here)") {
    val statesolver = getStateSolver

    val p1 = PureVar(State.getId())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val ifoo = I(CBEnter, Set(("", "foo")),  "_"::"a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")),  "_"::"a" :: Nil)
    val ibarc = I(CBEnter, Set(("", "bar")), "_"::"c" :: Nil)

    val at = AbstractTrace(NI(ifoo,ibar), ibarc::Nil, Map("a"->p1, "c"->p1))
    val state = State(CallStackFrame(loc, None, Map(StackVar("x") -> p1)) :: Nil, Map(), Set(), Set(at), 0)
    val res = statesolver.simplify(state, Some(8))
    assert(res.isEmpty)
  }
  test("Subsumption of pure formula in states"){
    val statesolver = getStateSolver

    val p1 = PureVar(State.getId())
    val p2 = PureVar(State.getId())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val state = State(CallStackFrame(loc,None,Map(StackVar("x") -> p1))::Nil, Map(),Set(),Set(),0)

    val state_ = state.copy(pureFormula = Set(PureConstraint(p1,TypeComp,SubclassOf("Foo")  )))
    val state__ = state.copy(pureFormula = Set(PureConstraint(p1,TypeComp,SubclassOf("java.lang.Object"))))
    // (x->p1 && p1 <: Foo) can be subsumed by (x->p1 && p1 <:Object)
    assert(statesolver.canSubsume(state__, state_))
    assert(statesolver.canSubsume(state_, state_))

    // (x->p1 && p1 <: Object) can not be subsumed by (x->p1 && p1 <:Foo)
    assert(!statesolver.canSubsume(state_, state__))

    // (x->p1 &&  p1 <: Foo && p1 == p2) can be subsumed by (x->p1 &&  p2 <: Object && p1 == p2)
    val state1_ = state.copy(pureFormula = Set(
      PureConstraint(p1, TypeComp, SubclassOf("Foo")),
      PureConstraint(p1, Equals, p2)
    ))
    val state1__ = state.copy(pureFormula = Set(
      PureConstraint(p2, TypeComp, SubclassOf("java.lang.Object")),
      PureConstraint(p1, Equals, p2)
    ))
    assert(statesolver.canSubsume(state1__, state1_))
    assert(!statesolver.canSubsume(state1_, state1__))

    // Combine type constraints and trace constraints
    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val formula = AbstractTrace(NI(ifoo,ibar),Nil, Map("a"->p1))
    val state2_ = state_.copy(traceAbstraction = Set(formula))
    val state2__ = state__.copy(traceAbstraction = Set(formula))
    assert(statesolver.canSubsume(state2__, state2_, Some(20)))
    assert(!statesolver.canSubsume(state2_, state2__, Some(20)))

    // x->p1 * y->p2 can be subsumed by x->p1
    val state_x_y = state.copy(
      callStack = CallStackFrame(loc,None,Map(
        StackVar("x") -> p1,
        StackVar("y") -> p2
      ))::Nil,
      pureFormula = Set(PureConstraint(p1, NotEquals, p2))
    )
    assert(statesolver.canSubsume(state,state_x_y))
    assert(!statesolver.canSubsume(state_x_y,state))

  }

  test("Trace contained in abstraction") {
    val statesolver = getStateSolver

    val foo = FwkMethod("foo", "")
    val bar = FwkMethod("bar", "")
    val baz = FwkMethod("baz", "")

    val i_foo_x = I(CIEnter, Set(("foo",""),("foo2","")), "X"::Nil)
    val i_bar_x = I(CIEnter, Set(("bar",""),("bar2","")), "X"::Nil)
    val trace = List(
      TMessage(CIEnter, foo, TAddr(1)::Nil),
      TMessage(CIEnter, bar, TAddr(1)::Nil)
    )

    val ni_foo_x_bar_x = NI(i_foo_x, i_bar_x)
    // I(x.foo()) models @1.foo();@1.bar()
    assert(statesolver.traceInAbstraction(
      state.copy(traceAbstraction = Set(AbstractTrace(i_foo_x,Nil, Map()))),
      trace))

    // I(x.foo()) ! models empty
    assert(!statesolver.traceInAbstraction(
      state.copy(traceAbstraction = Set(AbstractTrace(i_foo_x,Nil,Map()))),
      Nil))

    // NI(x.foo(), x.bar()) ! models empty
    assert(!statesolver.traceInAbstraction(
      state.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x,Nil,Map()))),
      Nil))

    // NI(x.foo(), x.bar()) ! models @1.foo();@1.bar()
    assert(!
      statesolver.traceInAbstraction(
        state.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x, Nil,Map()))),
        trace
      ))

    // NI(x.foo(),x.bar()) |> x.foo() models empty
    assert(
      statesolver.traceInAbstraction(
        state.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x, i_foo_x::Nil,Map()))),
        Nil
      ))
    // NI(x.foo(),x.bar()) |> x.foo() models @1.bar()
    assert(
      statesolver.traceInAbstraction(
        state.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x, i_foo_x::Nil,Map()))),
        TMessage(CIEnter, bar, TAddr(1)::Nil)::Nil
      ))
    // NI(x.foo(),x.bar()) |> x.foo() models @1.foo();@1.bar()
    assert(
      statesolver.traceInAbstraction(
        state.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x, i_foo_x::Nil,Map()))),
        trace
      ))

    // NI(x.foo(),x.bar()) |> x.bar() ! models empty
    assert(
      !statesolver.traceInAbstraction(
        state.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x, i_bar_x::Nil,Map()))),
        Nil
      ))

    // Not NI(x.foo(), x.bar())  models @1.foo();@1.bar()
    assert(
      statesolver.traceInAbstraction(
        state.copy(traceAbstraction = Set(AbstractTrace(Not(ni_foo_x_bar_x), Nil,Map()))),
        trace
      ))
    //TODO: test "and", "scoped abstract traces"
  }

  private def getStateSolver: Z3StateSolver = {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy: Map[String, Set[String]] =
      Map("java.lang.Object" -> Set("String", "Foo", "Bar", "java.lang.Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))

    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    new Z3StateSolver(pc)
  }

  test("quantifier example") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val foo1:ArithExpr = ctx.mkConst("foo", ctx.mkIntSort()).asInstanceOf[ArithExpr]
    println(s"foo1: ${foo1}")
    val f = ctx.mkFuncDecl("f",ctx.mkIntSort(), ctx.mkBoolSort())
    val expr:Expr = ctx.mkIff(
      f.apply(foo1).asInstanceOf[BoolExpr],
      ctx.mkGt(foo1, ctx.mkInt(0)))
    val a1 = ctx.mkForall(Array(foo1),expr, 1,
      null,null,
      null,null)
    val a = ctx.mkExists(Array(foo1),expr, 1,
      null,null,
      null,null)
    println(s"input:\n${a}")

    solver.add(a)
    solver.check()
    val m = solver.getModel

    println(s"model: \n${m}")
  }
  test("sandbox") {
    val ctx = new Context
    val solver = ctx.mkSolver()
    val addr = ctx.mkUninterpretedSort("Msg")
//    val msgSort2 = ctx.mkUninterpretedSort("Msg")
//    val pos1 = ctx.mkFuncDecl("tracePos", ctx.mkIntSort, msgSort)
//    val pos2 = ctx.mkFuncDecl("tracePos", ctx.mkIntSort, msgSort2)
//    val m1 = ctx.mkConst("m1",msgSort)
//    val m2 = ctx.mkConst("m2",msgSort2)
//    val p = ctx.mkAnd(
//      ctx.mkEq(pos1.apply(ctx.mkInt(1)), m1 ),
//      ctx.mkEq(pos2.apply(ctx.mkInt(1)), m2),
//      ctx.mkNot(ctx.mkEq(m1,m2)))
    val a1 = ctx.mkConst("a1", addr)
    val a2 = ctx.mkConst("a2", addr)
    val a3 = ctx.mkConst("a3", addr)
    val p1 = ctx.mkEq(a1,a2)
    val p2 = ctx.mkNot(ctx.mkEq(a2,a3))
    val p3 = ctx.mkEq(a3,a1)
    solver.add(ctx.mkAnd(p1,p2,p3))

    solver.check() match {
      case Status.UNSATISFIABLE => println("unsat")
      case Status.SATISFIABLE => println(solver.getModel)
      case Status.UNKNOWN => ???
    }

  }

  test("sandbox2") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val es: EnumSort = ctx.mkEnumSort("Foo", "Foo1", "Foo2")
    val foo2: Expr = es.getConst(1)
    println(foo2)
//    solver.add(ctx.mkEq(foo2, ctx.mkSymbol("Foo2")))


    solver.check() match {
      case Status.UNSATISFIABLE => println("unsat")
      case Status.SATISFIABLE => println(solver.getModel)
      case Status.UNKNOWN => ???
    }

  }
}
