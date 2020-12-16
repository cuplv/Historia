package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{ArithExpr, BoolExpr, Context, EnumSort, Expr, IntExpr, Solver, Status, Symbol}
import edu.colorado.plv.bounder.ir.{AppLoc, CBEnter, CallbackMethodInvoke}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSAbsBind, NI, Not, Or}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbsAnd, AbsArrow, AbsEq, AbsFormula, CallStackFrame, Equals, FieldPtEdge, NotEquals, NullVal, PureConstraint, PureVar, StackVar, State, SubclassOf, TraceAbstraction, TypeComp}
import edu.colorado.plv.bounder.testutils.{TestIRLineLoc, TestIRMethodLoc}

class Z3StateSolverTest extends org.scalatest.FunSuite {
  val dummyLoc = CallbackMethodInvoke(fmwClazz = "",
    fmwName="void foo()", TestIRMethodLoc("","foo"))
  val v = PureVar()
  val frame = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> v))
  val state = State(Nil,Map(),Set(), Set())
  test("null not null") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy : Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    val v2 = PureVar()
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal), PureConstraint(v2, Equals, NullVal))
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints,Set())
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)
  }
  test("alias") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy : Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    val v2 = PureVar()
    val v3 = PureVar()
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal),
      PureConstraint(v3, Equals, NullVal))
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints + PureConstraint(v2, Equals, v3),Set())
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)
  }
  test("Separate fields imply base must not be aliased a^.f->b^ * c^.f->b^ AND a^=c^ (<=> false)") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy : Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    val v2 = PureVar()
    val v3 = PureVar()
    val v4 = PureVar()
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v, Equals, v2)), Set())
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)

    // v3 and v4 on the right side of the points to can be aliased
    val unrefutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4)), Set())
    val simplifyResult2 = statesolver.simplify(unrefutableState)
    assert(simplifyResult2.isDefined)
  }
  test("aliased object implies fields must be aliased refuted by type constraints") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy : Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    // aliased and contradictory types of field
    val v2 = PureVar()
    val v3 = PureVar()
    val v4 = PureVar()
    val constraints = Set(
      PureConstraint(v3, Equals, v4),
      PureConstraint(v3, TypeComp, SubclassOf("String")),
      PureConstraint(v4, TypeComp, SubclassOf("Foo"))
    )
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3),constraints, Set())
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)

    // aliased and consistent field type constraints
    val constraints2 = Set(
      PureConstraint(v3, Equals, v4),
      PureConstraint(v3, TypeComp, SubclassOf("String")),
      PureConstraint(v4, TypeComp, SubclassOf("Object"))
    )
    val state = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),constraints2, Set())
    val simplifyResult2 = statesolver.simplify(state)
    assert(simplifyResult2.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) && a == p1 (<==>true)") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy : Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val niBarBaz = NI(i,i2)
    val p1 = PureVar()
    val abs1 = AbsAnd(AbsFormula(niBarBaz), AbsEq("a",p1))
    val state1 = State(Nil, Map(),Set(), Set(abs1))
    val res1 = statesolver.simplify(state1)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) |> I(a.bar()) (<==>true)") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy : Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val niBarBaz = NI(i,i2)
    val abs1 = AbsArrow(AbsFormula(niBarBaz), i)
    val state1 = State(Nil, Map(),Set(), Set(abs1))
    val res1 = statesolver.simplify(state1)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy : Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i,i2)

    // pure vars for next few tests
    val p1 = PureVar()
    val p2 = PureVar()

    // NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)
    val abs1: TraceAbstraction = AbsArrow(
      AbsAnd(AbsAnd(AbsFormula(niBarBaz), AbsEq("a",p1)), AbsEq("b",p1)),
      i3
    )
    val state1 = State(Nil, Map(),Set(), Set(abs1))
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
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy: Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val stateSolver = new Z3StateSolver(pc)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar()
    val p2 = PureVar()

    // NI(a.bar(),a.baz()) |> I(c.bar()) && a == p1 && c == p1 (<=> true)
    val abs2: TraceAbstraction = AbsArrow(
      AbsAnd(AbsAnd(AbsFormula(niBarBaz), AbsEq("a",p1)), AbsEq("c",p1)),
      i4
    )
    val state2 = State(Nil,Map(),Set(), Set(abs2))
    val res2 = stateSolver.simplify(state2)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(b.baz()) |> I(c.bar()) (<=> true) ") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy: Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar()

    // NI(a.bar(),a.baz()) |> I(c.bar()) |> i(b.baz()
    val niaa: TraceAbstraction = AbsArrow(AbsArrow(
      AbsFormula(niBarBaz),
      i3
    ),i4)
    val abs1 = AbsAnd(AbsEq("a",p1), AbsAnd(AbsEq("c",p1), AbsAnd(AbsEq("b",p1), niaa)))
    val state2 = State(Nil,Map(),Set(), Set(abs1))
    val res2 = statesolver.simplify(state2, Some(20)) //TODO: remove dbg limit
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = b = c (<=> false) ") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy: Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar()

    // NI(a.bar(),a.baz()) |> I(c.bar()) |> i(b.baz()
    val niaa: TraceAbstraction = AbsArrow(AbsArrow(
      AbsFormula(niBarBaz),
      i4
    ),i3)
    val abs1 = AbsAnd(AbsEq("a",p1), AbsAnd(AbsEq("c",p1), AbsAnd(AbsEq("b",p1), niaa)))
    val state2 = State(Nil,Map(),Set(), Set(abs1))
    val res2 = statesolver.simplify(state2)
    assert(res2.isEmpty)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = c (<=> true) ") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy: Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar()
    val p2 = PureVar()

    // NI(a.bar(),a.baz()) |> I(c.bar()) |> i(b.baz()
    val niaa: TraceAbstraction = AbsArrow(AbsArrow(
      AbsFormula(niBarBaz),
      i4
    ),i3)
    val abs1 = AbsAnd(AbsEq("a",p1), AbsAnd(AbsEq("c",p1), AbsAnd(AbsEq("b",p2), niaa)))
    val state2 = State(Nil,Map(),Set(), Set(abs1))
    val res2 = statesolver.simplify(state2)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = b (<=> false) ") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy: Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar()
    val p2 = PureVar()

    // NI(a.bar(),a.baz()) |> I(c.bar()) |> i(b.baz()
    val niaa: TraceAbstraction = AbsArrow(AbsArrow(
      AbsFormula(niBarBaz),
      i4
    ),i3)
    val abs1 = AbsAnd(AbsEq("a",p1), AbsAnd(AbsEq("c",p2), AbsAnd(AbsEq("b",p1), niaa)))
    val state2 = State(Nil,Map(),Set(), Set(abs1))
    val res2 = statesolver.simplify(state2)
    assert(res2.isEmpty)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(a.bar()),  NI(a.foo(),a.baz()) |> I(a.foo()) (<=> true) ") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy: Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    // Lifestate atoms for next few tests
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibaz = I(CBEnter, Set(("", "baz")), "a" :: Nil)
    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val t1 = AbsArrow(AbsFormula(NI(ibar, ibaz)), ibar)
    val t2 = AbsArrow(AbsFormula(NI(ifoo, ibaz)), ifoo)
    val s = state.copy(traceAbstraction = Set(t1,t2))
    val res = statesolver.simplify(s, Some(20))
    assert(res.isDefined)
  }
  test("Vacuous NI(a,a) spec") {
    //TODO: Is there ever a reason to need this case?
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy: Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "b" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBar = NI(i, i)

    // pure vars for next few tests
    val p1 = PureVar()
    val p2 = PureVar()
    //NI(a.bar(),a.bar()) (<=> true)
    // Note that this should be the same as I(a.bar())
    val nia = AbsFormula(niBarBar)
    val res0 = statesolver.simplify(state.copy(traceAbstraction = Set(nia)))
    assert(res0.isDefined)

    //NI(a.bar(),a.bar()) |> I(b.bar()) && a = b (<=> true)
    val niaa: TraceAbstraction = AbsArrow(
      AbsFormula(niBarBar),
      i4
    )
    val abs1 = AbsAnd(AbsEq("a",p1), AbsAnd(AbsEq("b",p1), niaa))
    val res1 = statesolver.simplify(state.copy(traceAbstraction = Set(abs1)))
    assert(res1.isDefined)
  }
  test("Subsumption of states") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy: Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))

    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)

    val p1 = PureVar()
    val p2 = PureVar()
    val loc = AppLoc(TestIRMethodLoc("","foo"), TestIRLineLoc(1), isPre = false)

    val state = State(CallStackFrame(loc,None,Map(StackVar("x") -> p1))::Nil, Map(),Set(),Set())
    val state2 = state.copy(callStack =
      state.callStack.head.copy(locals=Map(StackVar("x") -> p1, StackVar("y")->p2))::Nil)
    assert(statesolver.canSubsume(state,state))
    assert(statesolver.canSubsume(state,state2))
    assert(!statesolver.canSubsume(state2,state))

    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibarc = I(CBEnter, Set(("", "bar")), "c" :: Nil)
    val ifooc = I(CBEnter, Set(("", "foo")), "c" :: Nil)

    // I(a.foo()) can subsume I(a.foo()) |> a.bar()
    val baseTrace1 = AbsAnd(AbsFormula(ifoo), AbsEq("a",p1))
    val arrowTrace1 = AbsArrow(baseTrace1, ibarc)
    val state_ = state.copy(traceAbstraction = Set(baseTrace1))
    val state__ = state.copy(traceAbstraction = Set(arrowTrace1))
    assert(statesolver.canSubsume(state_,state__))

    val baseTrace = AbsAnd(AbsFormula(NI(ifoo, ibar)), AbsEq("a", p1))
    val state3_ = state.copy(traceAbstraction = Set(baseTrace))

    // NI(a.foo(), a.bar()) can subsume itself
    val res = statesolver.canSubsume(state3_, state3_)
    assert(res)

    val state3__ = state.copy(traceAbstraction = Set(AbsArrow(baseTrace, ibarc)))
    // NI(a.foo(), a.bar()) can subsume NI(a.foo(), a.bar()) |> c.bar()
    assert(statesolver.canSubsume(state3_,state3__))

    // NI(a.foo(), a.bar()) cannot subsume NI(a.foo(), a.bar()) |> c.foo()
    val fooBarArrowFoo = state.copy(traceAbstraction = Set(AbsArrow(baseTrace, ifooc)))
    assert(!statesolver.canSubsume(state3_, fooBarArrowFoo, Some(10)))
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
    val solver: Solver = ctx.mkSolver()
    val msgSort = ctx.mkUninterpretedSort("Msg")
    val msgSort2 = ctx.mkUninterpretedSort("Msg")
    val pos1 = ctx.mkFuncDecl("tracePos", ctx.mkIntSort, msgSort)
    val pos2 = ctx.mkFuncDecl("tracePos", ctx.mkIntSort, msgSort2)
    val m1 = ctx.mkConst("m1",msgSort)
    val m2 = ctx.mkConst("m2",msgSort2)
    val p = ctx.mkAnd(
      ctx.mkEq(pos1.apply(ctx.mkInt(1)), m1 ),
      ctx.mkEq(pos2.apply(ctx.mkInt(1)), m2),
      ctx.mkNot(ctx.mkEq(m1,m2)))
    solver.add(p)

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
