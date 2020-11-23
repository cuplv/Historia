package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{ArithExpr, BoolExpr, Context, EnumSort, Expr, IntExpr, Solver, Status, Symbol}
import edu.colorado.plv.bounder.ir.{CBEnter, CallbackMethodInvoke}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSAbsBind, NI, Not, Or}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbsAnd, AbsArrow, AbsEq, AbsFormula, CallStackFrame, Equals, FieldPtEdge, NotEquals, NullVal, PureConstraint, PureVar, StackVar, State, SubclassOf, TraceAbstraction, TypeComp}
import edu.colorado.plv.bounder.testutils.TestIRMethodLoc

class Z3StateSolverTest extends org.scalatest.FunSuite {
  val dummyLoc = CallbackMethodInvoke(fmwClazz = "",
    fmwName="void foo()", TestIRMethodLoc("","foo"))
  val v = PureVar()
  val frame = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> v))
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
    val simplifyResult = statesolver.simplify(refutableState,true,Some(0))
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
    val simplifyResult = statesolver.simplify(refutableState,true,Some(0))
    assert(!simplifyResult.isDefined)

    // v3 and v4 on the right side of the points to can be aliased
    val unrefutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4)), Set())
    val simplifyResult2 = statesolver.simplify(unrefutableState,true,Some(0))
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
    val res1 = statesolver.simplify(state1,true, Some(2))
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
    val res1 = statesolver.simplify(state1,true)
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
    val res1 = statesolver.simplify(state1,true)
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

    // NI(a.bar(),a.baz()) |> I(c.bar()) && a == p1 && c == p1 (<=> true)
    val abs2: TraceAbstraction = AbsArrow(
      AbsAnd(AbsAnd(AbsFormula(niBarBaz), AbsEq("a",p1)), AbsEq("c",p1)),
      i4
    )
    val state2 = State(Nil,Map(),Set(), Set(abs2))
    val res2 = statesolver.simplify(state2, true)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(b.baz()) |> I(c.bar() (<=> true) ") {
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
      i3
    ),i4)
    val abs1 = AbsAnd(AbsEq("a",p1), AbsAnd(AbsEq("c",p1), AbsAnd(AbsEq("b",p1), niaa)))
    val state2 = State(Nil,Map(),Set(), Set(abs1))
    val res2 = statesolver.simplify(state2, true)
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
    val p2 = PureVar()

    // NI(a.bar(),a.baz()) |> I(c.bar()) |> i(b.baz()
    val niaa: TraceAbstraction = AbsArrow(AbsArrow(
      AbsFormula(niBarBaz),
      i4
    ),i3)
    val abs1 = AbsAnd(AbsEq("a",p1), AbsAnd(AbsEq("c",p1), AbsAnd(AbsEq("b",p1), niaa)))
    val state2 = State(Nil,Map(),Set(), Set(abs1))
    val res2 = statesolver.simplify(state2, true)
    assert(!res2.isDefined)
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
    val res2 = statesolver.simplify(state2, true)
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
    val res2 = statesolver.simplify(state2, true)
    assert(!res2.isDefined)
  }
  test("quantifier example") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val foo1:ArithExpr = ctx.mkConst("foo", ctx.mkIntSort()).asInstanceOf[ArithExpr]
    val f = ctx.mkFuncDecl("f",ctx.mkIntSort(), ctx.mkBoolSort())
    val expr:Expr = ctx.mkIff(
      f.apply(foo1).asInstanceOf[BoolExpr],
      ctx.mkGt(foo1, ctx.mkInt(0)))
    val ptrn: Array[Expr] = Array(ctx.mkGt(foo1,ctx.mkInt(1)))
    val a = ctx.mkForall(Array(foo1),expr, 1,
      null,null,
      null,null)

    solver.add(a)
    solver.check()
    val m = solver.getModel

    println(m)
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
