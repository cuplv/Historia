package edu.colorado.plv.bounder.solver

import better.files.Resource
import com.microsoft.z3._
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.{And, I, LSFalse, LSTrue, NI, Not, Or, Ref, SetSignatureMatcher, SignatureMatcher, SubClassMatcher}
import edu.colorado.plv.bounder.symbolicexecutor.state._
import org.scalatest.funsuite.FixtureAnyFunSuite

import scala.collection.BitSet
import scala.language.implicitConversions

class Z3StateSolverTest extends FixtureAnyFunSuite {

  private val fooMethod = TestIRMethodLoc("","foo", List(Some(LocalWrapper("@this","Object"))))
  private val dummyLoc = CallbackMethodReturn(tgtClazz = "",
     fmwName="void foo()", fooMethod, None)
  private val v = PureVar(State.getId_TESTONLY())
  private val frame = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> v))
  private val state = State.topState
  case class FixtureParam(typeSolving: StateTypeSolving)

  val hierarchy: Map[String, Set[String]] =
    Map("java.lang.Object" -> Set("String", "Foo", "Bar",
      "com.example.createdestroy.MyFragment",
      "rx.Single",
      "com.example.createdestroy.-$$Lambda$MyFragment$hAOPQ7FFP1lMCJX7gGOvwmZq1uk",
      "java.lang.Object"),
      "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"),
      "com.example.createdestroy.MyFragment" -> Set("com.example.createdestroy.MyFragment"),
      "com.example.createdestroy.-$$Lambda$MyFragment$hAOPQ7FFP1lMCJX7gGOvwmZq1uk" ->
        Set("com.example.createdestroy.-$$Lambda$MyFragment$hAOPQ7FFP1lMCJX7gGOvwmZq1uk"),
      "rx.Single" -> Set("rx.Single"),
      "foo" -> Set("foo"),
      "bar" -> Set("bar"),
      "foo2" -> Set("foo2")
  )
  private val classToInt: Map[String, Int] = hierarchy.keySet.zipWithIndex.toMap
  val intToClass: Map[Int, String] = classToInt.map(k => (k._2, k._1))

  object BoundedTypeSet {
    def apply(someString: Some[String], none: None.type, value: Set[Nothing]): TypeSet = someString match{
      case Some(v) =>
        val types = hierarchy(v).map(classToInt)
        val bitSet = BitSet() ++ types
        BitTypeSet(bitSet)
    }
  }

  implicit def set2SigMat(s:Set[(String,String)]):SignatureMatcher =
    SubClassMatcher(s.map(_._1),s.map(_._2).mkString("|"),s.head._1 + s.head._2)

  override def withFixture(test: OneArgTest) = {
    // Run all tests with both set inclusion type solving and solver type solving
    // Some subsumption tests override type solving parameter
    // All other tests should work with either
//    withFixture(test.toNoArgTest(FixtureParam(SetInclusionTypeSolving)))
    withFixture(test.toNoArgTest(FixtureParam(SolverTypeSolving)))
  }
  test("value not value") { f =>
    println(s"fixture param: $f")
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val v2 = PureVar(State.getId_TESTONLY())
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal), PureConstraint(v2, Equals, NullVal))
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints,Map(),Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState)
    assert(simplifyResult.isEmpty)

    val constraints2 = Set(PureConstraint(v2, NotEquals, IntVal(0)), PureConstraint(v2, Equals, IntVal(0)))
    val refutableState2 = refutableState.copy(sf = refutableState.sf.copy(pureFormula = constraints2))
    val simplifyResult2 = stateSolver.simplify(refutableState2)
    assert(simplifyResult2.isEmpty)

    val constraints3 = Set(PureConstraint(v2, NotEquals, IntVal(0)), PureConstraint(v2, Equals, IntVal(1)))
    val refutableState3 = refutableState.copy(sf = refutableState.sf.copy(pureFormula = constraints3))
    val simplifyResult3 = stateSolver.simplify(refutableState3)
    assert(simplifyResult3.isDefined)

  }
  test("alias") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val v2 = PureVar(State.getId_TESTONLY())
    val v3 = PureVar(State.getId_TESTONLY())
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal),
      PureConstraint(v3, Equals, NullVal))
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints + PureConstraint(v2, Equals, v3),Map(),Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)
  }
  test("Separate fields imply base must not be aliased a^.f->b^ * c^.f->b^ AND a^=c^ (<=> false)") { f=>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val v2 = PureVar(State.getId_TESTONLY())
    val v3 = PureVar(State.getId_TESTONLY())
    val v4 = PureVar(State.getId_TESTONLY())
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v, Equals, v2)),Map(), Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)

    // v3 and v4 on the right side of the points to can be aliased
    val unrefutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4),
        PureConstraint(v, NotEquals, v2)),Map(), Set()),0)
    val simplifyResult2 = stateSolver.simplify(unrefutableState)
    assert(simplifyResult2.isDefined)

    // object field can point to self
    val unrefutableState2 = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4),
        PureConstraint(v, Equals, v4)),Map(), Set()),0)
    val simplifyResult3 = stateSolver.simplify(unrefutableState2)
    assert(simplifyResult3.isDefined)
  }
  test("Transitive equality should be refuted by type constraints") { f=>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val v2 = PureVar(State.getId_TESTONLY())
    val v3 = PureVar(State.getId_TESTONLY())
    val v4 = PureVar(State.getId_TESTONLY())
    val refutableState = State(StateFormula(List(frame),
      Map(),
      Set(PureConstraint(v2, Equals, v3),PureConstraint(v3, Equals, v4)),
      Map(v2->BoundedTypeSet(Some("String"),None,Set()),
        //        v3->BoundedTypeSet(Some("String"),None,Set()),
        v4->BoundedTypeSet(Some("Foo"),None,Set())),
      Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)

    val refutableState2 = State(StateFormula(List(frame),
      Map(),
      Set(PureConstraint(v2, Equals, v3),PureConstraint(v3, Equals, v4), PureConstraint(v2, NotEquals, v4)),
      Map(),
      Set()),0)
    val simplifyResult2 = stateSolver.simplify(refutableState2)
    assert(!simplifyResult2.isDefined)
  }
  test("test feasibility of constraints before GC") { f=>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val v2 = PureVar(State.getId_TESTONLY())
    val v3 = PureVar(State.getId_TESTONLY())
    val v4 = PureVar(State.getId_TESTONLY())
    val refutableState = State(StateFormula(List(frame),
      Map(),
      Set(PureConstraint(v2, Equals, v3),PureConstraint(v3, Equals, v4)),
      Map(v2->BoundedTypeSet(Some("String"),None,Set()),
        v3->BoundedTypeSet(Some("String"),None,Set()),v4->BoundedTypeSet(Some("Foo"),None,Set())),
      Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)

  }
  //TODO: group equal pure vars for type check
  test("aliased object implies fields must be aliased refuted by type constraints") { f =>
    val (stateSolver,_) = getStateSolver(SolverTypeSolving)
//    val (stateSolver,_) = getStateSolver(SetInclusionTypeSolving)

    // aliased and contradictory types of field
    val v2 = PureVar(State.getId_TESTONLY())
    val v3 = PureVar(State.getId_TESTONLY())
    val v4 = PureVar(State.getId_TESTONLY())
    val constraints = Set(
      PureConstraint(v3, Equals, v4),
//      PureConstraint(v3, TypeComp, SubclassOf("String")),
//      PureConstraint(v4, TypeComp, SubclassOf("Foo"))
    )
    val typeC = Map(
      v3-> BoundedTypeSet(Some("String"),None,Set()),
      v4 -> BoundedTypeSet(Some("Foo"), None, Set())
    )
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3),constraints,typeC, Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)

    // aliased and consistent field type constraints
    val constraints2 = Set(
      PureConstraint(v3, Equals, v4),
//      PureConstraint(v3, TypeComp, SubclassOf("String")),
//      PureConstraint(v4, TypeComp, SubclassOf("java.lang.Object"))
    )
    val typeC2 = Map(
      v3 -> BoundedTypeSet(Some("String"),None,Set()),
      v4 -> BoundedTypeSet(Some("java.lang.Object"),None,Set())
    )
    val state = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),constraints2,typeC2, Set()),0)
    val simplifyResult2 = stateSolver.simplify(state)
    assert(simplifyResult2.isDefined)
  }
  test("Trace abstraction lsfalse is empty and lstrue is not"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val absFalse = AbstractTrace(LSFalse, Nil, Map())
    val state = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = Set(absFalse)))
    val res = stateSolver.simplify(state)
    assert(!res.isDefined)
    val absTrue = AbstractTrace(LSTrue, Nil, Map())
    val stateTrue = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = Set(absTrue)))
    val resTrue = stateSolver.simplify(stateTrue)
    assert(resTrue.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) && a == p1 (<==>true)") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val niBarBaz = NI(i,i2)
    val p1 = PureVar(State.getId_TESTONLY())
    val abs1 = AbstractTrace(niBarBaz, Nil, Map("a"->p1))
    val state1 = State(StateFormula(Nil, Map(),Set(),Map(), Set(abs1)),0)
    val res1 = stateSolver.simplify(state1)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) |> I(a.bar()) (<==>true)") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val niBarBaz = NI(i,i2)
//    val abs1 = AbsArrow(AbsFormula(niBarBaz), i::Nil)
    val abs1 = AbstractTrace(niBarBaz, i::Nil, Map())
    val state1 = State(StateFormula(Nil, Map(),Set(),Map(), Set(abs1)),0)
    val res1 = stateSolver.simplify(state1)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("_", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("_", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("_", "baz")), "b" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i,i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())

    // NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)
    val abs1 = AbstractTrace(niBarBaz,i3::Nil, Map("a"->p1, "b"->p1))
//    AbsAnd(AbsAnd(AbsFormula(niBarBaz), AbsEq("a",p1)), AbsEq("b",p1)),
    val state1 = State(StateFormula(Nil, Map(),Set(),Map(), Set(abs1)),0)
    println(s"state: ${state1}")
    val res1 = stateSolver.simplify(state1, Some(3))
    assert(!res1.isDefined)
    val res2 = stateSolver.witnessed(state1)
    assert(!res2)

    //TODO: more tests
    // [NI(m1^,m2^) OR (NOT NI(m1^,m2^)) ] AND (a |->a^) => TRUE
    val pred2 = Or(NI(i,i2),Not(NI(i,i2)))
    //val state2 = State(Nil, Map(),Set(), Set(LSAbstraction(pred2, Map("a"-> p1))))
    //val res2 = stateSolver.simplify(state2)
    //assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) && a == p1 && c == p1 (<=> true)") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())

    // NI(a.bar(),a.baz()) |> I(c.bar()) && a == p1 && c == p1 (<=> true)
    val abs2 = AbstractTrace(niBarBaz,i4::Nil, Map("a"->p1, "c"->p1) )
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(abs2)),0)
    val res2 = stateSolver.simplify(state2)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(b.baz()) |> I(c.bar()) (<=> true) ") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())

    // NI(a.bar(),a.baz()) |> I(c.bar()) ; i(b.baz()
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1, "c"->p1))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(niaa)),0)
    val res2 = stateSolver.simplify(state2)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) ; I(c.bar()) ; I(b.baz()) && a = b = c (<=> false) ") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())

    // NI(a.bar(),a.baz()) |> I(a.bar());I(a.baz())
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1, "c"->p1, "b"->p1))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(niaa)),0)
    val res2 = stateSolver.simplify(state2)
    assert(res2.isEmpty)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = c (<=> true) ") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())

    // NI(a.bar(),a.baz()) |> I(c.bar()) ; I(b.baz())
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1, "c"->p1, "b"->p2))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(niaa)),0)
    val res2 = stateSolver.simplify(state2, Some(10))
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = b (<=> false) ") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())

    // NI(a.bar(),a.baz()) |> I(c.bar()) |> i(b.baz()
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1,"b"->p1, "c"->p2))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(niaa)),0)
    val res2 = stateSolver.simplify(state2)
    assert(res2.isEmpty)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(a.bar()),  NI(a.foo(),a.baz()) |> I(a.foo()) (<=> true) ") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibaz = I(CBEnter, Set(("", "baz")), "a" :: Nil)
    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val t1 = AbstractTrace(NI(ibar,ibaz), ibar::Nil, Map())
    val t2 = AbstractTrace(NI(ifoo,ibaz), ifoo::Nil, Map())
    val s = state.copy(sf = state.sf.copy(traceAbstraction = Set(t1,t2)))
    val res = stateSolver.simplify(s)
    assert(res.isDefined)
  }

  test("( (Not I(a.bar())) && (Not I(a.baz())) ) |> I(b.bar()) && a=pv1 && b = pv1,  (<=>false) ") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val ibar_a = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibar_b = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibaz_a = I(CBEnter, Set(("", "baz")), "a" :: Nil)
    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)

    // (Not I(a.bar()))  |> I(b.bar()) && a = pv1 && b = pv1
    val pv1 = PureVar(1)
    val t1 = AbstractTrace(Not(ibar_a), ibar_b::Nil, Map()).addModelVar("a",pv1).addModelVar("b",pv1)
    val s1 = state.copy(sf = state.sf.copy(traceAbstraction = Set(t1)))
    val res = stateSolver.simplify(s1)
    assert(res.isEmpty)

    //( (Not I(a.bar())) && (Not I(a.baz())) ) |> I(b.bar()) && a = pv1 && b = pv1
    val t2 = AbstractTrace(And(Not(ibar_a), Not(ibaz_a)), ibar_b::Nil, Map())
      .addModelVar("a",pv1).addModelVar("b",pv1)
    val s2 = state.copy(sf = state.sf.copy(traceAbstraction = Set(t2)))
    val res2 = stateSolver.simplify(s2)
    assert(res2.isEmpty)
  }
  test("Not witnessed: I(a.foo()) |> b.foo() && Not(I(b.bar())) |> a.bar() && a = pv1 && b = pv2") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val ibar_a = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibar_b = I(CBEnter, Set(("", "bar")), "b" :: Nil)
    val ifoo_a = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ifoo_b = I(CBEnter, Set(("", "foo")), "b" :: Nil)

    val pv1 = PureVar(1)
    val pv2 = PureVar(2)

    // t1: I(a.foo()) |> b.foo()
    val t1 = AbstractTrace(ifoo_a, ifoo_b::Nil, Map("a" -> pv1, "b" -> pv2))

    // t2: Not(I(b.bar())) |> a.bar()
    val t2 = AbstractTrace(Not(ibar_b), ibar_a::Nil, Map("a" -> pv1, "b" -> pv2))

    val s1 = state.copy(sf = state.sf.copy(traceAbstraction = Set(t1,t2)))
    val res = stateSolver.witnessed(s1)
    assert(!res)

    // t1 is witnessed
    val s2 = state.copy(sf = state.sf.copy(traceAbstraction = Set(t1)))
    val res2 = stateSolver.witnessed(s2)
    assert(res2)
  }
  test("Not feasible: Not(I(a.foo(_)))) |> b.foo(c) && a=p1 && b = p3 && c = p2 && p1 = p3") {f=>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val ifoo_a_ = I(CBEnter, Set(("", "foo")), "a"::"_" :: Nil)
    val ifoo_bc = I(CBEnter, Set(("", "foo")), "b"::"c" :: Nil)

    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    val pv3 = PureVar(3)

    // t1: I(a.foo(_)) |> b.foo(c)
    val t1 = AbstractTrace(Not(ifoo_a_), ifoo_bc::Nil, Map("a" -> pv1, "b" -> pv3, "c" -> pv2))

    val s1 = state.copy(sf = state.sf.copy(pureFormula = Set(PureConstraint(pv1, Equals, pv3)),
      traceAbstraction = Set(t1)))

    val isFeas = stateSolver.simplify(s1)
    assert(isFeas.isEmpty)

    val isWit = stateSolver.witnessed(s1)
    assert(!isWit)
  }

  ignore ("Pickled states from integration tests should not crash solver") { f =>
    //TODO: pickle format changed, fix this test
    // (Map(l -> p-2, s -> p-5) -
    // NI( I(CIExit I_CIExit_rx.Single_rx.Subscription subscribe(rx.functions.Action1) ( _,s,l ) ,
    //     I(CIExit I_CIExit_rx.Subscription_void unsubscribe() ( _,s ) ) |>
    //     I(CIExit I_CIExit_rx.Single_rx.Subscription subscribe(rx.functions.Action1) ( LS_GENERATED__3,p-5,p-2 ))
    val pickledAbstractTrace =
    """{"a":{"$type":"edu.colorado.plv.bounder.lifestate.LifeState.NI","i1":
      |{"$type":"edu.colorado.plv.bounder.lifestate.LifeState.I","mt":{"$type":"edu.colorado.plv.bounder.ir.CIExit"},
      |"signatures":[["rx.Single","rx.Subscription subscribe(rx.functions.Action1)"]],"lsVars":["_","s","l"]},
      |"i2":{"$type":"edu.colorado.plv.bounder.lifestate.LifeState.I",
      |"mt":{"$type":"edu.colorado.plv.bounder.ir.CIExit"},
      |"signatures":[["rx.Subscription","void unsubscribe()"],
      |["rx.internal.operators.CachedObservable$ReplayProducer","void unsubscribe()"]],
      |"lsVars":["_","s"]}},"rightOfArrow":[{"$type":"edu.colorado.plv.bounder.lifestate.LifeState.I",
      |"mt":{"$type":"edu.colorado.plv.bounder.ir.CIExit"},
      |"signatures":[["rx.Single","rx.Subscription subscribe(rx.functions.Action1)"]],
      |"lsVars":["LS_GENERATED__3","LS_GENERATED__4","LS_GENERATED__5"]}],
      |"modelVars":{"l":{"$type":"edu.colorado.plv.bounder.symbolicexecutor.state.PureVar","id":2},
      |"s":{"$type":"edu.colorado.plv.bounder.symbolicexecutor.state.PureVar","id":5},
      |"LS_GENERATED__4":{"$type":"edu.colorado.plv.bounder.symbolicexecutor.state.PureVar","id":5},
      |"LS_GENERATED__5":{"$type":"edu.colorado.plv.bounder.symbolicexecutor.state.PureVar","id":2}}}""".stripMargin

    import upickle.default._
    val at = read[AbstractTrace](pickledAbstractTrace)
    val state = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = Set(at)))

    val (stateSolver,_) = getStateSolver()
    val res = stateSolver.simplify(state)
    assert(res.isDefined)

    // (Map(f -> p-1) -
    // ((NOT I(CBEnter I_CBEnter_android.app.DialogFragment_void onActivityCreated(android.os.Bundle) ( _,f ))
    // OR
    // I(CBExit I_CBExit_android.app.Fragment_void onDestroy() ( _,f ))
    // |> I(CBEnter I_CBEnter_android.app.DialogFragment_void onActivityCreated(android.os.Bundle) ( _,p-1 ))
    val at1Pickle =
    """{"a":{"$type":"edu.colorado.plv.bounder.lifestate.LifeState.Or",
      |"l1":{"$type":"edu.colorado.plv.bounder.lifestate.LifeState.Not",
      |"l":{"$type":"edu.colorado.plv.bounder.lifestate.LifeState.I",
      |"mt":{"$type":"edu.colorado.plv.bounder.ir.CBEnter"},
      |"signatures":[["androidx.fragment.app.DialogFragment","void onActivityCreated(android.os.Bundle)"],
      |["android.app.Fragment","void onActivityCreated(android.os.Bundle)"],
      |["androidx.fragment.app.Fragment","void onActivityCreated(android.os.Bundle)"],
      |["androidx.lifecycle.ReportFragment","void onActivityCreated(android.os.Bundle)"],
      |["android.support.v4.app.Fragment","void onActivityCreated(android.os.Bundle)"],
      |["android.support.wearable.view.CardFragment","void onActivityCreated(android.os.Bundle)"],
      |["android.support.v7.preference.PreferenceFragmentCompat","void onActivityCreated(android.os.Bundle)"],
      |["android.support.v14.preference.PreferenceFragment","void onActivityCreated(android.os.Bundle)"],
      |["android.support.v4.app.DialogFragment","void onActivityCreated(android.os.Bundle)"],
      |["android.arch.lifecycle.ReportFragment","void onActivityCreated(android.os.Bundle)"],
      |["android.app.DialogFragment","void onActivityCreated(android.os.Bundle)"],
      |["android.preference.PreferenceFragment","void onActivityCreated(android.os.Bundle)"]],
      |"lsVars":["_","f"]}},"l2":{"$type":"edu.colorado.plv.bounder.lifestate.LifeState.I",
      |"mt":{"$type":"edu.colorado.plv.bounder.ir.CBExit"},
      |"signatures":[["androidx.fragment.app.Fragment","void onDestroy()"],
      |["androidx.fragment.app.FragmentActivity","void onDestroy()"],
      |["android.app.Fragment","void onDestroy()"],
      |["androidx.fragment.app.DialogFragment","void onDestroyView()"],
      |["androidx.lifecycle.ReportFragment","void onDestroy()"],
      |["android.support.wearable.view.CardFragment","void onDestroy()"],
      |["android.support.v4.app.FragmentActivity","void onDestroy()"],
      |["androidx.fragment.app.Fragment","void onDestroyOptionsMenu()"],
      |["android.support.v4.app.Fragment","void onDestroy()"],
      |["android.preference.PreferenceFragment","void onDestroy()"],
      |["android.app.Fragment","void onDestroyView()"],
      |["android.arch.lifecycle.ReportFragment","void onDestroy()"],
      |["androidx.fragment.app.Fragment","void onDestroyView()"],
      |["android.app.Fragment","void onDestroyOptionsMenu()"],
      |["androidx.fragment.app.ListFragment","void onDestroyView()"]],
      |"lsVars":["_","f"]}},"rightOfArrow":[{"$type":"edu.colorado.plv.bounder.lifestate.LifeState.I",
      |"mt":{"$type":"edu.colorado.plv.bounder.ir.CBEnter"},"signatures":[["androidx.fragment.app.DialogFragment",
      |"void onActivityCreated(android.os.Bundle)"],["android.app.Fragment",
      |"void onActivityCreated(android.os.Bundle)"],["androidx.fragment.app.Fragment",
      |"void onActivityCreated(android.os.Bundle)"],["androidx.lifecycle.ReportFragment",
      |"void onActivityCreated(android.os.Bundle)"],["android.support.v4.app.Fragment",
      |"void onActivityCreated(android.os.Bundle)"],["android.support.wearable.view.CardFragment",
      |"void onActivityCreated(android.os.Bundle)"],["android.support.v7.preference.PreferenceFragmentCompat",
      |"void onActivityCreated(android.os.Bundle)"],["android.support.v14.preference.PreferenceFragment",
      |"void onActivityCreated(android.os.Bundle)"],["android.support.v4.app.DialogFragment",
      |"void onActivityCreated(android.os.Bundle)"],["android.arch.lifecycle.ReportFragment",
      |"void onActivityCreated(android.os.Bundle)"],["android.app.DialogFragment",
      |"void onActivityCreated(android.os.Bundle)"],["android.preference.PreferenceFragment",
      |"void onActivityCreated(android.os.Bundle)"]],"lsVars":["_","LS_GENERATED__15"]}],
      |"modelVars":{"f":{"$type":"edu.colorado.plv.bounder.symbolicexecutor.state.PureVar","id":1},
      |"LS_GENERATED__15":{"$type":"edu.colorado.plv.bounder.symbolicexecutor.state.PureVar","id":1}}}""".stripMargin
    val at1 = read[AbstractTrace](at1Pickle)

    val state1 = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = Set(at1)))
    val res1 = stateSolver.simplify(state1)
    assert(res1.isDefined)
  }
  test("Not I(a.foo) |> a.foo does not contain empty trace"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    implicit val zctx = stateSolver.getSolverCtx

    // Lifestate atoms for next few tests
    val foo_a = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val foo_b = I(CBEnter, Set(("", "foo")), "b" :: Nil)
    val bar_a = I(CBEnter, Set(("", "bar")), "a" :: Nil)


    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())

    val niaa = AbstractTrace(Not(foo_a), foo_b::Nil, Map("a"->p1, "b"->p2))
    val state = State(StateFormula(Nil,Map(),Set(PureConstraint(p1, Equals, p2)),Map(), Set(niaa)),0)
    val contains = stateSolver.traceInAbstraction(state, Nil )
    assert(!contains)

    val niaa2 = AbstractTrace(Or(Not(foo_a),bar_a), foo_b::Nil, Map("a"->p1))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(niaa2)),0)
    val simpl = stateSolver.simplify(state2,Some(2))
    assert(simpl.isDefined)
    val contains2 = stateSolver.traceInAbstraction(state2, Nil)
    assert(contains2)
  }

  test("refuted: I(a.foo()) && !Ref(a)"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    implicit val zctx = stateSolver.getSolverCtx

    // Lifestate atoms for next few tests
    val foo_a = I(CBEnter, Set(("", "foo")), "a":: "c" :: Nil)


    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())

    val at = AbstractTrace(foo_a, Nil, Map("a"->p1))
    val notRef = AbstractTrace(Not(Ref("b")), Nil, Map("b" -> p2))
    val state = State(StateFormula(Nil,Map(),
      Set(PureConstraint(p1, Equals, p2)),Map(), Set(at, notRef)),0)
    val res = stateSolver.simplify(state)
    assert(res.isEmpty)

    val state0 = state.copy(sf =
      state.sf.copy(pureFormula = Set(PureConstraint(p1, NotEquals, p2))))
    val res0 = stateSolver.simplify(state0)
    assert(res0.isDefined)

    val ref = AbstractTrace(Ref("b"), Nil, Map("b" -> p2))
    val state2 = State(StateFormula(Nil, Map(),
      Set(PureConstraint(p1, Equals, p2)), Map(), Set(at, ref)), 0)
    val res2 = stateSolver.simplify(state2)
    assert(res2.isDefined)
  }

  import upickle.default.read
  private val js = (name:String) => ujson.Value(Resource.getAsString(name)).obj
  //TODO: changed serialized format and broke this test
//  test("Test bad witnessed state"){
//    //  Not(I(f.onActivityCreated())) or I(f.onDestroy()) <= null = f.getActivity()
//    // The following abstract state should not be witnessed and not refuted:
//    // f == f2 /\ Not(I(f.onActivityCreated())) or I(f.onDestroy()) |> f2.onActivityCreated()
//    val state1 = read[State](js("TestStates/badWitnessState.json"))
//    val state = state1.copy(
//      traceAbstraction = state1.traceAbstraction.filter(v => v.toString.contains("onActivityCreated")),
//      pureFormula = state1.pureFormula.filter(p => p.toString.contains("p-1") && p.toString.contains("p-7"))
//    )
//    val stateSolver = getStateSolver()
//
//    val containsEmpty = stateSolver.traceInAbstraction(state, Nil)
//    assert(!containsEmpty)
//
//    val refuted = stateSolver.simplify(state)
//    assert(refuted.isDefined)
//    val witnessed = stateSolver.witnessed(state)
//    assert(!witnessed)
//  }

  test("Vacuous NI(a,a) spec") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "b" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBar = NI(i, i)

    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())
    //NI(a.bar(),a.bar()) (<=> true)
    // Note that this should be the same as I(a.bar())
    val nia = AbstractTrace(niBarBar, Nil, Map())
    val res0 = stateSolver.simplify(state.copy(sf = state.sf.copy(traceAbstraction = Set(nia))))
    assert(res0.isDefined)

    //NI(a.bar(),a.bar()) |> I(b.bar()) && a = b (<=> true)
    val niaa = AbstractTrace(niBarBar, i4::Nil, Map("a"->p1,"b"->p1))
    val res1 = stateSolver.simplify(state.copy(sf = state.sf.copy(traceAbstraction = Set(niaa))))
    assert(res1.isDefined)
  }
  test("Subsumption of stack"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val state = State(StateFormula(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil,
      Map(),Set(),Map(),Set()),0)
    val state_ = state.copy(sf = state.sf.copy(callStack = CallStackFrame(dummyLoc, None, Map(
      StackVar("x") -> p1,
      StackVar("y") -> p2
    ))::Nil))
    assert(stateSolver.canSubsume(state,state_))
    assert(!stateSolver.canSubsume(state_,state))

  }
  test("Subsumption of abstract traces") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val state = State(StateFormula(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil,
      Map(),Set(),Map(),Set()),0)
    val state2 = state.copy(sf = state.sf.copy(callStack =
      state.callStack.head.copy(locals=Map(StackVar("x") -> p1, StackVar("y")->p2))::Nil))
    assert(stateSolver.canSubsume(state,state))
    assert(stateSolver.canSubsume(state,state2))
    assert(!stateSolver.canSubsume(state2,state))

    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibarc = I(CBEnter, Set(("", "bar")), "c" :: Nil)
    val ifooc = I(CBEnter, Set(("", "foo")), "c" :: Nil)

    val baseTrace1 = AbstractTrace(ifoo, Nil, Map("a"->p1))
    val arrowTrace1 = AbstractTrace(ifoo, ibarc::Nil, Map("a"->p1))
    val state_ = state.copy(sf = state.sf.copy(traceAbstraction = Set(baseTrace1)))
    val state__ = state.copy(sf = state.sf.copy(traceAbstraction = Set(arrowTrace1)))

    // State I(a.foo())|>empty should subsume itself

    assert(stateSolver.canSubsume(state_,state_, Some(3)))
    // I(a.foo()) can subsume I(a.foo()) |> a.bar()
    assert(stateSolver.canSubsume(state_,state__))

    val baseTrace = AbstractTrace(NI(ifoo,ibar), Nil, Map("a"->p1))
    val state3_ = state.copy(sf = state.sf.copy(traceAbstraction = Set(baseTrace)))

    // NI(a.foo(), a.bar()) can subsume itself
    val res = stateSolver.canSubsume(state3_, state3_)
    assert(res)

    val state3__ = state.copy(sf = state.sf.copy(traceAbstraction =
      Set(AbstractTrace(NI(ifoo,ibar), ibarc::Nil, Map("a"->p1)))))
    // NI(a.foo(), a.bar()) can subsume NI(a.foo(), a.bar()) |> c.bar()
    assert(stateSolver.canSubsume(state3_,state3__))

    // NI(a.foo(), a.bar()) cannot subsume NI(a.foo(), a.bar()) |> c.foo() /\ a==c
    // ifooc::Nil
    val fooBarArrowFoo = state.copy(sf = state.sf.copy(
      traceAbstraction = Set(AbstractTrace(NI(ifoo,ibar), ifooc::Nil, Map("a"->p1, "c"->p1)))))
    val resfoobarfoo = stateSolver.canSubsume(state3_, fooBarArrowFoo)
    assert(!resfoobarfoo)

    // NI(a.foo(), a.bar()), I(a.foo()) should be subsumed by NI(a.foo(), a.bar())
    val s_foo_bar_foo = state.copy(sf = state.sf.copy(traceAbstraction =
      Set(AbstractTrace(NI(ifoo,ibar), Nil, Map("a"->p1, "c"->p1)),
        AbstractTrace(ifooc,Nil, Map()))))
    val s_foo_bar = state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(NI(ifoo,ibar),
      Nil, Map("a"->p1)))))
    assert(stateSolver.canSubsume(s_foo_bar, s_foo_bar_foo))

    // Extra trace constraint does not prevent subsumption
    // NI(foo(a),bar(a)), I(foo(c))  can subsume  NI(foo(a),bar(a))
    val res2 = stateSolver.canSubsume(s_foo_bar_foo, s_foo_bar)
    assert(res2)

    // NI(foo(a),bar(a)), I(foo(c)) /\ a!=c cannot subsume  NI(foo(a),bar(a))
    val s_foo_bar_foo_notEq = state.copy(sf = state.sf.copy(traceAbstraction =
      Set(AbstractTrace(NI(ifoo,ibar), Nil, Map("a"->p1, "c"->p2)),
        AbstractTrace(ifooc,Nil, Map())),
      pureFormula = Set(PureConstraint(p1, NotEquals, p2))
    ))
    val res3 = stateSolver.canSubsume(s_foo_bar_foo_notEq, s_foo_bar)
    assert(!res3)

    // Extra pure constraints should not prevent subsumption
    val fewerPure = State.topState.copy(sf = State.topState.sf.copy(
      pureFormula = Set(PureConstraint(p2, NotEquals, NullVal))))
    val morePure = fewerPure.copy(sf = fewerPure.sf.copy(pureFormula = fewerPure.pureFormula +
//      PureConstraint(p1, TypeComp, SubclassOf("java.lang.Object")) +
      PureConstraint(p1, NotEquals, p2),
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("java.lang.Object"),None,Set()))))
    assert(stateSolver.canSubsume(fewerPure, morePure))

  }
  test("X -> p1 && p1:T1 cannot subsume X -> p1 && p1:T2 && p2:T1"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val pvy = PureVar(1)
    val pvy2 = PureVar(2)
    val fr = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> pvy))
    val s1 = State.topState.copy(sf = State.topState.sf.copy(callStack = fr::Nil))
      .addTypeConstraint(pvy, BitTypeSet(BitSet(1)))
    val s2 = State.topState.copy(sf = State.topState.sf.copy(callStack = fr::Nil))
      .addTypeConstraint(pvy, BitTypeSet(BitSet(2)))
      .addTypeConstraint(pvy2, BitTypeSet(BitSet(1)))
    val res = stateSolver.canSubsume(s1,s2)
    assert(!res)

  }
  test("x -> p1 * p1.f -> p2 && p2:T1 can subsume x -> p2 * p2.f -> p1 && p1:T1"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val pvy = PureVar(1)
    val pvy2 = PureVar(2)

    val fr1 = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> pvy))
    val s1 = State.topState.copy(
      sf = State.topState.sf.copy(
        callStack = fr1::Nil,
        heapConstraints = Map(FieldPtEdge(pvy, "f") -> pvy2)
      ))
      .addTypeConstraint(pvy2, BitTypeSet(BitSet(1)))

    val fr2 = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> pvy2))
    val s2 = State.topState.copy(
      sf = State.topState.sf.copy(
        callStack = fr2::Nil,
        heapConstraints = Map(FieldPtEdge(pvy2, "f") -> pvy)
      ))
      .addTypeConstraint(pvy, BitTypeSet(BitSet(1)))
//      .addTypeConstraint(pvy, BitTypeSet(BitSet(1)))
    val res = stateSolver.canSubsume(s1,s2)
    assert(res)
  }
  test("x -> p1 * p1.f -> p2 && p2:T1 cannot subsume x -> p2 * p2.f -> p1 && p1:T2"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val pvy = PureVar(1)
    val pvy2 = PureVar(2)
    val fr = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> pvy))
    val s1 = State.topState.copy(
      sf = State.topState.sf.copy(
        callStack = fr::Nil,
        heapConstraints = Map(FieldPtEdge(pvy, "f") -> pvy2)
      ))
      .addTypeConstraint(pvy2, BitTypeSet(BitSet(1)))
    val s2 = State.topState.copy(
      sf = State.topState.sf.copy(
        callStack = fr::Nil,
        heapConstraints = Map(FieldPtEdge(pvy2, "f") -> pvy)
      ))
      .addTypeConstraint(pvy, BitTypeSet(BitSet(2)))
    //      .addTypeConstraint(pvy, BitTypeSet(BitSet(1)))
    val res = stateSolver.canSubsume(s1,s2)
    assert(!res)
  }
  test("I(x.foo()) && I(z.bar(y)) cannot subsume I(x.foo())"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val iFoo_x = I(CBEnter, fooM, "x" :: Nil)
    val iBar_z = I(CBEnter, barM, "z"::"y" ::Nil)
    def s(t:Set[AbstractTrace]):State = {
      State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = t))
    }
    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    val s1 = s(Set(
      AbstractTrace(iFoo_x, Nil, Map("x" -> pv1)),
      AbstractTrace(iBar_z, Nil, Map("z" -> pv2))
    ))
    val s2 = s(Set(
      AbstractTrace(iFoo_x, Nil, Map("x" -> pv1))
    ))
    val res = stateSolver.canSubsume(s1,s2)
    assert(!res)

    val res2 = stateSolver.canSubsume(s2,s1)
    assert(res2)


  }
  test("/*I(x.foo()) && */ (Not I(y.bar())) && /*x:T1 &&*/ y:T2 cannot subsume I(x.foo()) && x:T1 && y:T2"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val iFoo_x = I(CBEnter, fooM, "x"::Nil)
    val iBar_z = I(CBEnter, barM, "z"::Nil)
    def s(t:Set[AbstractTrace]):State = {
      State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = t))
    }
    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    val s1 = s(Set(
//      AbstractTrace(iFoo_x, Nil, Map("x" -> pv1)),
      AbstractTrace(Not(iBar_z), Nil, Map("z" -> pv2))
    )).addTypeConstraint(pv2,BitTypeSet(BitSet(2)))//.addTypeConstraint(pv1,BitTypeSet(BitSet(1)))
    val s2 = s(Set(
      AbstractTrace(iFoo_x, Nil, Map("x" -> pv1))
    )).addTypeConstraint(pv1,BitTypeSet(BitSet(1)))
      .addTypeConstraint(pv2,BitTypeSet(BitSet(2)))
    val res = stateSolver.canSubsume(s1,s2)
    assert(!res)

    //TODO: add back in

//    val res2 = stateSolver.canSubsume(s2,s1)
//    assert(res2)
  }
  test("NI(x.foo(),x.baz()) && (not I(z.bar())) && x:T2 && z:T1 cannot subsume NI(x.foo(),x.baz()) && x:T2"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val bazM = SubClassMatcher("","baz","baz")
    val iFoo_x = I(CBEnter, fooM, "x"::Nil)
    val iBaz_x = I(CBEnter, bazM, "x"::Nil)
    val iBar_z = I(CBEnter, barM, "z"::Nil)

    def s(t:Set[AbstractTrace]):State = {
      State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = t))
    }
    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    val niFooBaz_x = AbstractTrace(NI(iFoo_x, iBaz_x), Nil, Map("x" -> pv1))
    val s1 = s(Set(
      niFooBaz_x,
      AbstractTrace(Not(iBar_z), Nil, Map("z" -> pv2))
    )).addTypeConstraint(pv1,BitTypeSet(BitSet(1))).addTypeConstraint(pv2,BitTypeSet(BitSet(2)))
    val s2 = s(Set(
      niFooBaz_x
    )).addTypeConstraint(pv1,BitTypeSet(BitSet(1))).addTypeConstraint(pv2,BitTypeSet(BitSet(2)))
    val res = stateSolver.canSubsume(s1,s2)
    assert(!res)

    val res2 = stateSolver.canSubsume(s2,s1)
    assert(res2)
  }
  test("I(x.foo(y)) can subsume I(x1.foo(y1)) && not ref(z)"){ f =>
    //TODO: implement this test, figure out what it means
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
    //    val iFoo_x_y = I(CBEnter, fooM, "x" :: "y" :: Nil)
    //    val iFoo_x1_y1 = I(CBEnter, fooM, "x1"::"y1" :: Nil)

    val iFoo_x_y = I(CBEnter, fooM, "x"::"y" :: Nil)
    val iFoo_x1_y1 = I(CBEnter, fooM, "x1"::"y1" :: Nil)


    val pvy = PureVar(1)
    val pvy2 = PureVar(2)
    val pvy3 = PureVar(3)

    def s(t:Set[AbstractTrace]):State = {
      State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = t))
    }
    val t1 = AbstractTrace(iFoo_x_y,Nil, Map("y"-> pvy))
    val t2 = AbstractTrace(iFoo_x1_y1, Nil, Map("y1" -> pvy2))
    val t3 = AbstractTrace(Not(Ref("Z")), Nil, Map("Z" -> pvy3))
    val s1 = s(Set(t1))
    val s2 = s(Set(t2,t3))
    val res = stateSolver.canSubsume(s1,s2)
    assert(res)

    val res2 = stateSolver.canSubsume(s2,s1)
    assert(!res2)
  }
  test("I(x.foo(y)) && y:T1 cannot subsume I(x1.foo(y1))"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
//    val iFoo_x_y = I(CBEnter, fooM, "x" :: "y" :: Nil)
//    val iFoo_x1_y1 = I(CBEnter, fooM, "x1"::"y1" :: Nil)

    val iFoo_x_y = I(CBEnter, fooM, "y" :: Nil)
    val iFoo_x1_y1 = I(CBEnter, fooM, "y1" :: Nil)


    val pvy = PureVar(1)
    val pvy2 = PureVar(2)
    val pvy3 = PureVar(3)

    def s(t:AbstractTrace):State = {
      State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = Set(t)))
    }
    val t1 = AbstractTrace(iFoo_x_y,Nil, Map("y"-> pvy))
    val t2 = AbstractTrace(iFoo_x1_y1, Nil, Map("y1" -> pvy2))
    val s1 = s(t1).addTypeConstraint(pvy, BitTypeSet(BitSet(1)))
    val s2 = s(t2).addTypeConstraint(pvy3, BitTypeSet(BitSet(1)))
      .addTypeConstraint(pvy2,BitTypeSet(BitSet(2)))
    val res = stateSolver.canSubsume(s1,s2)
    assert(!res)
  }
  test("I(x.foo(y)) && y:T1 cannot subsume I(x.foo(y))|>I(x1.foo(y1)) && I(x2.foo(y2)) && y2:T2"){f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
    val iFoo_x_y = I(CBEnter, fooM, "x" :: "y" :: Nil)
    val iFoo_x1_y1 = I(CBEnter, fooM, "x1"::"y1" :: Nil)
    val iFoo_x2_y2 = I(CBEnter, fooM, "x2"::"y2" :: Nil)
    def s(t:Set[AbstractTrace]):State = {
      State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = t))
    }
    val pvy = PureVar(1)
    val pvy2 = PureVar(2)
    //I(x.foo(y)) && y:T1
    val s1 = s(Set(AbstractTrace(iFoo_x_y, Nil, Map("y"->pvy)))).addTypeConstraint(pvy, BitTypeSet(BitSet(1)))

    //I(x.foo(y))|>I(x1.foo(y1)) && I(x2.foo(y2)) && y:T1 && y2:T2
    //"y"->pvy, "y2"->pvy2
    val t2 = AbstractTrace(iFoo_x_y, iFoo_x1_y1::Nil,Map("y"->pvy))
    val t3 = AbstractTrace(iFoo_x2_y2,Nil,Map("y2"->pvy2))
    // add y:T1 && y2:T2
//    val s2 = s(Set(t3))
    val s2 = s(Set(t2,t3))
      .addTypeConstraint(pvy2, BitTypeSet(BitSet(2)))
      .addTypeConstraint(pvy, BitTypeSet(BitSet(1)))
    val res = stateSolver.canSubsume(s1,s2)
    assert(!res)
  }
  test("I(x.foo()) && I(x.bar()) |> y.foo() cannot subsume I(x.foo()) && I(x.bar()) |> y.bar()") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    // I(x.foo()) && I(x.bar())
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val iFoo = I(CBEnter, fooM, "a" :: Nil)
    val iBar = I(CBEnter, barM, "a" :: Nil)
    val iFoo_b = I(CBEnter, fooM, "b" :: Nil)
    val iBar_b = I(CBEnter, barM, "b" :: Nil)
    val foobar = And(iFoo,iBar)
    def s(t:AbstractTrace):State = {
      State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = Set(t)))
    }
    val followsFoo = AbstractTrace(foobar, iFoo_b::Nil,Map())
    val followsBar = AbstractTrace(foobar, iBar_b::Nil, Map())
    val res = stateSolver.canSubsume(s(followsFoo),s(followsBar))
    assert(!res)

    // a: I(v = findView(a)) && NI( onDestroy(a) , onCreate(a))
    val fv = SubClassMatcher("","findView","findView")
    val de = SubClassMatcher("","onDestroy","onDestroy")
    val cr = SubClassMatcher("","onCreate","onCreate")
    val findView = I(CIExit, fv, "v"::"a"::Nil)
    val onDestroy = I(CBExit, de, "_"::"a"::Nil)
    val onCreate = I(CBEnter, cr, "_"::"a"::Nil)
    val a = And(findView, NI(onDestroy, onCreate))

    val subsumer = AbstractTrace(a, I(CBEnter, cr, "_"::"b"::Nil)::
      I(CIExit,fv,"v"::"b"::Nil)::Nil,Map())

    val subsumee = AbstractTrace(a, I(CBExit,de,"_"::"b"::Nil)::Nil,Map())
    val res2 = stateSolver.canSubsume(s(subsumer),s(subsumee))
    assert(!res2)
    val res3 = stateSolver.canSubsume(s(subsumee), s(subsumer))
    assert(res3)
  }
  test("Subsumption of unrelated trace constraint") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())


    val ifooa = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ifoob = I(CBEnter, Set(("", "foo")), "b" :: Nil)
    val state0 = State.topState.copy(sf = State.topState.sf.copy(
      traceAbstraction = Set(AbstractTrace(ifooa, Nil, Map("a"->p1)))
    ))
    val state1 = State.topState.copy(sf = State.topState.sf.copy(
      pureFormula = Set(PureConstraint(p1, NotEquals, p2)),
      traceAbstraction = Set(AbstractTrace(ifooa, ifoob::Nil, Map("a"->p1, "b"->p2)))
    ))
    assert(stateSolver.canSubsume(state0,state1, Some(2)))
  }
  test("Subsumption of multi arg abstract traces") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)


    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")), "a"::"b":: Nil)
    val niSpec = NI(ibar,ifoo)
    val state = State.topState.copy(sf = State.topState.sf.copy(
      traceAbstraction = Set(AbstractTrace(ibar, Nil, Map()))))
    assert(stateSolver.canSubsume(state,state, Some(2)))
  }

  test("Subsumption of abstract trace where type info creates disalias") { f =>
    val (stateSolver,cha) = getStateSolver(SolverTypeSolving)

    val p1 = PureVar(State.getId_TESTONLY())
    val p1t = BoundedTypeSet(Some("String"), None, Set())
    val p2 = PureVar(State.getId_TESTONLY())
    val p2t = BoundedTypeSet(Some("Foo"), None, Set())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    assert(p1t.intersect(p2t).isEmpty)


    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ifoob = I(CBEnter, Set(("", "foo")), "b" :: Nil)
    val state = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = Set(AbstractTrace(ifoo, Nil, Map("a"->p1)))))
    val state2 = State.topState.copy(sf = State.topState.sf.copy(
      traceAbstraction = Set(AbstractTrace(ifoo, ifoob::Nil, Map("a"->p1, "b"->p2))),
//      pureFormula = Set(PureConstraint(p1, NotEquals, p2)) // this constraint is enforced by the type constraints below
      typeConstraints = Map(p1 -> p1t, p2->p2t)
    ))
    assert(stateSolver.canSubsume(state,state2, Some(2)))
  }

  test("Refute trace with multi arg and multi var (bad arg fun skolemization caused bug here)") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val p1 = PureVar(State.getId_TESTONLY())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val ifoo = I(CBEnter, Set(("", "foo")),  "_"::"a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")),  "_"::"a" :: Nil)
    val ibarc = I(CBEnter, Set(("", "bar")), "_"::"c" :: Nil)

    val at = AbstractTrace(NI(ifoo,ibar), ibarc::Nil, Map("a"->p1, "c"->p1))
    val state = State(StateFormula(
      CallStackFrame(dummyLoc, None, Map(StackVar("x") -> p1)) :: Nil, Map(), Set(),Map(), Set(at)), 0)
    val res = stateSolver.simplify(state)
    assert(res.isEmpty)
  }
  test("Subsumption of pure formula including type information"){ f =>
    val (stateSolver,_) = getStateSolver(SolverTypeSolving)
    // (x->p1 && p1 <: Object) can not be subsumed by (x->p1 && p1 <:Foo)
    val p1 = PureVar(State.getId_TESTONLY())
    val state_ = state.copy(sf = state.sf.copy(
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("Foo"),None,Set())),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    val state__ = state.copy(sf = state.sf.copy(
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("java.lang.Object"),None,Set())),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
//    val state__ = state.copy(pureFormula = Set(PureConstraint(p1,TypeComp,SubclassOf("java.lang.Object"))))
    assert(!stateSolver.canSubsume(state_, state__))

    val p2 = PureVar(State.getId_TESTONLY())
    // (x->p1 &&  p1 <: Foo && p1 == p2) can be subsumed by (x->p1 &&  p2 <: Object && p1 == p2)
    val state1_ = state.copy(sf = state.sf.copy(
      pureFormula = Set(PureConstraint(p1, Equals, p2)),
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("Foo"),None,Set())),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    val state1__ = state.copy(sf = state.sf.copy(
      pureFormula = Set(PureConstraint(p1, Equals, p2)),
      typeConstraints = Map(p2 -> BoundedTypeSet(Some("java.lang.Object"),None,Set())),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    assert(stateSolver.canSubsume(state1__, state1_))
    assert(!stateSolver.canSubsume(state1_, state1__))

    // (x->p1 && p1 <: Foo) can be subsumed by (x->p1 && p1 <:Object)
    assert(stateSolver.canSubsume(state__, state_))
    assert(stateSolver.canSubsume(state_, state_))

    // Combine type constraints and trace constraints
    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val formula = AbstractTrace(NI(ifoo,ibar),Nil, Map("a"->p1))
    val state2_ = state_.copy(sf = state_.sf.copy(
      traceAbstraction = Set(formula),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    val state2__ = state__.copy(sf = state__.sf.copy(
      traceAbstraction = Set(formula),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    assert(stateSolver.canSubsume(state2__, state2_))
    assert(!stateSolver.canSubsume(state2_, state2__))
  }
  test("Subsumption of pure formula in states"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val state = State(
      StateFormula(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil, Map(),Set(),Map(),Set()),0)

    // x->p1 * y->p2 can be subsumed by x->p1
    val state_x_y = state.copy(sf = state.sf.copy(
      callStack = CallStackFrame(dummyLoc,None,Map(
        StackVar("x") -> p1,
        StackVar("y") -> p2
      ))::Nil,
      pureFormula = Set(PureConstraint(p1, NotEquals, p2))
    ))
    assert(stateSolver.canSubsume(state,state_x_y))
    assert(!stateSolver.canSubsume(state_x_y,state))

  }

  test("Trace contained in abstraction") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    implicit val zCTX: Z3SolverCtx = stateSolver.getSolverCtx

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
    assert(stateSolver.traceInAbstraction(
      state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(i_foo_x,Nil, Map())))),
      trace))

    // I(x.foo()) ! models empty
    assert(!stateSolver.traceInAbstraction(
      state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(i_foo_x,Nil,Map())))),
      Nil))

    // not I(x.foo()) models empty
    assert(stateSolver.traceInAbstraction(
      state = state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(Not(i_foo_x), Nil, Map())))),
      trace = Nil
    ))

    // not I(x.foo()) or I(x.bar()) models empty
    assert(stateSolver.traceInAbstraction(
      state = state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(Or(Not(i_foo_x), i_bar_x), Nil,
        Map())))),
      trace = Nil
    ))

//    // not I(x.foo()) or I(x.bar()) ! models @1.foo()
//    assert(!stateSolver.traceInAbstraction(
//      state = state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(Or(Not(i_foo_x), i_bar_x), Nil,
//        Map())))),
//      trace = TMessage(CIEnter, foo, TAddr(1)::Nil)::Nil
//    )) //TODO:=============== decide if negation can just be for things that are already grounded by other terms

    // empty ! models NI(x.foo(), x.bar())
    assert(!stateSolver.traceInAbstraction(
      state.copy(state.sf.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x,Nil,Map())))),
      Nil))

    // NI(x.foo(), x.bar()) ! models @1.foo();@1.bar()
    assert(!
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x, Nil,Map())))),
        trace
      ))

    // empty(trace) models NI(x.foo(),x.bar()) |> x.foo()
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x, i_foo_x::Nil,Map())))),
        Nil
      ))
    // NI(x.foo(),x.bar()) |> x.foo() models @1.bar()
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x, i_foo_x::Nil,Map())))),
        TMessage(CIEnter, bar, TAddr(1)::Nil)::Nil
      ))
    // NI(x.foo(),x.bar()) |> x.foo() models @1.foo();@1.bar()
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x, i_foo_x::Nil,Map())))),
        trace
      ))

    // NI(x.foo(),x.bar()) |> x.bar() ! models empty
    assert(
      !stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(ni_foo_x_bar_x, i_bar_x::Nil,Map())))),
        Nil
      ))

    // Not NI(x.foo(), x.bar())  models @1.foo();@1.bar()
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(Not(ni_foo_x_bar_x), Nil,Map())))),
        trace
      ))

    // I(foo(x,y)) models foo(@1,@2)
    val i_foo_x_y = I(CIEnter, Set(("foo",""),("foo2","")), "X"::"Y"::Nil)
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(i_foo_x_y,Nil,Map())))),
        trace = TMessage(CIEnter, foo, TAddr(1)::TAddr(2)::Nil)::Nil
      )
    )


//    // not I(foo(x,y)) !models foo(@1,@2)
//    assert( //TODO:===============
//      !stateSolver.traceInAbstraction(
//        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(Not(i_foo_x_y),Nil,Map())))),
//        trace = TMessage(CIEnter, foo, TAddr(1)::TAddr(2)::Nil)::Nil
//      )
//    )

    // I(foo(y,y) !models foo(@1,@2)
    val i_foo_y_y = I(CIEnter, Set(("foo",""),("foo2","")), "Y"::"Y"::Nil)
    assert(
      !stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(i_foo_y_y,Nil,Map("Y" -> PureVar(1)))))),
        trace = TMessage(CIEnter, foo, TAddr(1)::TAddr(2)::Nil)::Nil,
        debug = true
      )
    )

    // I(foo(y,y) models foo(@2,@2)
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(i_foo_y_y,Nil,Map())))),
        trace = TMessage(CIEnter, foo, TAddr(2)::TAddr(2)::Nil)::Nil
      )
    )

    //TODO: test "and", "scoped abstract traces"
  }

  private def getStateSolver(stateTypeSolving: StateTypeSolving = SetInclusionTypeSolving):
    (Z3StateSolver, ClassHierarchyConstraints) = {
    val pc = new ClassHierarchyConstraints(hierarchy,Set("java.lang.Runnable"),intToClass, stateTypeSolving)
    (new Z3StateSolver(pc),pc)
  }


  test("quantifier example") { f =>
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val foo1 = ctx.mkConst("foo", ctx.mkIntSort()).asInstanceOf[ArithExpr[_]]
    println(s"foo1: ${foo1}")
    val f = ctx.mkFuncDecl("f",ctx.mkIntSort(), ctx.mkBoolSort())
//    val expr: BoolExpr = ctx.mkIff(
//      f.apply(foo1).asInstanceOf[BoolExpr],
//      ctx.mkGt(foo1, ctx.mkInt(0)))
//    val a1 = ctx.mkForall(Array(foo1),expr, 1,
//      null,null,
//      null,null)
//    val a = ctx.mkExists(Array(foo1),expr, 1,
//      null,null,
//      null,null)
//    println(s"input:\n${a}")
//
//    solver.add(a)
//    solver.check()
//    val m = solver.getModel

//    println(s"model: \n${m}")
  }
  test("sandbox") { f =>
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

  test("sandbox2") { f =>
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val es = ctx.mkEnumSort("Foo", "Foo1", "Foo2")
    val foo2 = es.getConst(1)
    println(foo2)
//    solver.add(ctx.mkEq(foo2, ctx.mkSymbol("Foo2")))


    solver.check() match {
      case Status.UNSATISFIABLE => println("unsat")
      case Status.SATISFIABLE => println(solver.getModel)
      case Status.UNKNOWN => ???
    }

  }
}
