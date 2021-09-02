package edu.colorado.plv.bounder.solver

import better.files.Resource
import com.microsoft.z3._
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.{And, Forall, I, LSConstraint, LSFalse, LSSpec, LSTrue, LSVar, NI, Not, Or, Ref, SetSignatureMatcher, SignatureMatcher, SubClassMatcher}
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LifecycleSpec, RxJavaSpec, SpecSignatures, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state._
import org.scalatest.funsuite.FixtureAnyFunSuite
import upickle.default.{read, write}

import scala.collection.BitSet
import scala.language.implicitConversions

class Z3StateSolverTest extends FixtureAnyFunSuite {

  private val fooMethod = TestIRMethodLoc("","foo", List(Some(LocalWrapper("@this","Object"))))
  private val dummyLoc = CallbackMethodReturn(tgtClazz = "",
     fmwName="void foo()", fooMethod, None)
  private val v = PureVar(230)
  private val p1 = PureVar(1)
  private val p2 = PureVar(2)
  private val p3 = PureVar(3)
  private val frame = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> v))
  private val state = State.topState
  case class FixtureParam(typeSolving: StateTypeSolving)

  val esp = new SpecSpace(Set(), Set())
  def st(t:AbstractTrace):State = {
    State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = Set(t)))
  }

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

    val v2 = PureVar(2)
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal), PureConstraint(v2, Equals, NullVal))
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints,Map(),Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState, esp)
    assert(simplifyResult.isEmpty)

    val constraints2 = Set(PureConstraint(v2, NotEquals, IntVal(0)), PureConstraint(v2, Equals, IntVal(0)))
    val refutableState2 = refutableState.copy(sf = refutableState.sf.copy(pureFormula = constraints2))
    val simplifyResult2 = stateSolver.simplify(refutableState2, esp)
    assert(simplifyResult2.isEmpty)

    val constraints3 = Set(PureConstraint(v2, NotEquals, IntVal(0)), PureConstraint(v2, Equals, IntVal(1)))
    val refutableState3 = refutableState.copy(sf = refutableState.sf.copy(pureFormula = constraints3))
    val simplifyResult3 = stateSolver.simplify(refutableState3,esp)
    assert(simplifyResult3.isDefined)

  }
  test("alias") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val v2 = PureVar(2)
    val v3 = PureVar(3)
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal),
      PureConstraint(v3, Equals, NullVal))
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints + PureConstraint(v2, Equals, v3),Map(),Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState,esp)
    assert(!simplifyResult.isDefined)
  }
  test("Separate fields imply base must not be aliased a^.f->b^ * c^.f->b^ AND a^=c^ (<=> false)") { f=>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val v2 = PureVar(2)
    val v3 = PureVar(3)
    val v4 = PureVar(4)
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v, Equals, v2)),Map(), Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState,esp)
    assert(!simplifyResult.isDefined)

    // v3 and v4 on the right side of the points to can be aliased
    val unrefutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4),
        PureConstraint(v, NotEquals, v2)),Map(), Set()),0)
    val simplifyResult2 = stateSolver.simplify(unrefutableState,esp)
    assert(simplifyResult2.isDefined)

    // object field can point to self
    val unrefutableState2 = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4),
        PureConstraint(v, Equals, v4)),Map(), Set()),0)
    val simplifyResult3 = stateSolver.simplify(unrefutableState2,esp)
    assert(simplifyResult3.isDefined)
  }
  test("Transitive equality should be refuted by type constraints") { f=>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val v2 = PureVar(2)
    val v3 = PureVar(3)
    val v4 = PureVar(4)
    val refutableState = State(StateFormula(List(frame),
      Map(),
      Set(PureConstraint(v2, Equals, v3),PureConstraint(v3, Equals, v4)),
      Map(v2->BoundedTypeSet(Some("String"),None,Set()),
        //        v3->BoundedTypeSet(Some("String"),None,Set()),
        v4->BoundedTypeSet(Some("Foo"),None,Set())),
      Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState,esp)
    assert(!simplifyResult.isDefined)

    val refutableState2 = State(StateFormula(List(frame),
      Map(),
      Set(PureConstraint(v2, Equals, v3),PureConstraint(v3, Equals, v4), PureConstraint(v2, NotEquals, v4)),
      Map(),
      Set()),0)
    val simplifyResult2 = stateSolver.simplify(refutableState2,esp)
    assert(!simplifyResult2.isDefined)
  }
  test("test feasibility of constraints before GC") { f=>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val v2 = PureVar(2)
    val v3 = PureVar(3)
    val v4 = PureVar(4)
    val refutableState = State(StateFormula(List(frame),
      Map(),
      Set(PureConstraint(v2, Equals, v3),PureConstraint(v3, Equals, v4)),
      Map(v2->BoundedTypeSet(Some("String"),None,Set()),
        v3->BoundedTypeSet(Some("String"),None,Set()),v4->BoundedTypeSet(Some("Foo"),None,Set())),
      Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState,esp)
    assert(!simplifyResult.isDefined)

  }
  test("aliased object implies fields must be aliased refuted by type constraints") { f =>
    val (stateSolver,_) = getStateSolver(SolverTypeSolving)

    // aliased and contradictory types of field
    val v2 = PureVar(2)
    val v3 = PureVar(3)
    val v4 = PureVar(4)
    val constraints = Set(
      PureConstraint(v3, Equals, v4),
    )
    val typeC = Map(
      v3-> BoundedTypeSet(Some("String"),None,Set()),
      v4 -> BoundedTypeSet(Some("Foo"), None, Set())
    )
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3),constraints,typeC, Set()),0)
    val simplifyResult = stateSolver.simplify(refutableState,esp)
    assert(!simplifyResult.isDefined)

    // aliased and consistent field type constraints
    val constraints2 = Set(
      PureConstraint(v3, Equals, v4),
    )
    val typeC2 = Map(
      v3 -> BoundedTypeSet(Some("String"),None,Set()),
      v4 -> BoundedTypeSet(Some("java.lang.Object"),None,Set())
    )
    val state = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),constraints2,typeC2, Set()),0)
    val simplifyResult2 = stateSolver.simplify(state,esp)
    assert(simplifyResult2.isDefined)
  }
  test("Trace abstraction lsfalse is empty and lstrue is not"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val iFoo_ac = I(CBEnter, Set(("", "foo")), "c"::"a" :: Nil)
    val iFoo_bd = I(CBEnter, Set(("", "foo")), "d"::"b" :: Nil)
    val specSpace = new SpecSpace(Set(LSSpec("a"::"c"::Nil, Nil, LSFalse, iFoo_ac)))
    val absFalse = AbstractTrace(None, iFoo_bd::Nil, Map())
    val state = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = Set(absFalse)))
      .defineAllLS()
    val res = stateSolver.simplify(state,specSpace)
    assert(res.isEmpty)
    val specSpace2 = new SpecSpace(Set(LSSpec("a"::"c"::Nil, Nil, LSTrue, iFoo_ac)))
    val absTrue = AbstractTrace(None, iFoo_bd::Nil, Map())
    val stateTrue = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = Set(absTrue)))
      .defineAllLS()
    val resTrue = stateSolver.simplify(stateTrue,specSpace2)
    assert(resTrue.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) && a == p1 (<==>true)") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val iFoo_ac = I(CBEnter, Set(("", "foo")), "c"::"a" :: Nil)
    val iFoo_bd = I(CBEnter, Set(("", "foo")), "d"::"b" :: Nil)
    val iBar_a = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val iBaz_a = I(CBEnter, Set(("", "baz")), "a" :: Nil)
    val niBarBaz = NI(iBar_a,iBaz_a)
    val spec = new SpecSpace(Set(LSSpec("a"::"c"::Nil, Nil, niBarBaz, iFoo_ac)))

    // Lifestate atoms for next few tests
    val abs1 = AbstractTrace(iFoo_bd::Nil, Map("b"->p1, "d" -> p2))
    val state1 = State(StateFormula(Nil, Map(),Set(),Map(), Set(abs1)),0)
    val res1 = stateSolver.simplify(state1,spec)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) |> I(a.bar()) (<==>true)") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val iFoo_ac = I(CBEnter, Set(("", "foo")), "c"::"a" :: Nil)
    val iFoo_bd = I(CBEnter, Set(("", "foo")), "d"::"b" :: Nil)
    val iBar_a = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val iBar_e = I(CBEnter, Set(("", "bar")), "e" :: Nil)
    val iBaz_a = I(CBEnter, Set(("", "baz")), "a" :: Nil)
    val niBarBaz = NI(iBar_a,iBaz_a)
    val spec = new SpecSpace(Set(LSSpec("a"::"c"::Nil, Nil, niBarBaz, iFoo_ac)))

    // Lifestate atoms for next few tests
    val abs1 = AbstractTrace(iBar_e::iFoo_bd::Nil, Map("e"->p1,"b"->p1))
    val state1 = State(StateFormula(Nil, Map(),Set(),Map(), Set(abs1)),0).defineAllLS()
    val res1 = stateSolver.simplify(state1,spec)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val iBar_a = I(CBEnter, Set(("_", "bar")), "a" :: Nil)
    val iBaz_a = I(CBEnter, Set(("_", "baz")), "a" :: Nil)
    val iBaz_b = I(CBEnter, Set(("_", "baz")), "b" :: Nil)
    val iBaz_c = I(CBEnter, Set(("_", "baz")), "c" :: Nil)
    val tgt = I(CBEnter, Set(("_", "tgt")), "a"::Nil)

    // NI(a.bar(), a.baz())
    val niBarBaz = NI(iBar_a,iBaz_a)
    val spec = new SpecSpace(Set(LSSpec("a"::Nil, Nil, niBarBaz, tgt)))

    // NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)
    val abs1 = AbstractTrace(iBaz_b::tgt::Nil, Map("a"->p1, "b"->p1))
//    AbsAnd(AbsAnd(AbsFormula(niBarBaz), AbsEq("a",p1)), AbsEq("b",p1)),
    val state1 = State(StateFormula(Nil, Map(),Set(),Map(), Set(abs1)),0)
    val res1 = stateSolver.simplify(state1, spec)
    assert(res1.isEmpty)
    val res2 = stateSolver.witnessed(state1,spec)
    assert(!res2)
  }
  ignore("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) && a == p1 && c == p1 (<=> true)") { f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // NI(a.bar(),a.baz()) |> I(c.bar()) && a == p1 && c == p1 (<=> true)
    val abs2 = AbstractTrace(niBarBaz,i4::Nil, Map("a"->p1, "c"->p1) )
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(abs2)),0)
    val res2 = stateSolver.simplify(state2,esp)
    assert(res2.isDefined)
  }
  ignore("Trace abstraction NI(a.bar(),a.baz()) |> I(b.baz()) |> I(c.bar()) (<=> true) ") { f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // NI(a.bar(),a.baz()) |> I(c.bar()) ; i(b.baz()
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1, "c"->p1))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(niaa)),0)
    val res2 = stateSolver.simplify(state2,esp)
    assert(res2.isDefined)
  }
  ignore("Trace abstraction NI(a.bar(),a.baz()) ; I(c.bar()) ; I(b.baz()) && a = b = c (<=> false) ") { f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // NI(a.bar(),a.baz()) |> I(a.bar());I(a.baz())
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1, "c"->p1, "b"->p1))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(niaa)),0)
    val res2 = stateSolver.simplify(state2,esp)
    assert(res2.isEmpty)
  }
  ignore("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = c (<=> true) ") { f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // NI(a.bar(),a.baz()) |> I(c.bar()) ; I(b.baz())
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1, "c"->p1, "b"->p2))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(niaa)),0)
    val res2 = stateSolver.simplify(state2,esp)
    assert(res2.isDefined)
  }
  ignore("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = b (<=> false) ") { f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val b_baz = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val c_bar = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i, i2)

    // NI(a.bar(),a.baz()) |> I(c.bar()) |> i(b.baz()
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map("a"->p1,"b"->p1, "c"->p2))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(niaa)),0)
    val res2 = stateSolver.simplify(state2,esp)
    assert(res2.isEmpty)
  }
  ignore("Trace abstraction NI(a.bar(),a.baz()) |> I(a.bar()),  NI(a.foo(),a.baz()) |> I(a.foo()) (<=> true) ") { f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibaz = I(CBEnter, Set(("", "baz")), "a" :: Nil)
    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val t1 = AbstractTrace(NI(ibar,ibaz), ibar::Nil, Map())
    val t2 = AbstractTrace(NI(ifoo,ibaz), ifoo::Nil, Map())
    val s = state.copy(sf = state.sf.copy(traceAbstraction = Set(t1,t2)))
    val res = stateSolver.simplify(s,esp)
    assert(res.isDefined)
  }

  ignore("( (Not I(a.bar())) && (Not I(a.baz())) ) |> I(b.bar()) && a=pv1 && b = pv1,  (<=>false) ") { f =>
    //TODO: |>
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
    val res = stateSolver.simplify(s1,esp)
    assert(res.isEmpty)

    //( (Not I(a.bar())) && (Not I(a.baz())) ) |> I(b.bar()) && a = pv1 && b = pv1
    val t2 = AbstractTrace(And(Not(ibar_a), Not(ibaz_a)), ibar_b::Nil, Map())
      .addModelVar("a",pv1).addModelVar("b",pv1)
    val s2 = state.copy(sf = state.sf.copy(traceAbstraction = Set(t2)))
    val res2 = stateSolver.simplify(s2,esp)
    assert(res2.isEmpty)
  }
  ignore("Not witnessed: I(a.foo()) |> b.foo() && Not(I(b.bar())) |> a.bar() && a = pv1 && b = pv2") { f =>
    //TODO: |>
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
    val res = stateSolver.witnessed(s1,esp)
    assert(!res)

    // t1 is witnessed
    val s2 = state.copy(sf = state.sf.copy(traceAbstraction = Set(t1)))
    val res2 = stateSolver.witnessed(s2,esp)
    assert(res2)
  }
  ignore("Not feasible: Not(I(a.foo(_)))) |> b.foo(c) && a=p1 && b = p3 && c = p2 && p1 = p3") {f=>
    //TODO: |>
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

    val isFeas = stateSolver.simplify(s1,esp)
    assert(isFeas.isEmpty)

    val isWit = stateSolver.witnessed(s1,esp)
    assert(!isWit)
  }
  ignore("Not I(a.foo) |> a.foo does not contain empty trace"){ f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    implicit val zctx = stateSolver.getSolverCtx

    // Lifestate atoms for next few tests
    val foo_a = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val foo_b = I(CBEnter, Set(("", "foo")), "b" :: Nil)
    val bar_a = I(CBEnter, Set(("", "bar")), "a" :: Nil)

    val niaa = AbstractTrace(Not(foo_a), foo_b::Nil, Map("a"->p1, "b"->p2))
    val state = State(StateFormula(Nil,Map(),Set(PureConstraint(p1, Equals, p2)),Map(), Set(niaa)),0)
    val contains = stateSolver.traceInAbstraction(state,esp, Nil )
    assert(!contains)

    val niaa2 = AbstractTrace(Or(Not(foo_a),bar_a), foo_b::Nil, Map("a"->p1))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), Set(niaa2)),0)
    val simpl = stateSolver.simplify(state2,esp)
    assert(simpl.isDefined)
    val contains2 = stateSolver.traceInAbstraction(state2,esp, Nil)
    assert(contains2)
  }


  test("refuted: I(a.foo()) |> Ref(a)"){ f =>
    // a.foo() must be invoked before a is created
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    implicit val zctx = stateSolver.getSolverCtx

    // Lifestate atoms for next few tests
    val foo_a = I(CBEnter, Set(("", "foo")), "a":: "c" :: Nil)
    val tgt_a = I(CBEnter, Set(("", "tgt")), "a":: "c" :: Nil)
    val spec = new SpecSpace(Set(LSSpec("a"::"c"::Nil, Nil, foo_a, tgt_a)))

    val at = AbstractTrace(tgt_a::Ref("b")::Nil, Map("a"->p1, "b" -> p2, "c"->p3))
    val state = State(StateFormula(Nil,Map(),
      Set(PureConstraint(p1, Equals, p2)),Map(), Set(at)),0)
    val res = stateSolver.simplify(state,spec)
    assert(res.isEmpty)

    val state0 = state.copy(sf =
      state.sf.copy(pureFormula = Set(PureConstraint(p1, NotEquals, p2))))
    val res0 = stateSolver.simplify(state0,spec)
    assert(res0.isDefined)

    val state1 = state.copy(sf =
      state.sf.copy(pureFormula = Set()))
    val res1 = stateSolver.simplify(state1,esp)
    assert(res1.isDefined)
  }

  ignore("Vacuous NI(a,a) spec") { f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "b" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBar = NI(i, i)

    // pure vars for next few tests
    //NI(a.bar(),a.bar()) (<=> true)
    // Note that this should be the same as I(a.bar())
    val nia = AbstractTrace(niBarBar, Nil, Map())
    val res0 = stateSolver.simplify(state.copy(sf = state.sf.copy(traceAbstraction = Set(nia))),esp)
    assert(res0.isDefined)

    //NI(a.bar(),a.bar()) |> I(b.bar()) && a = b (<=> true)
    val niaa = AbstractTrace(niBarBar, i4::Nil, Map("a"->p1,"b"->p1))
    val res1 = stateSolver.simplify(state.copy(sf = state.sf.copy(traceAbstraction = Set(niaa))),esp)
    assert(res1.isDefined)
  }
  test("Subsumption of stack"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val state = State(StateFormula(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil,
      Map(),Set(),Map(),Set()),0)
    val state_ = state.copy(sf = state.sf.copy(callStack = CallStackFrame(dummyLoc, None, Map(
      StackVar("x") -> p1,
      StackVar("y") -> p2
    ))::Nil))
    assert(stateSolver.canSubsume(state,state_,esp))
    assert(!stateSolver.canSubsume(state_,state,esp))

  }
  test("Subsumption of abstract traces") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val state = State(StateFormula(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil,
      Map(),Set(),Map(),Set()),0)
    val state2 = state.copy(sf = state.sf.copy(callStack =
      state.callStack.head.copy(locals=Map(StackVar("x") -> p1, StackVar("y")->p2))::Nil))
    assert(stateSolver.canSubsume(state,state,esp))
    assert(stateSolver.canSubsume(state,state2,esp))
    assert(!stateSolver.canSubsume(state2,state,esp))

    val iFoo_a = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val iBaz_a = I(CBEnter, Set(("", "baz")), "a" :: Nil)
    val iBaz_b = I(CBEnter, Set(("", "baz")), "b" :: Nil)
    val iBar_a = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val iBar_c = I(CBEnter, Set(("", "bar")), "c" :: Nil)
    val iFoo_c = I(CBEnter, Set(("", "foo")), "c" :: Nil)

    val spec = new SpecSpace(Set(LSSpec("a"::Nil, Nil, iFoo_a, iBaz_a)))

    val baseTrace1 = AbstractTrace(iBaz_b::Nil, Map("b"->p1))
    val arrowTrace1 = AbstractTrace(iBar_c::iBaz_b::Nil, Map("b"->p1, "c"->p2))
    val state_ = state.copy(sf = state.sf.copy(traceAbstraction = Set(baseTrace1)))
    val state__ = state.copy(sf = state.sf.copy(traceAbstraction = Set(arrowTrace1)))

    // State I(a.foo())|>empty should subsume itself

    assert(stateSolver.canSubsume(state_,state_,spec))
    // I(a.foo()) can subsume I(a.foo()) |> a.bar()
    assert(stateSolver.canSubsume(state_,state__,spec))

    val spec2 = new SpecSpace(Set(LSSpec("a"::Nil, Nil, NI(iFoo_a,iBar_a), iBaz_a)))
    val baseTrace = AbstractTrace( iBaz_b::Nil, Map("b"->p1))
    val state3_ = state.copy(sf = state.sf.copy(traceAbstraction = Set(baseTrace)))

    // NI(a.foo(), a.bar()) can subsume itself
    val res = stateSolver.canSubsume(state3_, state3_,spec2)
    assert(res)

    val state3__ = state.copy(sf = state.sf.copy(traceAbstraction =
      Set(AbstractTrace( iBar_c::iBaz_b::Nil, Map("b"->p1))))).defineAllLS()
    // NI(a.foo(), a.bar()) can subsume NI(a.foo(), a.bar()) |> c.bar()
    assert(stateSolver.canSubsume(state3_,state3__,spec2))

    // NI(a.foo(), a.bar()) cannot subsume NI(a.foo(), a.bar()) |> c.foo() /\ a==c
    // ifooc::Nil
    val fooBarArrowFoo = state.copy(sf = state.sf.copy(
      traceAbstraction = Set(AbstractTrace(iFoo_c::iBaz_b::Nil, Map("b"->p1, "c"->p1)))))
    val resfoobarfoo = stateSolver.canSubsume(state3_, fooBarArrowFoo,spec2)
    assert(!resfoobarfoo)

    val iZzz_a = I(CBEnter, Set(("", "zzz")), "a" :: Nil)
    val iZzz_d = I(CBEnter, Set(("", "zzz")), "d" :: Nil)
    val spec3 = new SpecSpace(Set(
      LSSpec("a"::Nil, Nil, NI(iFoo_a,iBar_a), iBaz_a),
      LSSpec("a"::Nil, Nil, iFoo_a, iZzz_a)
    ))

    // NI(a.foo(), a.bar()) /\ I(a.foo()) should be subsumed by NI(a.foo(),a.bar())
    val s_foo_bar_foo = state.copy(sf = state.sf.copy(traceAbstraction =
      Set(AbstractTrace(iBaz_b::iZzz_d::Nil, Map("b"->p1, "d"->p1)))))
    val s_foo_bar = state.copy(sf = state.sf.copy(traceAbstraction =
      Set(AbstractTrace(iBaz_b::Nil, Map("b"->p1, "d"->p1)))))
    assert(stateSolver.canSubsume(s_foo_bar, s_foo_bar_foo,spec3))

    // Extra trace constraint does not prevent subsumption
    // NI(foo(a),bar(a)), I(foo(c))  can subsume  NI(foo(a),bar(a))
    val res2 = stateSolver.canSubsume(s_foo_bar_foo, s_foo_bar,spec3)
    assert(res2)

    // NI(foo(a),bar(a)), I(foo(c)) /\ a!=c cannot subsume  NI(foo(a),bar(a))
    val s_foo_bar_foo_notEq = state.copy(sf = state.sf.copy(traceAbstraction =
      Set(AbstractTrace(iBaz_b::iZzz_d::Nil, Map("b"->p1, "d"->p2))),
      pureFormula = Set(PureConstraint(p1, NotEquals, p2))
    ))

    val res3 = stateSolver.canSubsume(s_foo_bar_foo_notEq, s_foo_bar,spec3)
    assert(!res3)

    // Extra pure constraints should not prevent subsumption
    val fewerPure = State.topState.copy(sf = State.topState.sf.copy(
      pureFormula = Set(PureConstraint(p2, NotEquals, NullVal))))
    val morePure = fewerPure.copy(sf = fewerPure.sf.copy(pureFormula = fewerPure.pureFormula +
//      PureConstraint(p1, TypeComp, SubclassOf("java.lang.Object")) +
      PureConstraint(p1, NotEquals, p2),
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("java.lang.Object"),None,Set()))))
    assert(stateSolver.canSubsume(fewerPure, morePure,esp))

  }
  test("NI(foo(x),bar(x)) cannot subsume I(foo(x))"){ f =>
    //TODO: this test shows an encoding of state subsumption that is not provably in the EPR fragment of logic
    val (stateSolver, _) = getStateSolver(f.typeSolving)
    val pv = PureVar(1)
    def s(t:Set[AbstractTrace]):State = {
      State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = t))
    }
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val zzzM = SubClassMatcher("","zzz","zzz")
    val yyyM = SubClassMatcher("","yyy","yyy")
    val iFoo_x = I(CBEnter, fooM, "x":: Nil)
    val iBar_x = I(CBEnter, barM, "x"::Nil)
    val iZzz_x = I(CBEnter, zzzM, "x"::Nil)
    val iZzz_y = I(CBEnter, zzzM, "y"::Nil)
    val iYyy_x = I(CBEnter, yyyM, "x"::Nil)
    val iYyy_y = I(CBEnter, yyyM, "y"::Nil)
    val spec = new SpecSpace(Set(
      LSSpec("x"::Nil, Nil, NI(iFoo_x, iBar_x),iZzz_x),
      LSSpec("x"::Nil, Nil, iFoo_x, iYyy_x)
    ))
    val at1 = AbstractTrace( iZzz_y::Nil, Map("y"-> pv))
    val at2 = AbstractTrace(iYyy_y::Nil, Map("y"-> pv))
    val res = stateSolver.canSubsume(s(Set(at1)),s(Set(at2)),spec)
    assert(!res)
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
    val res = stateSolver.canSubsume(s1,s2,esp)
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
    val res = stateSolver.canSubsume(s1,s2,esp)
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
    val res = stateSolver.canSubsume(s1,s2,esp)
    assert(!res)
  }
  test("I(x.foo()) && I(z.bar(y)) cannot subsume I(x.foo())"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val yyyM = SubClassMatcher("","bar","yyy")
    val zzzM = SubClassMatcher("","bar","zzz")
    val iFoo_x = I(CBEnter, fooM, "x" :: Nil)
    val iBar_zy = I(CBEnter, barM, "z"::"y" ::Nil)
    val iYyy_x = I(CBEnter, yyyM, "x"::Nil)
    val iYyy_k = I(CBEnter, yyyM, "k"::Nil)
    val iZzz_z = I(CBEnter, zzzM, "z"::Nil)
    val iZzz_j = I(CBEnter, zzzM, "j"::Nil)
    val spec = new SpecSpace(Set(
      LSSpec("x"::Nil, Nil, iFoo_x, iYyy_x),
      LSSpec("z"::Nil, "y"::Nil, iBar_zy, iZzz_z)
    ))

    def s(t:Set[AbstractTrace]):State = {
      State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = t))
    }
    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    val s1 = s(Set(
      AbstractTrace(iYyy_k::iZzz_j::Nil, Map("k" -> pv1, "j"->pv2)),
    ))
    val s2 = s(Set(
      AbstractTrace(iYyy_k::Nil, Map("k" -> pv1))
    ))

    val res = stateSolver.canSubsume(s1,s2,spec)
    assert(!res)

    val res2 = stateSolver.canSubsume(s2,s1,spec)
    assert(res2)
  }
  test("I(y.foo()) && (Not I(y.bar())) && y:T2 cannot subsume I(x.foo()) && x:T2"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val iFoo_x = I(CBEnter, fooM, "x"::Nil)
    val iFoo_z = I(CBEnter, fooM, "z"::Nil)
    val iBar_z = I(CBEnter, barM, "z"::Nil)
    val notbar_tgt_z = I(CBEnter, SubClassMatcher("","notbar_tgt","notbar_tgt"), "z"::Nil)
    val foo_tgt_x = I(CBEnter, SubClassMatcher("","foo_tgt","foo_tgt"), "x"::Nil)
    val spec = new SpecSpace(Set(
      LSSpec("z"::Nil, Nil, And(iFoo_z,Not(iBar_z)), notbar_tgt_z),
      LSSpec("x"::Nil, Nil, iFoo_x, foo_tgt_x)
    ))
    val s1 = st(
      AbstractTrace(notbar_tgt_z::Nil, Map("z" -> p2))
    ).addTypeConstraint(p2,BitTypeSet(BitSet(2)))//.addTypeConstraint(p1,BitTypeSet(BitSet(1)))
    val s2 = st(
      AbstractTrace(foo_tgt_x::Nil, Map("x" -> p1))
    ).addTypeConstraint(p1,BitTypeSet(BitSet(2)))
//      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))
    val res = stateSolver.canSubsume(s1,s2,spec)
    assert(!res)

    // I(x.foo()) && x:T2 can subsume I(y.foo()) && (Not I(y.bar())) && y:T2

    val res2 = stateSolver.canSubsume(s2,s1, spec)
    assert(res2)
  }
  test("|>tgt(x) can be subsumed by |>"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val tgtM = SubClassMatcher("","tgt","tgt")
    val iFoo_x = I(CBEnter, fooM, "x"::Nil)
    val iBar_x = I(CBEnter, barM, "x"::Nil)
    val iTgt_x = I(CBEnter, tgtM, "x"::Nil)
    val spec = new SpecSpace(Set(
      LSSpec("x"::Nil, Nil, NI(iFoo_x, iBar_x), iTgt_x)
    ))
    val s1 = st(AbstractTrace(iTgt_x::Nil, Map("x"->p1)))
      .addTypeConstraint(p1,BitTypeSet(BitSet(1)))
    val s2 = st(AbstractTrace(Nil, Map()))
      .addTypeConstraint(p1,BitTypeSet(BitSet(1)))
    assert(stateSolver.canSubsume(s2,s1,spec))
    assert(!stateSolver.canSubsume(s1,s2,spec))

    val s1h = s1.copy(sf = s1.sf.copy(heapConstraints = Map(FieldPtEdge(p1,"f")->p2)))
    val s2h = s2.copy(sf = s2.sf.copy(heapConstraints = Map(FieldPtEdge(p1,"f")->p2)))
    assert(stateSolver.canSubsume(s2h,s1h,spec))
    assert(!stateSolver.canSubsume(s1h,s2h,spec))
  }

  test("NI(x.foo(),x.baz()) && (not I(z.bar())) && x:T2 && z:T1 cannot subsume NI(x.foo(),x.baz()) && x:T2"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val bazM = SubClassMatcher("","baz","baz")
    val niTgt_x = I(CBEnter, SubClassMatcher("","niTgtM","niTgtM"), "x"::Nil)
    val notTgt_z = I(CBEnter, SubClassMatcher("", "notTgtM", "notTgtM"), "z"::Nil)
    val iFoo_x = I(CBEnter, fooM, "x"::Nil)
    val iBaz_x = I(CBEnter, bazM, "x"::Nil)
    val iBar_z = I(CBEnter, barM, "z"::Nil)

    val spec = new SpecSpace(Set(
      LSSpec("x"::Nil, Nil, NI(iFoo_x, iBaz_x), niTgt_x),
      LSSpec("z"::Nil, Nil, Not(iBar_z), notTgt_z)
    ))
    val s1 = st(AbstractTrace(niTgt_x::notTgt_z::Nil, Map("z"->p1,"x" -> p2)))
      .addTypeConstraint(p1,BitTypeSet(BitSet(1)))
      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))
    val s2 = st(AbstractTrace(niTgt_x::Nil, Map("x" -> p1)))
      .addTypeConstraint(p1, BitTypeSet(BitSet(2)))
    assert(!stateSolver.canSubsume(s1,s2,spec))
    assert(stateSolver.canSubsume(s2,s1,spec))

  }
  test("|>x.call() can subsume |> y.unsubscribe() |> x.call()"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    // Test with no wildcards
    val callSig = SpecSignatures.RxJava_call
    val unsubSig = SpecSignatures.RxJava_unsubscribe
    val subSig = SpecSignatures.RxJava_subscribe

    val subI = I(CIExit, subSig, "s"::"_"::"l"::Nil)
    val unsubI = I(CIExit, unsubSig, "_"::"s"::Nil)
    val unsubITgt = I(CIExit, unsubSig, "_"::"s1"::Nil)
    val callI = I(CBEnter, callSig, "_"::"l"::Nil)
    val callITgt = I(CBEnter, callSig, "_"::"l1"::Nil)
    val spec = new SpecSpace(Set(
      LSSpec("l"::Nil, "s"::Nil, NI(subI, unsubI),callI)
    ))
    val callSpec = RxJavaSpec.call
    val specReal = new SpecSpace(Set(callSpec))
    val s_1 = st(AbstractTrace(callITgt::Nil, Map("l1" -> p1)))
    val s_2 = st(AbstractTrace(unsubITgt::callITgt::Nil, Map("s1"->p2, "l1"->p1)))
    assert(stateSolver.canSubsume(s_1,s_2, specReal))
    assert(!stateSolver.canSubsume(s_2,s_1,specReal)) // forall v ... arg(omega(...)) != v ...?

    // Test with real spec
    val callTgt_x = SpecSignatures.RxJava_call_entry.copy(lsVars = "_"::"x"::Nil)
    val unsubTgt_y =  SpecSignatures.RxJava_unsubscribe_exit.copy(lsVars = "_"::"y"::Nil)
    val destTgt_z = SpecSignatures.Activity_onDestroy_exit.copy(lsVars = "_"::"z"::Nil)
    //TODO: add destroy before call?
    //TODO: ===== adding type constraints breaks things
    val s1 = st(AbstractTrace(callTgt_x::Nil,Map("x"->p2)))
//        .addTypeConstraint(p2,BitTypeSet(BitSet(2)))
//      .addTypeConstraint(p1,BitTypeSet(BitSet(1)))

    val s1h = s1.copy(sf = s1.sf.copy(heapConstraints = Map(
//      FieldPtEdge(p3, "subscription")-> p2,
    )))

    val s2 = st(AbstractTrace(unsubTgt_y::callTgt_x::Nil, Map("x"->p1, "y"->p2)))
//      .addTypeConstraint(p1,BitTypeSet(BitSet(1)))
//      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))


    val s2h = s2.copy(sf = s2.sf.copy(heapConstraints = Map(
//      FieldPtEdge(p3, "subscription")-> p2,
    )))

    assert(stateSolver.simplify(s1h,specReal).isDefined)
    assert(stateSolver.simplify(s2h,specReal).isDefined)
    // s2h (|>s = subscribe(x)|> y.unsubscribe() |> x.call()) should be refuted if s == y (sanity check)
    //TODO:
//    val s2hRef = s2h.addPureConstraint(PureConstraint(p1, Equals, p2))
//    assert(stateSolver.simplify(s2hRef, specReal).isEmpty)

    assert(stateSolver.canSubsume(s1h,s1h,specReal))
    assert(!stateSolver.canSubsume(s2h,s1h,specReal))
    assert(stateSolver.canSubsume(s1h,s2h, specReal))

    val spec2 = new SpecSpace(LifecycleSpec.spec + callSpec)

    assert(stateSolver.canSubsume(s1h,s2h, spec2))
    assert(!stateSolver.canSubsume(s2h,s1h,spec2))
  }
  test("|>y = _.subscribe(x)|> y.unsubscribe() |> x.call() should be subsumed by |> x.call()"){ f =>
    //TODO: Failing to refute this in symbex test =====
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    // Test with no wildcards
    val callSig = SpecSignatures.RxJava_call
    val unsubSig = SpecSignatures.RxJava_unsubscribe
    val subSig = SpecSignatures.RxJava_subscribe

    val subI = I(CIExit, subSig, "s"::"l"::Nil)
    val subITgt = I(CIExit, subSig, "s1"::"l1"::Nil)
    val unsubI = I(CIExit, unsubSig, "s"::Nil) //TODO: "_"::"s" swapped out for debugging
    val unsubITgt = I(CIExit, unsubSig, "s2"::Nil)
    val callI = I(CBEnter, callSig, "l"::Nil)
    val callITgt = I(CBEnter, callSig, "l2"::Nil)
    val spec = new SpecSpace(Set(
      LSSpec("l"::Nil, "s"::Nil, NI(subI, unsubI),callI)
    ))
    val s = st(AbstractTrace(subI::unsubI::callI::Nil, Map("s"->p2, "l"->p1)))
//    assert(stateSolver.simplify(s,spec).isEmpty) //Note: case exists where there may be a second sub
    val s2 = st(AbstractTrace(callI::Nil, Map("l"->p1)))
    assert(stateSolver.canSubsume(s2,s,spec))

    val s_1 = st(AbstractTrace(subITgt::unsubITgt::callITgt::Nil, Map("s2"->p2,"s1"->p2, "l2"->p1, "l1"->p1)))
    val s_2 = st(AbstractTrace(callITgt::Nil, Map("l2"->p1)))
    assert(stateSolver.canSubsume(s_2,s_1,spec))
//    assert(stateSolver.simplify(s_1,spec).isEmpty)

  }
  test("|> y.onDestroy() |>null = x.getActivity() not refuted"){f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val getActivityTgt_e_f = SpecSignatures.Fragment_get_activity_exit.copy(lsVars = "e"::"f"::Nil)
    val onDestroyTgt_d = SpecSignatures.Fragment_onDestroy_exit.copy(lsVars = "_"::"d"::Nil)
    val onCreateTgt_g= SpecSignatures.Fragment_onActivityCreated_entry.copy(lsVars = "_"::"g"::Nil)

    val s = st(AbstractTrace(onDestroyTgt_d::getActivityTgt_e_f::Nil,Map("e"->p1, "f"->p2, "d"->p3)))
      .addPureConstraint(PureConstraint(p1, Equals, NullVal))
    val spec = new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNonNull,
      FragmentGetActivityNullSpec.getActivityNull))
    assert(stateSolver.simplify(s,spec).isDefined)

    // empty trace in abstraction if x = y
    val s2 = s.addPureConstraint(PureConstraint(p2, Equals, p3))
    assert(stateSolver.witnessed(s2,spec))

    // |> y.onCreate() |> null = x.getActivity() not refuted unless x = y
    val s3 = st(AbstractTrace(onCreateTgt_g::getActivityTgt_e_f::Nil, Map("g"->p3, "e"->p1, "f"->p2)))
      .addPureConstraint(PureConstraint(p1, Equals, NullVal))
    assert(stateSolver.simplify(s3,spec).isDefined)

    val s4 = s3.addPureConstraint(PureConstraint(p3, Equals, p2))
    assert(stateSolver.simplify(s4, spec).isEmpty)
  }
  test("|>null = x.getActivity() can not subsume |> x.onDestroy() |>null = x.getActivity()"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val getActivityTgt_e_f = SpecSignatures.Fragment_get_activity_exit.copy(lsVars = "e"::"f"::Nil)
    val onDestroyTgt_d = SpecSignatures.Fragment_onDestroy_exit.copy(lsVars = "_"::"d"::Nil)
    val unsubscribe_g = SpecSignatures.RxJava_unsubscribe_exit.copy(lsVars = "_"::"g"::Nil)
    val s1 = st(AbstractTrace(getActivityTgt_e_f::Nil, Map("e"->p1, "f"->p2)))
      .addPureConstraint(PureConstraint(p1, Equals, NullVal))
    val s2 = st(AbstractTrace(onDestroyTgt_d::getActivityTgt_e_f::Nil,Map("e"->p1, "f"->p2, "d"->p2)))
      .addPureConstraint(PureConstraint(p1, Equals, NullVal))
    val spec = new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNonNull,
      FragmentGetActivityNullSpec.getActivityNull))

    assert(!stateSolver.canSubsume(s1,s2,spec))
    assert(stateSolver.canSubsume(s2,s1, spec))
  }
  ignore("I(x.foo(y)) can subsume I(x1.foo(y1)) && not ref(z)"){ f =>
    //TODO: |>
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
    val startTime1 = System.currentTimeMillis()
    val res = stateSolver.canSubsume(s1,s2,esp)
    println(s"s1 can subsume s2 time: ${(System.currentTimeMillis() - startTime1).toFloat/1000}")
    assert(res)

    val startTime2 = System.currentTimeMillis()
    val res2 = stateSolver.canSubsume(s2,s1,esp)
    println(s"s1 can subsume s2 time: ${(System.currentTimeMillis() - startTime2).toFloat/1000}")
    assert(!res2)
  }
  test("I(x.foo(y)) && y:T1 cannot subsume I(x1.foo(y1)) && y:T2"){ f =>
    // cannot subsume if types must be different
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    val fooM = SubClassMatcher("","foo","foo")
    val iFoo_x_y = I(CBEnter, fooM, "x" :: "y" :: Nil)
    val iFoo_x1_y1 = I(CBEnter, fooM, "x1"::"y1" :: Nil)
    val tgt_foo1_x_y = I(CBEnter, SubClassMatcher("","tgt_foo_1","tgt_foo_1"),"x"::"y"::Nil)
    val tgt_foo2_x1_y1 = I(CBEnter, SubClassMatcher("","tgt_foo_2","tgt_foo_2"),"x1"::"y1"::Nil)
    val spec = new SpecSpace(Set(
      LSSpec("x"::"y"::Nil,Nil,iFoo_x_y, tgt_foo1_x_y),
      LSSpec("x1"::"y1"::Nil,Nil,iFoo_x1_y1, tgt_foo2_x1_y1)
    ))

    val t1 = AbstractTrace(tgt_foo1_x_y::Nil, Map("y"-> p1, "x"->p3))
    val t2 = AbstractTrace(tgt_foo2_x1_y1::Nil, Map("y1" -> p2, "x1"->p3))
    val s1 = st(t1).addTypeConstraint(p3,BitTypeSet(BitSet(1)))
      .addTypeConstraint(p1, BitTypeSet(BitSet(1)))
    val s2 = st(t2).addTypeConstraint(p3, BitTypeSet(BitSet(1)))
      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))
    val res = stateSolver.canSubsume(s1,s2,spec)
    assert(!res)
    assert(!stateSolver.canSubsume(s2,s1,spec))

    //s3: I(x.foo(y)) && y:T1 can subsume s4: I(x1.foo(y1)) && y:T1
    // can subsume when types are compatible
    val s3 = st(t1).addTypeConstraint(p3,BitTypeSet(BitSet(1)))
      .addTypeConstraint(p1, BitTypeSet(BitSet(2)))
    val s4 = st(t2).addTypeConstraint(p3, BitTypeSet(BitSet(1)))
      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))
    assert(stateSolver.canSubsume(s3,s4,spec))
    assert(stateSolver.canSubsume(s4,s3,spec))
  }
  ignore("I(x.foo(y)) && y:T1 cannot subsume I(x.foo(y))|>I(x1.foo(y1)) && I(x2.foo(y2)) && y2:T2"){f =>
    //TODO: |>
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
    val res = stateSolver.canSubsume(s1,s2,esp)
    assert(!res)
  }
  ignore("I(x.foo()) && I(x.bar()) |> y.foo() cannot subsume I(x.foo()) && I(x.bar()) |> y.bar()") { f =>
    //TODO: |>
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
    val res = stateSolver.canSubsume(s(followsFoo),s(followsBar),esp)
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
    val res2 = stateSolver.canSubsume(s(subsumer),s(subsumee),esp)
    assert(!res2)
    val res3 = stateSolver.canSubsume(s(subsumee), s(subsumer),esp)
    assert(res3)
  }
  ignore("Subsumption of unrelated trace constraint") { f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val ifooa = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ifoob = I(CBEnter, Set(("", "foo")), "b" :: Nil)
    val state0 = State.topState.copy(sf = State.topState.sf.copy(
      traceAbstraction = Set(AbstractTrace(ifooa, Nil, Map("a"->p1)))
    ))
    val state1 = State.topState.copy(sf = State.topState.sf.copy(
      pureFormula = Set(PureConstraint(p1, NotEquals, p2)),
      traceAbstraction = Set(AbstractTrace(ifooa, ifoob::Nil, Map("a"->p1, "b"->p2)))
    ))
    assert(stateSolver.canSubsume(state0,state1, esp))
  }
  ignore("Subsumption of multi arg abstract traces") { f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)


    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")), "a"::"b":: Nil)
    val niSpec = NI(ibar,ifoo)
    val state = State.topState.copy(sf = State.topState.sf.copy(
      traceAbstraction = Set(AbstractTrace(ibar, Nil, Map()))))
    assert(stateSolver.canSubsume(state,state, esp))
  }

  ignore("Subsumption of abstract trace where type info creates disalias") { f =>
    //TODO: |>
    val (stateSolver,cha) = getStateSolver(SolverTypeSolving)

    val p1t = BoundedTypeSet(Some("String"), None, Set())
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
    assert(stateSolver.canSubsume(state,state2, esp))
  }

  ignore("Refute trace with multi arg and multi var (bad arg fun skolemization caused bug here)") { f =>
    //TODO: |>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val ifoo = I(CBEnter, Set(("", "foo")),  "_"::"a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")),  "_"::"a" :: Nil)
    val ibarc = I(CBEnter, Set(("", "bar")), "_"::"c" :: Nil)

    val at = AbstractTrace(NI(ifoo,ibar), ibarc::Nil, Map("a"->p1, "c"->p1))
    val state = State(StateFormula(
      CallStackFrame(dummyLoc, None, Map(StackVar("x") -> p1)) :: Nil, Map(), Set(),Map(), Set(at)), 0)
    val res = stateSolver.simplify(state,esp)
    assert(res.isEmpty)
  }
  test("Subsumption of pure formula including type information"){ f =>
    val (stateSolver,_) = getStateSolver(SolverTypeSolving)
    // (x->p1 && p1 <: Object) can not be subsumed by (x->p1 && p1 <:Foo)
    val state_ = state.copy(sf = state.sf.copy(
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("Foo"),None,Set())),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    val state__ = state.copy(sf = state.sf.copy(
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("java.lang.Object"),None,Set())),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    assert(!stateSolver.canSubsume(state_, state__,esp))

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
    assert(stateSolver.canSubsume(state1__, state1_,esp))
    assert(!stateSolver.canSubsume(state1_, state1__,esp))

    // (x->p1 && p1 <: Foo) can be subsumed by (x->p1 && p1 <:Object)
    assert(stateSolver.canSubsume(state__, state_,esp))
    assert(stateSolver.canSubsume(state_, state_,esp))

    // Combine type constraints and trace constraints
    val iFoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val iBar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val iBaz = I(CBEnter, Set(("", "baz")), "a" :: Nil)
    val iBaz_b = I(CBEnter, Set(("", "baz")), "b" :: Nil)
    val spec = new SpecSpace(Set(LSSpec("a"::Nil,Nil,NI(iFoo,iBar),iBaz)))

    val formula = AbstractTrace(iBaz_b::Nil, Map("b"->p1))
    val state2_ = state_.copy(sf = state_.sf.copy(
      traceAbstraction = Set(formula),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    val state2__ = state__.copy(sf = state__.sf.copy(
      traceAbstraction = Set(formula),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    assert(stateSolver.canSubsume(state2__, state2_,spec))
    assert(!stateSolver.canSubsume(state2_, state2__,spec))
  }
  test("Subsumption of pure formula in states"){ f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)

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
    assert(stateSolver.canSubsume(state,state_x_y,esp))
    assert(!stateSolver.canSubsume(state_x_y,state,esp))

  }

  test("Trace contained in abstraction") { f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    implicit val zCTX: Z3SolverCtx = stateSolver.getSolverCtx

    val foo = FwkMethod("foo", "")
    val bar = FwkMethod("bar", "")

    val i_foo_x = I(CIEnter, Set(("foo",""),("foo2","")), "x"::Nil)
    val i_bar_x = I(CIEnter, Set(("bar",""),("bar2","")), "x"::Nil)
    val trace = List(
      TMessage(CIEnter, foo, TAddr(1)::Nil),
      TMessage(CIEnter, bar, TAddr(1)::Nil)
    )

    val ni_foo_x_bar_x = NI(i_foo_x, i_bar_x)
    val targetFoo_x = I(CIExit, Set(("","targetFoo")), "x"::Nil)
    val targetFoo_y = I(CIExit, Set(("","targetFoo")), "y"::Nil)
    val spec = new SpecSpace(Set(
      LSSpec("x"::Nil, Nil, i_foo_x, targetFoo_x)
    ))
    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    // I(x.foo()) models @1.foo();@1.bar()
    val stIFooX = state.copy(
      sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(targetFoo_y :: Nil, Map("y" -> pv1)))))
    assert(stateSolver.traceInAbstraction(
      stIFooX,spec,
      trace))
    assert(!stateSolver.traceInAbstraction(stIFooX,spec,trace,negate = true, debug = true))

    // I(x.foo()) ! models empty
    assert(!stateSolver.traceInAbstraction(
      stIFooX,spec,
      Nil))
    assert(stateSolver.traceInAbstraction(stIFooX,spec,Nil, negate = true))

    val specNotFoo = new SpecSpace(Set(
      LSSpec("x"::Nil, Nil, Not(i_foo_x), targetFoo_x)
    ))
    // not I(x.foo()) models empty
    assert(stateSolver.traceInAbstraction(
      state = stIFooX,
      specNotFoo,
      trace = Nil
    ))


    // not I(x.foo()) or I(x.bar()) models empty

    val spec_NotFoo_OrBar = new SpecSpace(Set(
      LSSpec("x"::Nil, Nil,Or(Not(i_foo_x), i_bar_x), targetFoo_x)
    ))
    assert(stateSolver.traceInAbstraction(
      state = stIFooX,
      spec_NotFoo_OrBar ,
      trace = Nil
    ))

    val spec_NiFooBar = new SpecSpace(Set(
      LSSpec("x"::Nil, Nil, ni_foo_x_bar_x, targetFoo_x)
    ))
    assert(!stateSolver.traceInAbstraction(
      state = stIFooX,
      spec_NiFooBar,
      trace = Nil
    ))


    // NI(x.foo(), x.bar()) ! models @1.foo();@1.bar()
    assert(!stateSolver.traceInAbstraction(
      state = stIFooX,
      spec_NiFooBar,
      trace = trace
    ))

    // empty(trace) models NI(x.foo(),x.bar()) |> x.foo()
    val res = stateSolver.traceInAbstraction(
      state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(i_foo_x::targetFoo_x::Nil,Map("x"->pv1))))),
      spec_NiFooBar,
      Nil
    )
    assert(res)

    //@1.bar() models NI(x.foo(),x.bar()) |> x.foo()
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(i_foo_x::targetFoo_x::Nil,Map("x"->pv1))))),
        spec_NiFooBar,
        TMessage(CIEnter, bar, TAddr(1)::Nil)::Nil
      ))

    // NI(x.foo(),x.bar()) |> x.foo() models @1.foo();@1.bar()
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(i_foo_x::targetFoo_x::Nil,Map("x"->pv1))))),
        spec_NiFooBar,
        trace
      ))

    // NI(x.foo(),x.bar()) |> x.bar() ! models empty
    assert(
      !stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(i_bar_x::targetFoo_x::Nil,Map("x"->pv1))))),
        spec_NiFooBar,
        trace
      ))

    // Not NI(x.foo(), x.bar())  models @1.foo();@1.bar()
    val spec_not_NiFooBar = new SpecSpace(Set(
      LSSpec("x"::Nil, Nil, Not(ni_foo_x_bar_x), targetFoo_x)
    ))
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(targetFoo_x::Nil,Map("x"->pv1))))),
        spec_not_NiFooBar,
        trace
      ))
//    assert(
//      stateSolver.traceInAbstraction(
//        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(Not(ni_foo_x_bar_x), Nil,Map())))),esp,
//        trace
//      ))

    // I(foo(x,y)) models foo(@1,@2)
    val i_foo_x_y = I(CIEnter, Set(("foo",""),("foo2","")), "x"::"y"::Nil)
    val targetFoo_x_y = I(CIExit, Set(("","targetFoo")), "x"::"y"::Nil)
    val spec_Foo_x_y = new SpecSpace(Set(
      LSSpec("x"::"y"::Nil, Nil, i_foo_x_y, targetFoo_x_y)
    ))
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction =
          Set(AbstractTrace(targetFoo_x_y::Nil,Map("x"->pv1, "y"->pv2))))),
        spec_Foo_x_y,
        trace = TMessage(CIEnter, foo, TAddr(1)::TAddr(2)::Nil)::Nil
      )
    )

    // foo(@1,@2);bar(@1,@2) !models [¬I(foo(x,y))] /\ I(bar(x,y))
    val i_bar_x_y = I(CIEnter, Set(("bar",""),("bar2","")), "x"::"y"::Nil)
    val spec_NotFoo_Bar_x_y = new SpecSpace(Set(
      LSSpec("x"::"y"::Nil, Nil,And(Not(i_foo_x_y), i_bar_x_y), targetFoo_x_y)
    ))
    assert(
      !stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction =
          Set(AbstractTrace(targetFoo_x_y::Nil,Map("x"->pv1,"y"->pv2))))),
        spec_NotFoo_Bar_x_y,
        List(
          TMessage(CIEnter, foo, TAddr(1)::TAddr(2)::Nil),
          TMessage(CIEnter, bar, TAddr(1)::TAddr(2)::Nil)
        )
      )
    )

    // foo(@1,@2);bar(@1,@1) models [¬I(foo(x,y))] /\ I(bar(x,y))
    assert(
      !stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction =
          Set(AbstractTrace(targetFoo_x_y::Nil,Map("x"->pv1,"y"->pv2))))),
        spec_NotFoo_Bar_x_y,
        List(
          TMessage(CIEnter, foo, TAddr(1)::TAddr(2)::Nil),
          TMessage(CIEnter, bar, TAddr(1)::TAddr(1)::Nil)
        )
      )
    )

    // I(foo(y,y) !models foo(@1,@2)
    val i_foo_y_y = I(CIEnter, Set(("foo",""),("foo2","")), "y"::"y"::Nil)
    val targetFoo_y_y = I(CIExit, Set(("","targetFoo")), "y"::"y"::Nil)
    val spec_Foo_y_y = new SpecSpace(Set(
      LSSpec("x"::"y"::Nil, Nil, i_foo_y_y, targetFoo_x_y)
    ))
    assert(
      !stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction =
          Set(AbstractTrace(targetFoo_y_y::Nil,Map("y" -> PureVar(1)))))),
        spec_Foo_y_y,
        trace = TMessage(CIEnter, foo, TAddr(1)::TAddr(2)::Nil)::Nil,
        debug = true
      )
    )

    // I(foo(y,y) models foo(@2,@2)
    assert(
      stateSolver.traceInAbstraction(
        state.copy(sf = state.sf.copy(traceAbstraction =
          Set(AbstractTrace(targetFoo_x_y::Nil,Map("x"->pv1, "y"->pv2))))),
        spec_Foo_y_y,
        trace = TMessage(CIEnter, foo, TAddr(2)::TAddr(2)::Nil)::Nil
      )
    )
  }
  test("app mem restricted trace contained"){f =>
    val (stateSolver,_) = getStateSolver(f.typeSolving)
    implicit val zCTX: Z3SolverCtx = stateSolver.getSolverCtx

    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    val foo = FwkMethod("foo", "")
    val bar = FwkMethod("bar", "")

    val i_foo_x = I(CIEnter, Set(("foo",""),("foo2","")), "x"::Nil)
    val i_bar_x = I(CIEnter, Set(("bar",""),("bar2","")), "x"::Nil)
    val targetFoo_x_y = I(CIExit, Set(("","targetFoo")), "x"::"y"::Nil)
    val trace = List(
      TMessage(CIEnter, foo, TAddr(1)::Nil),
      TMessage(CIEnter, bar, TAddr(1)::Nil)
    )
    val spec = new SpecSpace(Set(
      LSSpec("x"::"y"::Nil, Nil, NI(i_foo_x, i_bar_x), targetFoo_x_y,
        Set(LSConstraint("y", Equals, "@null"))),
      LSSpec("x"::"y"::Nil, Nil, LSTrue, targetFoo_x_y, Set(LSConstraint("y", NotEquals, "@null")))
    ))
    val stateNull = state.copy(sf = state.sf.copy(
      traceAbstraction = Set(AbstractTrace(targetFoo_x_y::Nil, Map("y"->pv1, "x"->pv2))),
      pureFormula = Set(PureConstraint(pv1, Equals, NullVal))))
    val resIsNull = stateSolver.traceInAbstraction(
      stateNull,
      spec,
      trace
    )
    assert(
      !resIsNull
    )
    val resNonNull = stateSolver.traceInAbstraction(
      stateNull.copy(sf = stateNull.sf.copy(pureFormula = Set(PureConstraint(pv1, NotEquals, NullVal)))),
      spec,
      trace
    )
    assert(resNonNull)
  }

  private def getStateSolver(stateTypeSolving: StateTypeSolving = SetInclusionTypeSolving):
    (Z3StateSolver, ClassHierarchyConstraints) = {
    val pc = new ClassHierarchyConstraints(hierarchy,Set("java.lang.Runnable"),intToClass, stateTypeSolving)
    (new Z3StateSolver(pc),pc)
  }

  ignore("some timeout from 'Test prove dereference of return from getActivity'"){ f =>
    //TODO: fix or see if this is still reachable
    val (stateSolver,_) = getStateSolver(SolverTypeSolving)
    val s1 = read[State](Resource.getAsStream("s1_timeoutsubs.json"))
    val s2 = read[State](Resource.getAsStream("s2_timeoutsubs.json"))
    val s1pv = s1.pureVars()
    val s2pv = s2.pureVars()
    val s1tc = s1.typeConstraints
    val s2tc = s2.typeConstraints
    // Note: seems to finish if type ref removed
    val s1Simpl = s1.copy(sf = s1.sf.copy(typeConstraints = Map()))
    val s2Simpl = s2.copy(sf = s2.sf.copy(typeConstraints = Map()))

    val tmp = stateSolver.canSubsume(s1Simpl,s2Simpl,esp)

    // Note: seems to finish reasonably quickly without ref
    val s1NoRef = s1Simpl.copy(sf = s1Simpl.sf.copy(traceAbstraction =
      s1Simpl.sf.traceAbstraction.filter(abs => Ref.containsRefV(abs.a.get).isEmpty)))
    val s2NoRef = s2Simpl.copy(sf = s2Simpl.sf.copy(traceAbstraction =
      s2Simpl.sf.traceAbstraction.filter(abs => Ref.containsRefV(abs.a.get).isEmpty)))

    val res = stateSolver.canSubsume(s1Simpl, s2Simpl,esp)
    println(res)
  }
  test("Empty trace should not be contained in incomplete abstract trace") { f =>
    val (stateSolver,_) = getStateSolver(SolverTypeSolving)

    val iFoo_a = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val iFoo_b = I(CBEnter, Set(("", "foo")), "b" :: Nil)
    val iBar_a = I(CBEnter, Set(("", "bar")), "a"::Nil)
    val spec = new SpecSpace(Set(LSSpec("a"::Nil, Nil, iBar_a,iFoo_a,Set())),Set())
    def s(at:AbstractTrace):State = {
      val ts = State.topState
      ts.copy(sf = ts.sf.copy(traceAbstraction = Set(at)))
    }
    val pv = PureVar(1)
    val at = AbstractTrace(None, iFoo_b::Nil, Map("b" -> pv))

    val res = stateSolver.witnessed(s(at),spec)
    assert(!res)
  }
  ignore("Empty trace should not be contained in incomplete abstract trace with conditional spec") { f =>
    //TODO: Why is this test ignored???====
    //TODO: |>
    val (stateSolver,_) = getStateSolver(SolverTypeSolving)

    val iFoo_ac = I(CBEnter, Set(("", "foo")), "c"::"a" :: Nil)
    val iFoo_null_c =  I(CBEnter, Set(("", "foo")), "@null"::"a" :: Nil)
    val iFoo_bd = I(CBEnter, Set(("", "foo")), "d"::"b" :: Nil)
    val iBar_a = I(CBEnter, Set(("", "bar")), "a"::Nil)
    val s1 = LSSpec("a"::"c"::Nil, Nil, iBar_a,iFoo_ac,Set(LSConstraint("c", Equals, "@null")))
    val s2 = LSSpec("a"::"c"::Nil, Nil, LSTrue, iFoo_ac,Set(LSConstraint("c", NotEquals, "@null")))
    val spec = new SpecSpace(Set(s1,s2))
    def s(at:AbstractTrace, pc:Set[PureConstraint]):State = {
      val ts = State.topState
      ts.copy(sf = ts.sf.copy(traceAbstraction = Set(at), pureFormula = pc))
    }
    val pv = PureVar(1)
    val pv2 = PureVar(2)
    val at = AbstractTrace(None, iFoo_bd::Nil, Map("d" -> pv, "b" -> pv2))

    val res = stateSolver.witnessed(s(at,Set(PureConstraint(pv, Equals, NullVal))),spec)
    assert(!res)
    val res2 = stateSolver.witnessed(s(at,Set(PureConstraint(pv, NotEquals, NullVal))),spec)
    assert(res2)

    val s3 = LSSpec("c"::Nil, "a"::Nil, iBar_a, iFoo_null_c, Set())
    val spec2 = new SpecSpace(Set(s2,s3))
    val res3 = stateSolver.witnessed(s(at, Set(PureConstraint(pv, Equals, NullVal))), spec2)
    assert(!res3)

    val pv3 = PureVar(3)
    val iBaz_e = I(CBEnter, Set(("", "baz")), "e"::Nil)
    val iBaz_f = I(CBEnter, Set(("", "baz")), "f"::Nil)

    val s4 = LSSpec("e"::Nil, Nil, LSTrue,iBaz_e, Set())
//    val spec4 = new SpecSpace(Set(s2,s3,s4))
    val spec4 = new SpecSpace(Set(s3,s4))
    val at4 = AbstractTrace(None, iBaz_f::iFoo_bd::Nil, Map("f" -> pv3, "d" -> pv, "b" -> pv2))

    val res4 = stateSolver.witnessed(s(at4,Set(PureConstraint(pv, Equals, NullVal))),spec4,debug = true)
    assert(!res4)
  }
  test("Prepending required enable message to trace should prevent subsumption") { f =>
    val (stateSolver,_) = getStateSolver(SolverTypeSolving)

    val iFoo_ac = I(CBEnter, Set(("", "foo")), "c"::"a" :: Nil)
    val iFoo_null_c =  I(CBEnter, Set(("", "foo")), "@null"::"a" :: Nil)
    val iFoo_bd = I(CBEnter, Set(("", "foo")), "d"::"b" :: Nil)
    val iBar_a = I(CBEnter, Set(("", "bar")), "a"::Nil)
    val iBar_e = I(CBEnter, Set(("", "bar")), "e"::Nil)
    val iBaz_f = I(CBEnter, Set(("", "baz")), "f"::Nil)
    val iBaz_g = I(CBEnter, Set(("", "baz")), "g"::Nil)
    val iWap_g = I(CBEnter, Set(("", "wap")), "g"::Nil)
    val s1 = LSSpec("a"::"c"::Nil, Nil, iBar_a,iFoo_ac,Set(LSConstraint("c", Equals, "@null")))
    val s2 = LSSpec("a"::"c"::Nil, Nil, iBar_a, iFoo_ac,Set(LSConstraint("c", NotEquals, "@null"))) //TODO: does LSTrue cause issues?
    val s3 = LSSpec("g"::Nil, Nil, iWap_g, iBaz_g, Set())
    val spec = new SpecSpace(Set(s1,s2, s3))
    def s(at:AbstractTrace, pc:Set[PureConstraint]):State = {
      val ts = State.topState
      ts.copy(sf = ts.sf.copy(traceAbstraction = Set(at), pureFormula = pc))
    }
    val pv = PureVar(1)
    val pv2 = PureVar(2)
    val pv3 = PureVar(3)
    val pv4 = PureVar(4)
    val at1 = AbstractTrace(None, iBaz_f::iFoo_bd::Nil, Map("d" -> pv, "b" -> pv2, "f" ->pv4))
    val at2 = AbstractTrace(None, iBar_e::iBaz_f::iFoo_bd::Nil, Map("d" -> pv, "b" -> pv2, "e" -> pv3, "f" -> pv4))
    val pc = Set(PureConstraint(pv, Equals, NullVal))

    val s_1 = s(at1, pc)
    val isFeasible1 = stateSolver.simplify(s_1,spec)
    assert(isFeasible1.isDefined)
    val s_2 = s(at2,pc)
    val isFeasible2 = stateSolver.simplify(s_2, spec)
    assert(isFeasible2.isDefined)


    val res = stateSolver.canSubsume(s_1, s_2, spec)
    assert(!res)
  }
  test("z3 scratch"){f=>
    val ctx = new Context()
    val solver = ctx.mkSolver()
    solver.add(ctx.mkAnd())
    println(solver.check())

  }

}
