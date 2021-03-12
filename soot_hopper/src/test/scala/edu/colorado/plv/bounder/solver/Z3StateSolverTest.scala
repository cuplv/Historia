package edu.colorado.plv.bounder.solver

import better.files.Resource
import com.microsoft.z3._
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.{I, LSFalse, LSTrue, LSVar, NI, Not, Or}
import edu.colorado.plv.bounder.symbolicexecutor.state._
import org.scalatest.funsuite.AnyFunSuite

class Z3StateSolverTest extends AnyFunSuite {
  private val fooMethod = TestIRMethodLoc("","foo", List(Some(LocalWrapper("@this","Object"))))
  private val dummyLoc = CallbackMethodReturn(fmwClazz = "",
     fmwName="void foo()", fooMethod, None)
  private val v = PureVar(State.getId_TESTONLY())
  private val frame = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> v))
  private val state = State.topState
  test("null not null") {
  val statesolver = getStateSolver()

    val v2 = PureVar(State.getId_TESTONLY())
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal), PureConstraint(v2, Equals, NullVal))
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints,Map(),Set(),0)
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)
  }
  test("alias") {
    val statesolver = getStateSolver()

    val v2 = PureVar(State.getId_TESTONLY())
    val v3 = PureVar(State.getId_TESTONLY())
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal),
      PureConstraint(v3, Equals, NullVal))
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints + PureConstraint(v2, Equals, v3),Map(),Set(),0)
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)
  }
  test("Separate fields imply base must not be aliased a^.f->b^ * c^.f->b^ AND a^=c^ (<=> false)") {
    val statesolver = getStateSolver()

    val v2 = PureVar(State.getId_TESTONLY())
    val v3 = PureVar(State.getId_TESTONLY())
    val v4 = PureVar(State.getId_TESTONLY())
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v, Equals, v2)),Map(), Set(),0)
    val simplifyResult = statesolver.simplify(refutableState)
    assert(!simplifyResult.isDefined)

    // v3 and v4 on the right side of the points to can be aliased
    val unrefutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4),
        PureConstraint(v, NotEquals, v2)),Map(), Set(),0)
    val simplifyResult2 = statesolver.simplify(unrefutableState)
    assert(simplifyResult2.isDefined)

    // object field can point to self
    val unrefutableState2 = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4),
        PureConstraint(v, Equals, v4)),Map(), Set(),0)
    val simplifyResult3 = statesolver.simplify(unrefutableState2)
    assert(simplifyResult3.isDefined)
  }
  //TODO: group equal pure vars for type check
  test("aliased object implies fields must be aliased refuted by type constraints") {
//    val stateSolver = getStateSolver(SolverTypeSolving)
    //TODO: SolverTypeSolving is not currently working, decide if it is worth fixing
    val stateSolver = getStateSolver(SetInclusionTypeSolving)

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
    val refutableState = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3),constraints,typeC, Set(),0)
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
    val state = State(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),constraints2,typeC2, Set(),0)
    val simplifyResult2 = stateSolver.simplify(state)
    assert(simplifyResult2.isDefined)
  }
  test("Trace abstraction lsfalse is empty and lstrue is not"){
    val statesolver = getStateSolver()
    val absFalse = AbstractTrace(LSFalse, Nil, Map())
    val state = State.topState.copy(traceAbstraction = Set(absFalse))
    val res = statesolver.simplify(state)
    assert(!res.isDefined)
    val absTrue = AbstractTrace(LSTrue, Nil, Map())
    val stateTrue = State.topState.copy(traceAbstraction = Set(absTrue))
    val resTrue = statesolver.simplify(stateTrue)
    assert(resTrue.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) && a == p1 (<==>true)") {
    val statesolver = getStateSolver()

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val niBarBaz = NI(i,i2)
    val p1 = PureVar(State.getId_TESTONLY())
    val abs1 = AbstractTrace(niBarBaz, Nil, Map("a"->p1))
    val state1 = State(Nil, Map(),Set(),Map(), Set(abs1),0)
    val res1 = statesolver.simplify(state1)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) |> I(a.bar()) (<==>true)") {
    val statesolver = getStateSolver()

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val niBarBaz = NI(i,i2)
//    val abs1 = AbsArrow(AbsFormula(niBarBaz), i::Nil)
    val abs1 = AbstractTrace(niBarBaz, i::Nil, Map())
    val state1 = State(Nil, Map(),Set(),Map(), Set(abs1),0)
    val res1 = statesolver.simplify(state1)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)") {
    val statesolver = getStateSolver()

    // Lifestate atoms for next few tests
    val i = I(CBEnter, Set(("foo", "bar")), "a" :: Nil)
    val i2 = I(CBEnter, Set(("foo", "baz")), "a" :: Nil)
    val i3 = I(CBEnter, Set(("foo", "baz")), "b" :: Nil)
    val i4 = I(CBEnter, Set(("foo", "bar")), "c" :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NI(i,i2)

    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())

    // NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)
    val abs1 = AbstractTrace(niBarBaz,i3::Nil, Map("a"->p1, "b"->p1))
//    AbsAnd(AbsAnd(AbsFormula(niBarBaz), AbsEq("a",p1)), AbsEq("b",p1)),
    val state1 = State(Nil, Map(),Set(),Map(), Set(abs1),0)
    println(s"state: ${state1}")
    val res1 = statesolver.simplify(state1)
    assert(!res1.isDefined)
    val res2 = statesolver.witnessed(state1)
    assert(!res2)

    //TODO: more tests
    // [NI(m1^,m2^) OR (NOT NI(m1^,m2^)) ] AND (a |->a^) => TRUE
    val pred2 = Or(NI(i,i2),Not(NI(i,i2)))
    //val state2 = State(Nil, Map(),Set(), Set(LSAbstraction(pred2, Map("a"-> p1))))
    //val res2 = statesolver.simplify(state2)
    //assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) && a == p1 && c == p1 (<=> true)") {
    val stateSolver = getStateSolver()

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
    val state2 = State(Nil,Map(),Set(),Map(), Set(abs2),0)
    val res2 = stateSolver.simplify(state2)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(b.baz()) |> I(c.bar()) (<=> true) ") {
    val statesolver = getStateSolver()

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
    val state2 = State(Nil,Map(),Set(),Map(), Set(niaa),0)
    val res2 = statesolver.simplify(state2)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) ; I(c.bar()) ; I(b.baz()) && a = b = c (<=> false) ") {
    val statesolver = getStateSolver()

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
    val state2 = State(Nil,Map(),Set(),Map(), Set(niaa),0)
    val res2 = statesolver.simplify(state2)
    assert(res2.isEmpty)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = c (<=> true) ") {
    val statesolver = getStateSolver()

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
    val state2 = State(Nil,Map(),Set(),Map(), Set(niaa),0)
    val res2 = statesolver.simplify(state2)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = b (<=> false) ") {
    val statesolver = getStateSolver()

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
    val state2 = State(Nil,Map(),Set(),Map(), Set(niaa),0)
    val res2 = statesolver.simplify(state2)
    assert(res2.isEmpty)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(a.bar()),  NI(a.foo(),a.baz()) |> I(a.foo()) (<=> true) ") {
    val statesolver = getStateSolver()

    // Lifestate atoms for next few tests
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val ibaz = I(CBEnter, Set(("", "baz")), "a" :: Nil)
    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val t1 = AbstractTrace(NI(ibar,ibaz), ibar::Nil, Map())
    val t2 = AbstractTrace(NI(ifoo,ibaz), ifoo::Nil, Map())
    val s = state.copy(traceAbstraction = Set(t1,t2))
    val res = statesolver.simplify(s)
    assert(res.isDefined)
  }
  test ("Pickled states from integration tests should not crash solver") {
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
    val state = State.topState.copy(traceAbstraction = Set(at))

    val stateSolver = getStateSolver()
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

    val state1 = State.topState.copy(traceAbstraction = Set(at1))
    val res1 = stateSolver.simplify(state1)
    assert(res1.isDefined)
  }
  test("Not I(a.foo) |> a.foo does not contain empty trace"){
    val statesolver = getStateSolver()
    implicit val zctx = statesolver.getSolverCtx

    // Lifestate atoms for next few tests
    val foo_a = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val foo_b = I(CBEnter, Set(("", "foo")), "b" :: Nil)
    val bar_a = I(CBEnter, Set(("", "bar")), "a" :: Nil)


    // pure vars for next few tests
    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())

    val niaa = AbstractTrace(Not(foo_a), foo_b::Nil, Map("a"->p1, "b"->p2))
    val state = State(Nil,Map(),Set(PureConstraint(p1, Equals, p2)),Map(), Set(niaa),0)
    val contains = statesolver.traceInAbstraction(state, Nil )
    assert(!contains)

    val niaa2 = AbstractTrace(Or(Not(foo_a),bar_a), foo_b::Nil, Map("a"->p1))
    val state2 = State(Nil,Map(),Set(),Map(), Set(niaa2),0)
    val simpl = statesolver.simplify(state2,Some(2))
    assert(simpl.isDefined)
    val contains2 = statesolver.traceInAbstraction(state2, Nil)
    assert(contains2)
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

  test("Vacuous NI(a,a) spec") {
    val statesolver = getStateSolver()

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
    val res0 = statesolver.simplify(state.copy(traceAbstraction = Set(nia)))
    assert(res0.isDefined)

    //NI(a.bar(),a.bar()) |> I(b.bar()) && a = b (<=> true)
    val niaa = AbstractTrace(niBarBar, i4::Nil, Map("a"->p1,"b"->p1))
    val res1 = statesolver.simplify(state.copy(traceAbstraction = Set(niaa)))
    assert(res1.isDefined)
  }
  test("Subsumption of stack"){
    val statesolver = getStateSolver()

    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val state = State(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil, Map(),Set(),Map(),Set(),0)
    val state_ = state.copy(callStack = CallStackFrame(dummyLoc, None, Map(
      StackVar("x") -> p1,
      StackVar("y") -> p2
    ))::Nil)
    assert(statesolver.canSubsume(state,state_))
    assert(!statesolver.canSubsume(state_,state))

  }
  test("Subsumption of abstract traces") {
    val statesolver = getStateSolver()

    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val state = State(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil, Map(),Set(),Map(),Set(),0)
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

    // Extra trace constraint does not prevent subsumption
    // NI(foo(a),bar(a)), I(foo(c))  can subsume  NI(foo(a),bar(a))
    val res2 = statesolver.canSubsume(s_foo_bar_foo, s_foo_bar)
    assert(res2)

    // NI(foo(a),bar(a)), I(foo(c)) /\ a!=c cannot subsume  NI(foo(a),bar(a))
    val s_foo_bar_foo_notEq = state.copy(traceAbstraction =
      Set(AbstractTrace(NI(ifoo,ibar), Nil, Map("a"->p1, "c"->p2)),
        AbstractTrace(ifooc,Nil, Map())),
      pureFormula = Set(PureConstraint(p1, NotEquals, p2))
    )
    val res3 = statesolver.canSubsume(s_foo_bar_foo_notEq, s_foo_bar)
    assert(!res3)

    // Extra pure constraints should not prevent subsumption
    val fewerPure = State.topState.copy(pureFormula = Set(PureConstraint(p2, NotEquals, NullVal)))
    val morePure = fewerPure.copy(pureFormula = fewerPure.pureFormula +
//      PureConstraint(p1, TypeComp, SubclassOf("java.lang.Object")) +
      PureConstraint(p1, NotEquals, p2),
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("java.lang.Object"),None,Set())))
    assert(statesolver.canSubsume(fewerPure, morePure))

  }
  test("Subsumption of unrelated trace constraint") {
    val statesolver = getStateSolver()

    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())


    val ifooa = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ifoob = I(CBEnter, Set(("", "foo")), "b" :: Nil)
    val state0 = State.topState.copy(
      traceAbstraction = Set(AbstractTrace(ifooa, Nil, Map("a"->p1)))
    )
    val state1 = State.topState.copy(
      pureFormula = Set(PureConstraint(p1, NotEquals, p2)),
      traceAbstraction = Set(AbstractTrace(ifooa, ifoob::Nil, Map("a"->p1, "b"->p2)))
    )
    assert(statesolver.canSubsume(state0,state1, Some(2)))
  }
  test("Subsumption of multi arg abstract traces") {
    val statesolver = getStateSolver()

    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)


    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")), "a"::"b":: Nil)
    val niSpec = NI(ibar,ifoo)
    val state = State.topState.copy(traceAbstraction = Set(AbstractTrace(ibar, Nil, Map())))
    assert(statesolver.canSubsume(state,state, Some(2)))
  }

  test("Refute trace with multi arg and multi var (bad arg fun skolemization caused bug here)") {
    val statesolver = getStateSolver()

    val p1 = PureVar(State.getId_TESTONLY())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val ifoo = I(CBEnter, Set(("", "foo")),  "_"::"a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")),  "_"::"a" :: Nil)
    val ibarc = I(CBEnter, Set(("", "bar")), "_"::"c" :: Nil)

    val at = AbstractTrace(NI(ifoo,ibar), ibarc::Nil, Map("a"->p1, "c"->p1))
    val state = State(CallStackFrame(dummyLoc, None, Map(StackVar("x") -> p1)) :: Nil, Map(), Set(),Map(), Set(at), 0)
    val res = statesolver.simplify(state)
    assert(res.isEmpty)
  }
  test("Subsumption of pure formula including type information"){
    val statesolver = getStateSolver(SolverTypeSolving)
    // (x->p1 && p1 <: Object) can not be subsumed by (x->p1 && p1 <:Foo)
    val p1 = PureVar(State.getId_TESTONLY())
    val state_ = state.copy(typeConstraints = Map(p1 -> BoundedTypeSet(Some("Foo"),None,Set())))
    val state__ = state.copy(typeConstraints = Map(p1 -> BoundedTypeSet(Some("java.lang.Object"),None,Set())))
//    val state__ = state.copy(pureFormula = Set(PureConstraint(p1,TypeComp,SubclassOf("java.lang.Object"))))
    assert(!statesolver.canSubsume(state_, state__))

    val p2 = PureVar(State.getId_TESTONLY())
    // (x->p1 &&  p1 <: Foo && p1 == p2) can be subsumed by (x->p1 &&  p2 <: Object && p1 == p2)
    val state1_ = state.copy(pureFormula = Set(
//      PureConstraint(p1, TypeComp, SubclassOf("Foo")),
      PureConstraint(p1, Equals, p2)
    ), typeConstraints = Map(p1 -> BoundedTypeSet(Some("Foo"),None,Set())))
    val state1__ = state.copy(pureFormula = Set(
//      PureConstraint(p2, TypeComp, SubclassOf("java.lang.Object")),
      PureConstraint(p1, Equals, p2)
    ), typeConstraints = Map(p2 -> BoundedTypeSet(Some("java.lang.Object"),None,Set())))
    assert(statesolver.canSubsume(state1__, state1_))
    assert(!statesolver.canSubsume(state1_, state1__))

    // (x->p1 && p1 <: Foo) can be subsumed by (x->p1 && p1 <:Object)
    assert(statesolver.canSubsume(state__, state_))
    assert(statesolver.canSubsume(state_, state_))

    // Combine type constraints and trace constraints
    val ifoo = I(CBEnter, Set(("", "foo")), "a" :: Nil)
    val ibar = I(CBEnter, Set(("", "bar")), "a" :: Nil)
    val formula = AbstractTrace(NI(ifoo,ibar),Nil, Map("a"->p1))
    val state2_ = state_.copy(traceAbstraction = Set(formula))
    val state2__ = state__.copy(traceAbstraction = Set(formula))
    assert(statesolver.canSubsume(state2__, state2_, Some(20)))
    assert(!statesolver.canSubsume(state2_, state2__, Some(20)))
  }
  test("Subsumption of pure formula in states"){
    val statesolver = getStateSolver()

    val p1 = PureVar(State.getId_TESTONLY())
    val p2 = PureVar(State.getId_TESTONLY())
    val loc = AppLoc(fooMethod, TestIRLineLoc(1), isPre = false)

    val state = State(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil, Map(),Set(),Map(),Set(),0)

    // x->p1 * y->p2 can be subsumed by x->p1
    val state_x_y = state.copy(
      callStack = CallStackFrame(dummyLoc,None,Map(
        StackVar("x") -> p1,
        StackVar("y") -> p2
      ))::Nil,
      pureFormula = Set(PureConstraint(p1, NotEquals, p2))
    )
    assert(statesolver.canSubsume(state,state_x_y))
    assert(!statesolver.canSubsume(state_x_y,state))

  }

  test("Trace contained in abstraction") {
    val statesolver = getStateSolver()
    implicit val zctx = statesolver.getSolverCtx

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

    // not I(x.foo()) models empty
    assert(statesolver.traceInAbstraction(
      state = state.copy(traceAbstraction = Set(AbstractTrace(Not(i_foo_x), Nil, Map()))),
      trace = Nil
    ))

    // not I(x.foo()) or I(x.bar()) models empty
    assert(statesolver.traceInAbstraction(
      state = state.copy(traceAbstraction = Set(AbstractTrace(Or(Not(i_foo_x), i_bar_x), Nil, Map()))),
      trace = Nil
    ))

    // not I(x.foo()) or I(x.bar()) ! models @1.foo()
    assert(!statesolver.traceInAbstraction(
      state = state.copy(traceAbstraction = Set(AbstractTrace(Or(Not(i_foo_x), i_bar_x), Nil, Map()))),
      trace = TMessage(CIEnter, foo, TAddr(1)::Nil)::Nil
    ))

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

    // I(foo(x,y)) models foo(@1,@2)
    val i_foo_x_y = I(CIEnter, Set(("foo",""),("foo2","")), "X"::"Y"::Nil)
    assert(
      statesolver.traceInAbstraction(
        state.copy(traceAbstraction = Set(AbstractTrace(i_foo_x_y,Nil,Map()))),
        trace = TMessage(CIEnter, foo, TAddr(1)::TAddr(2)::Nil)::Nil //====
      )
    )


    // not I(foo(x,y)) !models foo(@1,@2)
    assert(
      !statesolver.traceInAbstraction(
        state.copy(traceAbstraction = Set(AbstractTrace(Not(i_foo_x_y),Nil,Map()))),
        trace = TMessage(CIEnter, foo, TAddr(1)::TAddr(2)::Nil)::Nil //====
      )
    )

    // I(foo(y,y) !models foo(@1,@2)
    val i_foo_y_y = I(CIEnter, Set(("foo",""),("foo2","")), "Y"::"Y"::Nil)
    assert(
      !statesolver.traceInAbstraction(
        state.copy(traceAbstraction = Set(AbstractTrace(i_foo_y_y,Nil,Map()))),
        trace = TMessage(CIEnter, foo, TAddr(1)::TAddr(2)::Nil)::Nil,
        debug = true
      )
    )

    // I(foo(y,y) models foo(@2,@2)
    assert(
      statesolver.traceInAbstraction(
        state.copy(traceAbstraction = Set(AbstractTrace(i_foo_y_y,Nil,Map()))),
        trace = TMessage(CIEnter, foo, TAddr(2)::TAddr(2)::Nil)::Nil //====
      )
    )

    //TODO: test "and", "scoped abstract traces"
  }

  private def getStateSolver(stateTypeSolving: StateTypeSolving = NoTypeSolving) : Z3StateSolver = {
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
        "rx.Single" -> Set("rx.Single")
    )

    val pc = new ClassHierarchyConstraints(hierarchy,Set("java.lang.Runnable"), stateTypeSolving)
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
