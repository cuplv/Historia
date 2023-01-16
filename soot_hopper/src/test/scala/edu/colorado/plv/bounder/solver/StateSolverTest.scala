package edu.colorado.plv.bounder.solver

import better.files.{File, Resource}
import com.microsoft.z3._
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, And, Exists, Forall, FreshRef, LSConstraint, LSFalse, LSPred, LSSpec, LSTrue, NS, Not, Or, Signature, SignatureMatcher, SubClassMatcher}
import edu.colorado.plv.bounder.lifestate.{FragmentGetActivityNullSpec, LSExpParser, LifecycleSpec, RxJavaSpec, SpecSignatures, SpecSpace, ViewSpec}
import edu.colorado.plv.bounder.symbolicexecutor.ExperimentSpecs
import edu.colorado.plv.bounder.symbolicexecutor.state._
import edu.colorado.plv.bounder.testutils.MkApk.getClass
import org.scalatest.{Exceptional, Failed, Outcome, Pending, Succeeded}
import org.scalatest.exceptions.TestFailedException
import org.scalatest.funsuite.FixtureAnyFunSuite
import smtlib.lexer.Lexer
import smtlib.parser.Parser
import smtlib.parser.Parser.UnknownCommandException
import smtlib.trees.Commands.{Assert, Command}
import smtlib.trees.Terms.SSymbol
import upickle.default.read

import java.io.StringReader
import scala.collection.BitSet
import scala.collection.mutable.ListBuffer
import scala.language.implicitConversions

class StateSolverTest extends FixtureAnyFunSuite {
  private val MAX_SOLVER_TIME = 5 //TODO //seconds -- Each call to "canSubsume" should take no more than this.
  private val fooMethod = SerializedIRMethodLoc("","foo()", List(Some(LocalWrapper("@this","Object"))))
  private val dummyLoc = CallbackMethodReturn(Signature("","void foo()"), fooMethod, None)
  private val v = PureVar(230)
  private val p1 = PureVar(1)
  private val p2 = PureVar(2)
  private val p3 = PureVar(3)
  private val p4 = PureVar(4)
  private val p5 = PureVar(5)
  private val p6 = PureVar(6)
  private val frame = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> v))
  private val state = State.topState
  case class FixtureParam(stateSolver:Z3StateSolver,
                          canSubsume: (State,State,SpecSpace)=> Boolean,
                          canSubsumePred:(LSPred,LSPred) => Boolean
                         )

  private val a = NamedPureVar("a")
  private val b = NamedPureVar("b")
  private val c = NamedPureVar("c")
  private val d = NamedPureVar("d")
  private val e = NamedPureVar("e")
  private val x = NamedPureVar("x")
  private val x1 = NamedPureVar("x1")
  private val y = NamedPureVar("y")
  private val y1 = NamedPureVar("y1")
  private val yy = NamedPureVar("yy")
  private val z = NamedPureVar("z")
  private val k = NamedPureVar("k")
  private val j = NamedPureVar("j")

  def loadState(resource:String):State = {
    //val f = File(Resource.getUrl(s"resources/${resource}").getPath)
    if(resource.startsWith("/")) {
      val f = File(resource)
      read[State](f.contentAsString)
    }else {
      read[State](Resource.getAsStream(resource))
    }
  }

  val esp = new SpecSpace(Set(), Set())

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

  private def getZ3StateSolver(checkSatPush:Boolean):
  (Z3StateSolver, ClassHierarchyConstraints) = {
    val pc = new ClassHierarchyConstraints(hierarchy,Set("java.lang.Runnable"),intToClass)
    (new Z3StateSolver(pc, logTimes = true,timeout = 20000, defaultOnSubsumptionTimeout = (z3SolverCtx:Z3SolverCtx) => {
      println(z3SolverCtx)
      throw new IllegalStateException("Exceeded time limit for test")
    }, pushSatCheck = checkSatPush, strict_test = true),pc)
  }
  override def withFixture(test: OneArgTest): Outcome = {
    // Run all tests with both set inclusion type solving and solver type solving
    // Some subsumption tests override type solving parameter
    // All other tests should work with either
//    withFixture(test.toNoArgTest(FixtureParam(SetInclusionTypeSolving)))

    val out = List(true/*,false*/).flatMap{ check => //TODO:====
      val (stateSolver, _) = getZ3StateSolver(check)
      //println(s"-normal subs, pushSatCheck:${check}")
      val t1 = withFixture(test.toNoArgTest(FixtureParam(stateSolver,
        (s1, s2, spec) => {
          //val s1simp = stateSolver.simplify(s1,spec).get
          //val s2simp = stateSolver.simplify(s2,spec).get
          println("Subsumption mode Z3")
          val start = System.nanoTime()
          val res = stateSolver.canSubsume(s1, s2, spec)
          val end = System.nanoTime()
          val totTime = (end - start)/1.0e9
          println(s"total time: ${totTime} seconds")
          if(totTime < MAX_SOLVER_TIME)
            res
          else
            throw new IllegalStateException(s"subsume took $totTime")

        },
        (p1,p2) => {
          val start = System.nanoTime()
          val res = stateSolver.canSubsume(p1, p2)
          val end = System.nanoTime()
          val totTime = (end - start)/1.0e9
          if (totTime < MAX_SOLVER_TIME)
            res
          else
            throw new IllegalStateException(s"subsume took $totTime")
          res
        }
      )))
      //Note: don't currently use canSubsumeSet, leaving test in case its useful later
      //println(s"-set subs, pushSatCheck:${check}")
//      val t2 = withFixture(test.toNoArgTest(FixtureParam(stateSolver, (s1, s2, spec) => {
//        s1.setSimplified() //For tests, just tell solver its simplified already
//        s2.setSimplified() //For tests, just tell solver its simplified already
//        //val s1simp = stateSolver.simplify(s1,spec).get
//        //val s2simp = stateSolver.simplify(s2,spec).get
//        println("Subsumption set")
//        val start = System.nanoTime()
//        val res = stateSolver.canSubsumeSet(Set(s1), s2, spec)
//        val end = System.nanoTime()
//        val totTime = (end - start) / 1.0e9
//        println(s"total time: ${totTime} seconds")
////        if (totTime < MAX_SOLVER_TIME)
//          res
////        else
////          throw new IllegalStateException(s"subsume took $totTime")
//      })))
      List(t1)
    }

    val (stateSolver, _) = getZ3StateSolver(false)
    //TODO: ===== make unify subsumption work
    val res = if(false){withFixture(test.toNoArgTest(FixtureParam(stateSolver, (s1, s2, spec) => {
      s1.setSimplified() //For tests, just tell solver its simplified already
      s2.setSimplified() //For tests, just tell solver its simplified already
      //val s1simp = stateSolver.simplify(s1,spec).get
      //val s2simp = stateSolver.simplify(s2,spec).get
      println("Subsumption unify mode")
      val start = System.nanoTime()
      val res = stateSolver.canSubsume(s1, s2, spec, method = SubsUnify)
      val end = System.nanoTime()
      val totTime = (end - start) / 1.0e9
      println(s"total time: ${totTime} seconds")
      if (totTime < MAX_SOLVER_TIME)
        res
      else
        throw new IllegalStateException(s"subsume took $totTime")
    }, ???)))} else Succeeded
    (res::out).reduce{(o1:Outcome, o2:Outcome) => (o1, o2)  match{
      case (Succeeded,Succeeded) => Succeeded
      case (_, exceptional: Exceptional)  => throw exceptional.toOption.get
      case (_, f:Failed) => throw f.exception
      case (f:Failed, _) => throw  f.exception
      case (e:Exceptional,Pending) => e
      case (_,Pending) => Pending
      case (o1, o2) =>
        println(o1)
        println(o2)
        ???
    }}
  }
  ignore("LOAD: test to debug subsumption issues by loading serialized states"){f =>
    // Note: leave ignored unless debugging, this test is just deserializing states to inspect
    val stateSolver = f.stateSolver
    val spec1 = new SpecSpace(
      Set(LifecycleSpec.Activity_onPause_onlyafter_onResume,
        LifecycleSpec.Activity_onResume_first_orAfter_onPause,
        ViewSpec.viewOnlyReturnedFromOneActivity,
        LifecycleSpec.noResumeWhileFinish,
        ViewSpec.clickWhileActive,
      )
    )
    val spec2 = new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
      FragmentGetActivityNullSpec.getActivityNonNull,
      LifecycleSpec.Fragment_activityCreatedOnlyFirst
    ) ++ RxJavaSpec.spec)
    val finishclickpause = new SpecSpace(Set( // specs for "Finish allows click after pause
      ViewSpec.clickWhileActive,
      ViewSpec.viewOnlyReturnedFromOneActivity,
      //              LifecycleSpec.noResumeWhileFinish,
      LifecycleSpec.Activity_onResume_first_orAfter_onPause //TODO: ==== testing if this prevents timeout
    )) //  ++ Dummy.specs)
    List(
      (new SpecSpace(ExperimentSpecs.row4Specs),
        "/Users/shawnmeier/Documents/source/bounder/soot_hopper/src/test/resources/s1.json",
        "/Users/shawnmeier/Documents/source/bounder/soot_hopper/src/test/resources/s2.json",
        (v:Boolean) =>{
          ???
        }),
      //      (spec2, "s1_diffz3unify.state", "s2_diffz3unify.state",true), // different in solver but same here???
      //(spec2, "/Users/shawnmeier/Desktop/outofInterpProblem/s1.json",
      //"/Users/shawnmeier/Desktop/outofInterpProblem/s2.json", true)
      //(spec1, "s1_timeout_1.json", "s2_timeout_1.json", (v:Boolean) => v == false)
    ).foreach {
      case (spec, f1, f2, expected) =>

        val s1 = loadState(f1)
        val s2 = loadState(f2)
        val startTime = System.nanoTime()

        val toCnfTest = (p:LSPred) => {
          val res = EncodingTools.toCNF(p)
          println("====")
          println(s"p: ${p}")
          println(s"res: ${res}")
          val dir1 = f.stateSolver.canSubsume(p,res)
          assert(dir1)
          println(dir1)
          println(s"dir1: $dir1")
          val dir2 = f.stateSolver.canSubsume(res,p)
          assert(dir2)
          println(s"dir2: $dir2")
          res
        }
        val s1P = EncodingTools.rhsToPred(s1.sf.traceAbstraction.rightOfArrow,spec).map(EncodingTools.simplifyPred).map(toCnfTest)
        val s2P = EncodingTools.rhsToPred(s2.sf.traceAbstraction.rightOfArrow,spec).map(EncodingTools.simplifyPred).map(toCnfTest)

        //TODO==== test code
        val ex1P = s1P.find(p => p.isInstanceOf[Exists])
        val ex2P = s2P.find(p => p.isInstanceOf[Exists])
        val subspred = f.stateSolver.canSubsume(ex1P.reduce(And),ex2P.reduce(And))
        println(subspred)

        //TODO==== end test code


        val res = f.canSubsume(s1, s2, spec)
        println(s"Subsumption check took ${(System.nanoTime() - startTime)/1000000000.0} seconds")
        expected(res)
    }
  }
  test("value not value") { f =>
    println(s"fixture param: $f")
    val stateSolver = f.stateSolver

    val v2 = PureVar(2)
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal), PureConstraint(v2, Equals, NullVal))
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints,Map(),AbstractTrace(Nil)),0)
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
    val stateSolver = f.stateSolver

    val v2 = PureVar(2)
    val v3 = PureVar(3)
    val constraints = Set(PureConstraint(v2, NotEquals, NullVal),
      PureConstraint(v3, Equals, NullVal))
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v2),constraints + PureConstraint(v2, Equals, v3),Map(),AbstractTrace(Nil))
      ,0)
    val simplifyResult = stateSolver.simplify(refutableState,esp)
    assert(simplifyResult.isEmpty)
  }
  test("Separate fields imply base must not be aliased a^.f->b^ * c^.f->b^ AND a^=c^ (<=> false)") { f=>
    val stateSolver = f.stateSolver

    val v2 = PureVar(2)
    val v3 = PureVar(3)
    val v4 = PureVar(4)
    val refutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v, Equals, v2)),Map(),
      AbstractTrace(Nil) ),0)
    val simplifyResult = stateSolver.simplify(refutableState,esp)
    assert(simplifyResult.isEmpty)

    // v3 and v4 on the right side of the points to can be aliased
    val unrefutableState = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4),
        PureConstraint(v, NotEquals, v2)),Map(),AbstractTrace(Nil)),0)
    val simplifyResult2 = stateSolver.simplify(unrefutableState,esp)
    assert(simplifyResult2.isDefined)

    // object field can point to self
    val unrefutableState2 = State(StateFormula(List(frame),
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),Set(PureConstraint(v3, Equals, v4),
        PureConstraint(v, Equals, v4)),Map(),AbstractTrace(Nil)),0)
    val simplifyResult3 = stateSolver.simplify(unrefutableState2,esp)
    assert(simplifyResult3.isDefined)
  }
  test("Transitive equality should be refuted by type constraints") { f=>
    val stateSolver = f.stateSolver
    val v2 = PureVar(2)
    val v3 = PureVar(3)
    val v4 = PureVar(4)
    val refutableState = State(StateFormula(List(frame),
      Map(),
      Set(PureConstraint(v2, Equals, v3),PureConstraint(v3, Equals, v4)),
      Map(v2->BoundedTypeSet(Some("String"),None,Set()),
        //        v3->BoundedTypeSet(Some("String"),None,Set()),
        v4->BoundedTypeSet(Some("Foo"),None,Set())),AbstractTrace( Nil)),0)
    val simplifyResult = stateSolver.simplify(refutableState,esp)
    assert(simplifyResult.isEmpty)

    val refutableState2 = State(StateFormula(List(frame),
      Map(),
      Set(PureConstraint(v2, Equals, v3),PureConstraint(v3, Equals, v4), PureConstraint(v2, NotEquals, v4)),
      Map(),AbstractTrace( Nil)),0)
    val simplifyResult2 = stateSolver.simplify(refutableState2,esp)
    assert(simplifyResult2.isEmpty)
  }
  test("test feasibility of constraints before GC") { f=>
    val stateSolver = f.stateSolver
    val v2 = PureVar(2)
    val v3 = PureVar(3)
    val v4 = PureVar(4)
    val refutableState = State(StateFormula(List(frame),
      Map(),
      Set(PureConstraint(v2, Equals, v3),PureConstraint(v3, Equals, v4)),
      Map(v2->BoundedTypeSet(Some("String"),None,Set()),
        v3->BoundedTypeSet(Some("String"),None,Set()),v4->BoundedTypeSet(Some("Foo"),None,Set())),
      AbstractTrace( Nil)),0)
    val simplifyResult = stateSolver.simplify(refutableState,esp)
    assert(!simplifyResult.isDefined)

  }
  test("aliased object implies fields must be aliased refuted by type constraints") { f =>
    val stateSolver = f.stateSolver

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
      Map(FieldPtEdge(v,"f") -> v3),constraints,typeC,AbstractTrace( Nil)),0)
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
      Map(FieldPtEdge(v,"f") -> v3, FieldPtEdge(v2,"f") -> v4),constraints2,typeC2,AbstractTrace( Nil)),0)
    val simplifyResult2 = stateSolver.simplify(state,esp)
    assert(simplifyResult2.isDefined)
  }
  test("Trace abstraction lsfalse is empty and lstrue is not"){ f =>
    val stateSolver = f.stateSolver
    val iFoo_ac = AbsMsg(CBEnter, Set(("", "foo")), c::a :: Nil)
    val iFoo_bd = AbsMsg(CBEnter, Set(("", "foo")), d::b :: Nil)
    val specSpace = new SpecSpace(Set(LSSpec(a::c::Nil, Nil, LSFalse, iFoo_ac)))
    val absFalse = AbstractTrace( iFoo_bd::Nil)
    val state = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = absFalse))
    val res = stateSolver.simplify(state,specSpace)
    assert(res.isEmpty)
    val specSpace2 = new SpecSpace(Set(LSSpec(a::c::Nil, Nil, LSTrue, iFoo_ac)))
    val absTrue = AbstractTrace( iFoo_bd::Nil)
    val stateTrue = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = absTrue))
    val resTrue = stateSolver.simplify(stateTrue,specSpace2)
    assert(resTrue.isDefined)
  }
  test("Trace abstraction O(a.bar()) && HN(b.bar()) && a == p1 (<==>false)") { f =>
    val stateSolver = f.stateSolver
    val iBar_a = AbsMsg(CBEnter, Set(("", "bar")), a :: Nil)
    val iTgtPosBar_a = AbsMsg(CBEnter, Set(("", "tgtPos")), a :: Nil)
    val iTgtPosBar_b = AbsMsg(CBEnter, Set(("", "tgtPos")), b :: Nil)
    val iTgtNegBar_a = AbsMsg(CBEnter, Set(("","tgtNeg")), a::Nil)
    val iTgtNegBar_c = AbsMsg(CBEnter, Set(("","tgtNeg")), c::Nil)
    val spec = new SpecSpace(Set(
      LSSpec(a::Nil, Nil, iBar_a, iTgtPosBar_a),
      LSSpec(a::Nil, Nil, Not(iBar_a), iTgtNegBar_a)
    ))

    // Lifestate atoms for next few tests
    val abs1 = AbstractTrace(iTgtNegBar_c::iTgtPosBar_b::Nil)// , Map(b->p1, "c" -> p1))
    val state1 = State(StateFormula(Nil, Map(),
      Set(PureConstraint(b,Equals,p1), PureConstraint(c,Equals,p1)),Map(), abs1),0)
    val res1 = stateSolver.simplify(state1,spec)
    assert(res1.isEmpty)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) && a == p1 (<==>true)") { f =>
    val stateSolver = f.stateSolver
    val iFoo_ac = AbsMsg(CBEnter, Set(("", "foo")), c::a :: Nil)
    val iFoo_bd = AbsMsg(CBEnter, Set(("", "foo")), d::b :: Nil)
    val iBar_a = AbsMsg(CBEnter, Set(("", "bar")), a :: Nil)
    val iBaz_a = AbsMsg(CBEnter, Set(("", "baz")), a :: Nil)
    val niBarBaz = NS(iBar_a,iBaz_a)
    val spec = new SpecSpace(Set(LSSpec(a::c::Nil, Nil, niBarBaz, iFoo_ac)))

    // Lifestate atoms for next few tests
    val abs1 = AbstractTrace(iFoo_bd::Nil) //Map(b->p1, "d" -> p2))
    val state1 = State(StateFormula(Nil, Map(),
      Set(PureConstraint(b,Equals,p1),PureConstraint(d,Equals,p2)),Map(), abs1),0)
    val res1 = stateSolver.simplify(state1,spec)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(), a.baz()) |> I(a.bar()) (<==>true)") { f =>
    val stateSolver = f.stateSolver

    val iFoo_ac = AbsMsg(CBEnter, Set(("", "foo")), c::a :: Nil)
    val iFoo_bd = AbsMsg(CBEnter, Set(("", "foo")), d::b :: Nil)
    val iBar_a = AbsMsg(CBEnter, Set(("", "bar")), a :: Nil)
    val iBar_e = AbsMsg(CBEnter, Set(("", "bar")), e :: Nil)
    val iBaz_a = AbsMsg(CBEnter, Set(("", "baz")), a :: Nil)
    val niBarBaz = NS(iBar_a,iBaz_a)
    val spec = new SpecSpace(Set(LSSpec(a::c::Nil, Nil, niBarBaz, iFoo_ac)))

    // Lifestate atoms for next few tests
    val abs1 = AbstractTrace(iBar_e::iFoo_bd::Nil) //Map("e"->p1,b->p1))
    val state1 = State(StateFormula(Nil, Map(),
      Set(PureConstraint(e,Equals, p1), PureConstraint(b,Equals, p1)),Map(), abs1),0)
    val res1 = stateSolver.simplify(state1,spec)
    assert(res1.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)") { f =>
    val stateSolver = f.stateSolver

    val iBar_a = AbsMsg(CBEnter, Set(("_", "bar")), a :: Nil)
    val iBaz_a = AbsMsg(CBEnter, Set(("_", "baz")), a :: Nil)
    val iBaz_b = AbsMsg(CBEnter, Set(("_", "baz")), b :: Nil)
    val iBaz_c = AbsMsg(CBEnter, Set(("_", "baz")), c :: Nil)
    val tgt = AbsMsg(CBEnter, Set(("_", "tgt")), a::Nil)
    val tgtx = AbsMsg(CBEnter, Set(("_", "tgt")), x::Nil)

    // NI(a.bar(), a.baz())
    val niBarBaz = NS(iBar_a,iBaz_a)
    val spec = new SpecSpace(Set(LSSpec(a::Nil, Nil, niBarBaz, tgt)))

    // NI(a.bar(),a.baz()) |> I(c.baz()) && a == p1 && c == p1 (<=> false)
    val abs1 = AbstractTrace(iBaz_b::tgtx::Nil)// Map(a->p1, b->p1))
//    AbsAnd(AbsAnd(AbsFormula(niBarBaz), AbsEq(a,p1)), AbsEq(b,p1)),
    val state1 = State(StateFormula(Nil, Map(),
      Set(PureConstraint(x,Equals,p1), PureConstraint(b,Equals,p1)),Map(), abs1),0)
    val res1 = stateSolver.simplify(state1, spec)
    assert(res1.isEmpty)
    val res2 = stateSolver.witnessed(state1,spec)
    assert(res2.isEmpty)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) && a == p1 && c == p1 (feas and init)") { f =>
    val stateSolver = f.stateSolver

    // Lifestate atoms for next few tests
    val bara = AbsMsg(CBEnter, Set(("foo", "bar\\(\\)")), a :: Nil)
    val baza = AbsMsg(CBEnter, Set(("foo", "baz\\(\\)")), a :: Nil)
    val tgtNIa = AbsMsg(CBEnter, Set(("foo", "tgt\\(\\)")), a::Nil)
    val tgtNIp1 = AbsMsg(CBEnter, Set(("foo", "tgt\\(\\)")), p1::Nil)
    val barp1 = AbsMsg(CBEnter, Set(("foo", "bar\\(\\)")), p1 :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NS(bara, baza)
    val sp = LSSpec(a::Nil,Nil, niBarBaz,tgtNIa)
    val spec = new SpecSpace(Set(sp))

    val tr = AbstractTrace(barp1::tgtNIp1::Nil)
    val state = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = tr))

    val simp = f.stateSolver.simplify(state,spec)
    assert(simp.nonEmpty)

    val init = f.stateSolver.witnessed(state,spec)
    assert(init.isDefined)
  }
  ignore("Trace abstraction NI(a.bar(),a.baz()) |> I(b.baz()) |> I(c.bar()) (<=> true) ") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver

    // Lifestate atoms for next few tests
    val i = AbsMsg(CBEnter, Set(("foo", "bar")), a :: Nil)
    val i2 = AbsMsg(CBEnter, Set(("foo", "baz")), a :: Nil)
    val b_baz = AbsMsg(CBEnter, Set(("foo", "baz")), b :: Nil)
    val c_bar = AbsMsg(CBEnter, Set(("foo", "bar")), c :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NS(i, i2)

    // NI(a.bar(),a.baz()) |> I(c.bar()) ; i(b.baz()
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map(a->p1, c->p1))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), niaa),0)
    val res2 = stateSolver.simplify(state2,esp)
    assert(res2.isDefined)
  }
  test("Trace abstraction NI(a.bar(),a.baz()) ; I(c.bar()) ; I(b.baz()) && a = b = c (<=> false) ") { f =>

    val stateSolver = f.stateSolver

    // Lifestate atoms for next few tests
    val bara = AbsMsg(CBEnter, Set(("foo", "bar\\(\\)")), a :: Nil)
    val baza = AbsMsg(CBEnter, Set(("foo", "baz\\(\\)")), a :: Nil)
    val tgtNIa = AbsMsg(CBEnter, Set(("foo", "tgt\\(\\)")), a :: Nil)
    val tgtNIp1 = AbsMsg(CBEnter, Set(("foo", "tgt\\(\\)")), p1 :: Nil)
    val barp1 = AbsMsg(CBEnter, Set(("foo", "bar\\(\\)")), p1 :: Nil)
    val bazp1 = AbsMsg(CBEnter, Set(("foo", "baz\\(\\)")), p1 :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NS(bara, baza)
    val sp = LSSpec(a :: Nil, Nil, niBarBaz, tgtNIa)
    val spec = new SpecSpace(Set(sp))

    val tr = AbstractTrace(barp1 :: bazp1 :: tgtNIp1 :: Nil)
    val state = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = tr))

    val simp = f.stateSolver.simplify(state, spec)
    assert(simp.isEmpty)

    val init = f.stateSolver.witnessed(state, spec)
    assert(init.isEmpty)

  }
  ignore("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = c (<=> true) ") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver

    // Lifestate atoms for next few tests
    val i = AbsMsg(CBEnter, Set(("foo", "bar")), a :: Nil)
    val i2 = AbsMsg(CBEnter, Set(("foo", "baz")), a :: Nil)
    val b_baz = AbsMsg(CBEnter, Set(("foo", "baz")), b :: Nil)
    val c_bar = AbsMsg(CBEnter, Set(("foo", "bar")), c :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NS(i, i2)

    // NI(a.bar(),a.baz()) |> I(c.bar()) ; I(b.baz())
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map(a->p1, c->p1, b->p2))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), niaa),0)
    val res2 = stateSolver.simplify(state2,esp)
    assert(res2.isDefined)
  }
  ignore("Trace abstraction NI(a.bar(),a.baz()) |> I(c.bar()) |> I(b.baz() && a = b (<=> false) ") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver

    // Lifestate atoms for next few tests
    val i = AbsMsg(CBEnter, Set(("foo", "bar")), a :: Nil)
    val i2 = AbsMsg(CBEnter, Set(("foo", "baz")), a :: Nil)
    val b_baz = AbsMsg(CBEnter, Set(("foo", "baz")), b :: Nil)
    val c_bar = AbsMsg(CBEnter, Set(("foo", "bar")), c :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBaz = NS(i, i2)

    // NI(a.bar(),a.baz()) |> I(c.bar()) |> i(b.baz()
    val niaa = AbstractTrace(niBarBaz, c_bar::b_baz::Nil, Map(a->p1,b->p1, c->p2))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), niaa),0)
    val res2 = stateSolver.simplify(state2,esp)
    assert(res2.isEmpty)
  }
  ignore("Trace abstraction NI(a.bar(),a.baz()) |> I(a.bar()),  NI(a.foo(),a.baz()) |> I(a.foo()) (<=> true) ") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver

    // Lifestate atoms for next few tests
    val ibar = AbsMsg(CBEnter, Set(("", "bar")), a :: Nil)
    val ibaz = AbsMsg(CBEnter, Set(("", "baz")), a :: Nil)
    val ifoo = AbsMsg(CBEnter, Set(("", "foo")), a :: Nil)
    val t1 = AbstractTrace(NS(ibar,ibaz), ibar::Nil, Map())
    val t2 = AbstractTrace(NS(ifoo,ibaz), ifoo::Nil, Map())
//    val s = state.copy(sf = state.sf.copy(traceAbstraction = Set(t1,t2)))
//    val res = stateSolver.simplify(s,esp)
//    assert(res.isDefined)
    ???
  }

  ignore("( (Not I(a.bar())) && (Not I(a.baz())) ) |> I(b.bar()) && a=pv1 && b = pv1,  (<=>false) ") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver

    // Lifestate atoms for next few tests
    val ibar_a = AbsMsg(CBEnter, Set(("", "bar")), a :: Nil)
    val ibar_b = AbsMsg(CBEnter, Set(("", "bar")), b :: Nil)
    val ibaz_a = AbsMsg(CBEnter, Set(("", "baz")), a :: Nil)
    val ifoo = AbsMsg(CBEnter, Set(("", "foo")), a :: Nil)

    // (Not I(a.bar()))  |> I(b.bar()) && a = pv1 && b = pv1
    val pv1 = PureVar(1)
    val t1 = AbstractTrace(Not(ibar_a), ibar_b::Nil, Map())//.addModelVar(a,pv1).addModelVar(b,pv1)
    val s1 = state.copy(sf = state.sf.copy(traceAbstraction = t1,
      pureFormula = Set(PureConstraint(a,Equals, pv1), PureConstraint(b,Equals,pv1))))
    val res = stateSolver.simplify(s1,esp)
    assert(res.isEmpty)

    //( (Not I(a.bar())) && (Not I(a.baz())) ) |> I(b.bar()) && a = pv1 && b = pv1
    val t2 = AbstractTrace(And(Not(ibar_a), Not(ibaz_a)), ibar_b::Nil, Map())
      //.addModelVar(a,pv1).addModelVar(b,pv1)
    val s2 = state.copy(sf = state.sf.copy(traceAbstraction = t2,
      pureFormula = Set(PureConstraint(a,Equals,pv1), PureConstraint(b,Equals, pv1))
    ))
    val res2 = stateSolver.simplify(s2,esp)
    assert(res2.isEmpty)
  }
  ignore("Not witnessed: I(a.foo()) |> b.foo() && Not(I(b.bar())) |> a.bar() && a = pv1 && b = pv2") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver

    // Lifestate atoms for next few tests
    val ibar_a = AbsMsg(CBEnter, Set(("", "bar")), a :: Nil)
    val ibar_b = AbsMsg(CBEnter, Set(("", "bar")), b :: Nil)
    val ifoo_a = AbsMsg(CBEnter, Set(("", "foo")), a :: Nil)
    val ifoo_b = AbsMsg(CBEnter, Set(("", "foo")), b :: Nil)

    val pv1 = PureVar(1)
    val pv2 = PureVar(2)

    // t1: I(a.foo()) |> b.foo()
    val t1 = AbstractTrace(ifoo_a, ifoo_b::Nil, Map(a -> pv1, b -> pv2))

    // t2: Not(I(b.bar())) |> a.bar()
    val t2 = AbstractTrace(Not(ibar_b), ibar_a::Nil, Map(a -> pv1, b -> pv2))

//    val s1 = state.copy(sf = state.sf.copy(traceAbstraction = Set(t1,t2)))
//    val res = stateSolver.witnessed(s1,esp)
//    assert(!res)
    ???

    // t1 is witnessed
    val s2 = state.copy(sf = state.sf.copy(traceAbstraction = t1))
    val res2 = stateSolver.witnessed(s2,esp)
    assert(res2.isDefined)
  }
  ignore("Not feasible: Not(I(a.foo(_)))) |> b.foo(c) && a=p1 && b = p3 && c = p2 && p1 = p3") {f=>
    //TODO: |>
    val stateSolver = f.stateSolver

    // Lifestate atoms for next few tests
    val ifoo_a_ = AbsMsg(CBEnter, Set(("", "foo")), a::TopVal :: Nil)
    val ifoo_bc = AbsMsg(CBEnter, Set(("", "foo")), b::c :: Nil)

    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    val pv3 = PureVar(3)

    // t1: I(a.foo(_)) |> b.foo(c)
    val t1 = AbstractTrace(Not(ifoo_a_), ifoo_bc::Nil, Map(a -> pv1, b -> pv3, c -> pv2))

    val s1 = state.copy(sf = state.sf.copy(pureFormula = Set(PureConstraint(pv1, Equals, pv3)),
      traceAbstraction = t1))

    val isFeas = stateSolver.simplify(s1,esp)
    assert(isFeas.isEmpty)

    val isWit = stateSolver.witnessed(s1,esp)
    assert(isWit.isDefined)
  }
  ignore("Not I(a.foo) |> a.foo does not contain empty trace"){ f =>
    //TODO: |>
    val stateSolver = f.stateSolver
    implicit val zctx = stateSolver.getSolverCtx

    // Lifestate atoms for next few tests
    val foo_a = AbsMsg(CBEnter, Set(("", "foo")), a :: Nil)
    val foo_b = AbsMsg(CBEnter, Set(("", "foo")), b :: Nil)
    val bar_a = AbsMsg(CBEnter, Set(("", "bar")), a :: Nil)

    val niaa = AbstractTrace(Not(foo_a), foo_b::Nil, Map(a->p1, b->p2))
    val state = State(StateFormula(Nil,Map(),Set(PureConstraint(p1, Equals, p2)),Map(), niaa),0)
    val contains = stateSolver.traceInAbstraction(state,esp, Trace.empty )
    assert(contains.isEmpty)

    val niaa2 = AbstractTrace(Or(Not(foo_a),bar_a), foo_b::Nil, Map(a->p1))
    val state2 = State(StateFormula(Nil,Map(),Set(),Map(), niaa2),0)
    val simpl = stateSolver.simplify(state2,esp)
    assert(simpl.isDefined)
    val contains2 = stateSolver.traceInAbstraction(state2,esp, Trace.empty)
    assert(contains2.isDefined)
  }


  test("refuted: I(a.foo()) |> Ref(a)"){ f =>
    // a.foo() must be invoked before a is created
    val stateSolver = f.stateSolver
    implicit val zctx = stateSolver.getSolverCtx

    // Lifestate atoms for next few tests
    val foo_a = AbsMsg(CBEnter, Set(("", "foo")), a:: c :: Nil)
    val tgt_a = AbsMsg(CBEnter, Set(("", "tgt")), a:: c :: Nil)
    val tgt_x = AbsMsg(CBEnter, Set(("", "tgt")), x:: y :: Nil)
    val spec = new SpecSpace(Set(LSSpec(a::c::Nil, Nil, foo_a, tgt_a)))

    val at = AbstractTrace(tgt_x::FreshRef(b)::Nil) //Map(a->p1, b -> p2, "c"->p3))
    val pf = Set(PureConstraint(x,Equals,p1),PureConstraint(b,Equals,p2), PureConstraint(y,Equals,p3))
    val state = State(StateFormula(Nil,Map(),
      pf ++ Set(PureConstraint(p1, Equals, p2)),Map(), at),0)
    val res = stateSolver.simplify(state,spec)
    assert(res.isEmpty)

    val state0 = state.copy(sf =
      state.sf.copy(pureFormula = pf ++ Set(PureConstraint(p1, NotEquals, p2))))
    val res0 = stateSolver.simplify(state0,spec)
    assert(res0.isDefined)

    val state1 = state.copy(sf =
      state.sf.copy(pureFormula = pf))
    val res1 = stateSolver.simplify(state1,esp)
    assert(res1.isDefined)
  }

  ignore("Vacuous NI(a,a) spec") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver

    // Lifestate atoms for next few tests
    val i = AbsMsg(CBEnter, Set(("foo", "bar")), a :: Nil)
    val i4 = AbsMsg(CBEnter, Set(("foo", "bar")), b :: Nil)
    // NI(a.bar(), a.baz())
    val niBarBar = NS(i, i)

    // pure vars for next few tests
    //NI(a.bar(),a.bar()) (<=> true)
    // Note that this should be the same as I(a.bar())
    val nia = AbstractTrace(niBarBar, Nil, Map())
    val res0 = stateSolver.simplify(state.copy(sf = state.sf.copy(traceAbstraction = nia)),esp)
    assert(res0.isDefined)

    //NI(a.bar(),a.bar()) |> I(b.bar()) && a = b (<=> true)
    val niaa = AbstractTrace(niBarBar, i4::Nil, Map(a->p1,b->p1))
    val res1 = stateSolver.simplify(state.copy(sf = state.sf.copy(traceAbstraction = niaa)),esp)
    assert(res1.isDefined)
  }
  test("Subsumption of stack"){ f =>
    val stateSolver = f.stateSolver

    val loc = AppLoc(fooMethod, SerializedIRLineLoc(1), isPre = false)

    val state = State(StateFormula(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil,
      Map(),Set(),Map(),AbstractTrace( Nil)),0)
    val state_ = state.copy(sf = state.sf.copy(callStack = CallStackFrame(dummyLoc, None, Map(
      StackVar("x") -> p1,
      StackVar("y") -> p2
    ))::Nil))
    assert(f.canSubsume(state,state_,esp))
    assert(!f.canSubsume(state_,state,esp))

  }
  test("Subsumption of abstract traces") { f =>
    val stateSolver = f.stateSolver

    val state = State(StateFormula(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil,
      Map(),Set(),Map(),AbstractTrace( Nil)),0)
    val state2 = state.copy(sf = state.sf.copy(callStack =
      state.callStack.head.copy(locals=Map(StackVar("x") -> p1, StackVar("y")->p2))::Nil))
    assert(f.canSubsume(state,state,esp))
    assert(f.canSubsume(state,state2,esp))
    assert(!f.canSubsume(state2,state,esp))

    val iFoo_a = AbsMsg(CBEnter, Set(("", "foo")), a :: Nil)
    val iBaz_a = AbsMsg(CBEnter, Set(("", "baz")), a :: Nil)
    val iBaz_b = AbsMsg(CBEnter, Set(("", "baz")), b :: Nil)
    val iBar_a = AbsMsg(CBEnter, Set(("", "bar")), a :: Nil)
    val iBar_c = AbsMsg(CBEnter, Set(("", "bar")), c :: Nil)
    val iFoo_c = AbsMsg(CBEnter, Set(("", "foo")), c :: Nil)

    val spec = new SpecSpace(Set(LSSpec(a::Nil, Nil, iFoo_a, iBaz_a)))

    //    val baseTrace1 = AbstractTrace(iBaz_b::Nil, Map(b->p1))
    //    val arrowTrace1 = AbstractTrace(iBar_c::iBaz_b::Nil, Map(b->p1, "c"->p2))
    val state_ = state.copy(sf = state.sf.copy(traceAbstraction = AbstractTrace(iBaz_b::Nil),
      pureFormula= Set(PureConstraint(b,Equals,p1))))
    val state__ = state.copy(sf = state.sf.copy(traceAbstraction = AbstractTrace(iBar_c::iBaz_b::Nil),
      pureFormula= Set(PureConstraint(b,Equals,p1), PureConstraint(c,Equals,p2))))

    // State I(a.foo())|>empty should subsume itself

    assert(f.canSubsume(state_,state_,spec))
    // I(a.foo()) can subsume I(a.foo()) |> a.bar()
    assert(f.canSubsume(state_,state__,spec))

    val spec2 = new SpecSpace(Set(LSSpec(a::Nil, Nil, NS(iFoo_a,iBar_a), iBaz_a)))
    //val baseTrace = AbstractTrace( iBaz_b::Nil, Map(b->p1))
    val state3_ = state.copy(sf = state.sf.copy(traceAbstraction = AbstractTrace( iBaz_b::Nil),
      pureFormula = Set(PureConstraint(b,Equals,p1))))

    // NI(a.foo(), a.bar()) can subsume itself
    val res = f.canSubsume(state3_, state3_,spec2)
    assert(res)

    val state3__ = state.copy(sf = state.sf.copy(traceAbstraction =
      AbstractTrace( iBar_c::iBaz_b::Nil),pureFormula= Set(PureConstraint(b,Equals,p1))))
    // NI(a.foo(), a.bar()) can subsume NI(a.foo(), a.bar()) |> c.bar()
    assert(f.canSubsume(state3_,state3__,spec2))

    // NI(a.foo(), a.bar()) cannot subsume NI(a.foo(), a.bar()) |> c.foo() /\ a==c
    // ifooc::Nil
    val fooBarArrowFoo = state.copy(sf = state.sf.copy(
      traceAbstraction = AbstractTrace(iFoo_c::iBaz_b::Nil),
      pureFormula= Set(PureConstraint(b,Equals,p1), PureConstraint(c,Equals,p1))))
    val resfoobarfoo = f.canSubsume(state3_, fooBarArrowFoo,spec2)
    assert(!resfoobarfoo)

    val iZzz_a = AbsMsg(CBEnter, Set(("", "zzz")), a :: Nil)
    val iZzz_d = AbsMsg(CBEnter, Set(("", "zzz")), d :: Nil)
    val spec3 = new SpecSpace(Set(
      LSSpec(a::Nil, Nil, NS(iFoo_a,iBar_a), iBaz_a),
      LSSpec(a::Nil, Nil, iFoo_a, iZzz_a)
    ))

    // NI(a.foo(), a.bar()) /\ I(a.foo()) should be subsumed by NI(a.foo(),a.bar())
    val s_foo_bar_foo = state.copy(sf = state.sf.copy(traceAbstraction =
      AbstractTrace(iBaz_b::iZzz_d::Nil),
      pureFormula = Set(PureConstraint(b,Equals,p1), PureConstraint(d,Equals,p1))))
    val s_foo_bar = state.copy(sf = state.sf.copy(traceAbstraction =
      AbstractTrace(iBaz_b::Nil),pureFormula= Set(PureConstraint(b,Equals,p1), PureConstraint(d,Equals,p1))))
    assert(f.canSubsume(s_foo_bar, s_foo_bar_foo,spec3))

    // Extra trace constraint does not prevent subsumption
    // NI(foo(a),bar(a)), I(foo(c))  can subsume  NI(foo(a),bar(a))
    val res2 = f.canSubsume(s_foo_bar_foo, s_foo_bar,spec3)
    assert(res2)

    // NI(foo(a),bar(a)), I(foo(c)) /\ a!=c cannot subsume  NI(foo(a),bar(a))
    val s_foo_bar_foo_notEq = state.copy(sf = state.sf.copy(traceAbstraction =
      AbstractTrace(iBaz_b::iZzz_d::Nil),
      pureFormula= Set(PureConstraint(b,Equals,p1), PureConstraint(d,Equals,p2))
        ++ Set(PureConstraint(p1, NotEquals, p2))
    ))

    val res3 = f.canSubsume(s_foo_bar_foo_notEq, s_foo_bar,spec3)
    assert(!res3)

    // Extra pure constraints should not prevent subsumption
    val fewerPure = State.topState.copy(sf = State.topState.sf.copy(
      pureFormula = Set(PureConstraint(p2, NotEquals, NullVal))))
    val morePure = fewerPure.copy(sf = fewerPure.sf.copy(pureFormula = fewerPure.pureFormula +
//      PureConstraint(p1, TypeComp, SubclassOf("java.lang.Object")) +
      PureConstraint(p1, NotEquals, p2),
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("java.lang.Object"),None,Set()))))
    assert(f.canSubsume(fewerPure, morePure,esp))

  }
  def mapToPure(m:Map[NamedPureVar,PureVar]):Set[PureConstraint] = m.keySet.map{
    (k:NamedPureVar) => PureConstraint(k,Equals,m(k))
  }
  def st(t:AbstractTrace, m:Map[NamedPureVar,PureVar]):State = st((t,m))
  def st(t:(AbstractTrace, Map[NamedPureVar,PureVar])):State = {
    State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = t._1, pureFormula = mapToPure(t._2)))
  }
  test("NI(foo(x),bar(x)) cannot subsume I(foo(x))"){ f =>
    //TODO: this test shows an encoding of state subsumption that is not provably in the EPR fragment of logic
    val stateSolver = f.stateSolver
    val pv = PureVar(1)

    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val zzzM = SubClassMatcher("","zzz","zzz")
    val yyyM = SubClassMatcher("","yyy","yyy")
    val iFoo_x = AbsMsg(CBEnter, fooM, x:: Nil)
    val iBar_x = AbsMsg(CBEnter, barM, x::Nil)
    val iZzz_x = AbsMsg(CBEnter, zzzM, x::Nil)
    val iZzz_y = AbsMsg(CBEnter, zzzM, y::Nil)
    val iYyy_x = AbsMsg(CBEnter, yyyM, x::Nil)
    val iYyy_y = AbsMsg(CBEnter, yyyM, y::Nil)
    val spec = new SpecSpace(Set(
      LSSpec(x::Nil, Nil, NS(iFoo_x, iBar_x),iZzz_x),
      LSSpec(x::Nil, Nil, iFoo_x, iYyy_x)
    ))
    val at1 = (AbstractTrace( iZzz_y::Nil), Map(y-> pv))
    val at2 = (AbstractTrace(iYyy_y::Nil), Map(y-> pv))
    val res = f.canSubsume(st(at1),st(at2),spec)
    assert(!res)
  }
  test("X -> p1 && p1:T1 cannot subsume X -> p1 && p1:T2 && p2:T1"){ f =>
    val stateSolver = f.stateSolver
    val pvy = PureVar(1)
    val pvy2 = PureVar(2)
    val fr = CallStackFrame(dummyLoc, None, Map(StackVar("x") -> pvy))
    val s1 = State.topState.copy(sf = State.topState.sf.copy(callStack = fr::Nil))
      .addTypeConstraint(pvy, BitTypeSet(BitSet(1)))
    val s2 = State.topState.copy(sf = State.topState.sf.copy(callStack = fr::Nil))
      .addTypeConstraint(pvy, BitTypeSet(BitSet(2)))
      .addTypeConstraint(pvy2, BitTypeSet(BitSet(1)))
    val res = f.canSubsume(s1,s2,esp)
    assert(!res)
    assert(f.canSubsume(s1,s1, esp))

  }
  test("x -> p1 * p1.f -> p2 && p2:T1 can subsume x -> p2 * p2.f -> p1 && p1:T1"){ f =>
    val stateSolver = f.stateSolver
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
    val res = f.canSubsume(s1,s2,esp)
    assert(res)
  }
  test("p1.f->p2 * p3.f->p2 can be subsumed by p1.f -> p2 * p3.f -> p4"){ f =>
    val stateSolver = f.stateSolver
    val sP2P2 = State.topState.copy(
      sf = State.topState.sf.copy(
        heapConstraints = Map(
          FieldPtEdge(p1,"f")->p2,
          FieldPtEdge(p3,"f")->p2
        )
      )
    )
    val sP2P4 = State.topState.copy(
      sf = State.topState.sf.copy(
        heapConstraints = Map(
          FieldPtEdge(p1,"f")->p2,
          FieldPtEdge(p3,"f")->p4
        )
      )
    )
    assert(f.canSubsume(sP2P4,sP2P2, esp))
    assert(!f.canSubsume(sP2P2,sP2P4, esp))
    assert(!f.canSubsume(sP2P4.addPureConstraint(PureConstraint(p2, Equals, p5))
      .addPureConstraint(PureConstraint(p5,Equals,p4)), sP2P4, esp))


    val another = sP2P4.addPureConstraint(PureConstraint(p2, NotEquals, p4))
    assert(!f.canSubsume(another, sP2P4, esp))

  }
  test("x -> p1 * p1.f -> p2 && p2:T1 cannot subsume x -> p2 * p2.f -> p1 && p1:T2"){ f =>
    val stateSolver = f.stateSolver
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
    val res = f.canSubsume(s1,s2,esp)
    assert(!res)
  }
  test("I(x.foo()) && I(z.bar(y)) cannot subsume I(x.foo())"){ f =>
    val stateSolver = f.stateSolver
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val yyyM = SubClassMatcher("","bar","yyy")
    val zzzM = SubClassMatcher("","bar","zzz")
    val iFoo_x = AbsMsg(CBEnter, fooM, x :: Nil)
    val iBar_zy = AbsMsg(CBEnter, barM, z::y ::Nil)
    val iYyy_x = AbsMsg(CBEnter, yyyM, x::Nil)
    val iYyy_k = AbsMsg(CBEnter, yyyM, k::Nil)
    val iZzz_z = AbsMsg(CBEnter, zzzM, z::Nil)
    val iZzz_j = AbsMsg(CBEnter, zzzM, j::Nil)
    val spec = new SpecSpace(Set(
      LSSpec(x::Nil, Nil, iFoo_x, iYyy_x),
      LSSpec(z::Nil, y::Nil, iBar_zy, target = iZzz_z)
    ))

    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    val s1 = st((AbstractTrace(iYyy_k::iZzz_j::Nil), Map(k -> pv1, j->pv2)))
    val s2 = st((AbstractTrace(iYyy_k::Nil), Map(k -> pv1)))

    val res = f.canSubsume(s1,s2,spec)
    assert(!res)

    val res2 = f.canSubsume(s2,s1,spec)
    assert(res2)
  }

  test("I(y.foo()) && (Not I(y.bar())) && y:T2 cannot subsume I(x.foo()) && x:T2"){ f =>
    val stateSolver = f.stateSolver
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val iFoo_x = AbsMsg(CBEnter, fooM, x::Nil)
    val iFoo_z = AbsMsg(CBEnter, fooM, z::Nil)
    val iBar_z = AbsMsg(CBEnter, barM, z::Nil)
    val notbar_tgt_z = AbsMsg(CBEnter, SubClassMatcher("","notbar_tgt","notbar_tgt"), z::Nil)
    val notbar_tgt_a = AbsMsg(CBEnter, SubClassMatcher("","notbar_tgt","notbar_tgt"), a::Nil)
    val foo_tgt_x = AbsMsg(CBEnter, SubClassMatcher("","foo_tgt","foo_tgt"), x::Nil)
    val foo_tgt_b = AbsMsg(CBEnter, SubClassMatcher("","foo_tgt","foo_tgt"), b::Nil)
    val spec = new SpecSpace(Set(
      LSSpec(z::Nil, Nil, And(iFoo_z,Not(iBar_z)), notbar_tgt_z),
      LSSpec(x::Nil, Nil, iFoo_x, foo_tgt_x)
    ))
    val s1 = st(AbstractTrace(notbar_tgt_a::Nil), Map(a -> p2))
      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))//.addTypeConstraint(p1,BitTypeSet(BitSet(1)))
    val s2 = st(
      AbstractTrace(foo_tgt_b::Nil), Map(b -> p1)).addTypeConstraint(p1,BitTypeSet(BitSet(2)))
//      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))
    val res = f.canSubsume(s1,s2,spec)
    assert(!res)

    // I(x.foo()) && x:T2 can subsume I(y.foo()) && (Not I(y.bar())) && y:T2

    val res2 = f.canSubsume(s2,s1, spec)
    assert(res2)
  }
  test("|>tgt(x) can be subsumed by |>"){ f =>
    val stateSolver = f.stateSolver
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val tgtM = SubClassMatcher("","tgt","tgt")
    val iFoo_x = AbsMsg(CBEnter, fooM, x::Nil)
    val iBar_x = AbsMsg(CBEnter, barM, x::Nil)
    val iTgt_x = AbsMsg(CBEnter, tgtM, x::Nil)
    val iTgt_a = AbsMsg(CBEnter, tgtM, a::Nil)
    val spec = new SpecSpace(Set(
      LSSpec(x::Nil, Nil, NS(iFoo_x, iBar_x), iTgt_x)
    ))
    val s1 = st(AbstractTrace(iTgt_a::Nil), Map(a->p1)).addTypeConstraint(p1,BitTypeSet(BitSet(1)))
    val s2 = st(AbstractTrace(Nil),Map())
      .addTypeConstraint(p1,BitTypeSet(BitSet(1)))
    assert(f.canSubsume(s2,s1,spec))
    assert(!f.canSubsume(s1,s2,spec))

    val s1h = s1.copy(sf = s1.sf.copy(heapConstraints = Map(FieldPtEdge(p1,"f")->p2)))
    val s2h = s2.copy(sf = s2.sf.copy(heapConstraints = Map(FieldPtEdge(p1,"f")->p2)))
    assert(f.canSubsume(s2h,s1h,spec))
    assert(!f.canSubsume(s1h,s2h,spec))
  }
  test("|>bar(x,y)|>foo(x) && y =/≠ null  under spec bar(x,null) <= foo(x)") {f =>
    val stateSolver = f.stateSolver
    val fooM = SubClassMatcher("","foo\\(","foo")
    val barM = SubClassMatcher("","bar\\(","bar")
    val iFoo_x = AbsMsg(CBEnter, fooM, x::Nil)
    val iFoo_a = AbsMsg(CBEnter, fooM, a::Nil)
    val iBar_xy = AbsMsg(CBEnter, barM, x::y::Nil)
    val iBar_ab = AbsMsg(CBEnter, barM, a::b::Nil)
    val iBar_xN = AbsMsg(CBEnter, barM, x::NullVal::Nil)

    val spec = new SpecSpace(Set(LSSpec(x::Nil, Nil, iBar_xN, iFoo_x)))

    val s = st(AbstractTrace(iBar_ab::iFoo_a::Nil), Map(a -> p1, b->p2))

    val sNN = s.addPureConstraint(PureConstraint(p2, NotEquals, NullVal))
    assert(stateSolver.witnessed(sNN, spec).isEmpty)

    val sNull = s.addPureConstraint(PureConstraint(p2, Equals, NullVal))
    assert(stateSolver.witnessed(sNull, spec).isDefined)

    // Test const under negation
    val bazM = SubClassMatcher("","baz\\(","baz")
    val iBaz_x = AbsMsg(CBEnter, bazM, x::Nil)
    val spec2 = new SpecSpace(Set(LSSpec(x::Nil, y::Nil, NS(iBar_xy, iBar_xN), iFoo_x)))

    assert(stateSolver.simplify(sNull, spec2).isEmpty)

    assert(stateSolver.simplify(sNN, spec2).isDefined)
  }

  test("NI(x.foo(),x.baz()) && (not I(z.bar())) && x:T2 && z:T1 cannot subsume NI(x.foo(),x.baz()) && x:T2"){ f =>
    val stateSolver = f.stateSolver
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val bazM = SubClassMatcher("","baz","baz")
    val niTgt_x = AbsMsg(CBEnter, SubClassMatcher("","niTgtM","niTgtM"), x::Nil)
    val niTgt_a = AbsMsg(CBEnter, SubClassMatcher("","niTgtM","niTgtM"), a::Nil)
    val notTgt_z = AbsMsg(CBEnter, SubClassMatcher("", "notTgtM", "notTgtM"), z::Nil)
    val notTgt_b = AbsMsg(CBEnter, SubClassMatcher("", "notTgtM", "notTgtM"), b::Nil)
    val iFoo_x = AbsMsg(CBEnter, fooM, x::Nil)
    val iBaz_x = AbsMsg(CBEnter, bazM, x::Nil)
    val iBar_z = AbsMsg(CBEnter, barM, z::Nil)

    val spec = new SpecSpace(Set(
      LSSpec(x::Nil, Nil, NS(iFoo_x, iBaz_x), niTgt_x),
      LSSpec(z::Nil, Nil, Not(iBar_z), notTgt_z)
    ))
    val s1 = st(AbstractTrace(niTgt_a::notTgt_b::Nil), Map(b->p1,a -> p2))
      .addTypeConstraint(p1,BitTypeSet(BitSet(1)))
      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))
    val s2 = st(AbstractTrace(niTgt_a::Nil), Map(a -> p1))
      .addTypeConstraint(p1, BitTypeSet(BitSet(2)))
    assert(!f.canSubsume(s1,s2,spec))
    assert(f.canSubsume(s2,s1,spec))

  }
  test("|>bar(p1,p2)|>foo(p1) && p2=... S: I(bar(p1,true))<= foo(p1)"){ f=>
    val stateSolver = f.stateSolver

    // test v.setEnabled(false)
    val specClickDis = new SpecSpace(Set(ViewSpec.clickWhileNotDisabled))
    val isetEnabled_x_y = AbsMsg(CIExit, ViewSpec.setEnabled, TopVal::x::yy::Nil)
    val iOnClick_z = AbsMsg(CBEnter, ViewSpec.onClick, TopVal::z::Nil)
    val iSetOnClickListener_x_z = ViewSpec.setOnClickListenerI.copyMsg(lsVars = TopVal::x::z::Nil)
    val sDis = st(AbstractTrace(rightOfArrow = iSetOnClickListener_x_z::isetEnabled_x_y::iOnClick_z::Nil),
      Map(x->p1, yy->p2, z->p3))
    val sDis_False = sDis.addPureConstraint(PureConstraint(p2, Equals, BoolVal(false)))
    assert(stateSolver.witnessed(sDis_False,specClickDis).isEmpty)


    val fooM = SubClassMatcher("","foo\\(","foo")
    val barM = SubClassMatcher("","bar\\(","bar")

    val iFoo_x = AbsMsg(CBEnter, fooM, x :: Nil)
    val iFoo_a = AbsMsg(CBEnter, fooM, a :: Nil)
    val iBar_x_y = AbsMsg(CBEnter, barM, x::y::Nil)
    val iBar_a_b = AbsMsg(CBEnter, barM, a::b::Nil)
    val iBar_x_true = AbsMsg(CBEnter, barM, x::BoolVal(true)::Nil)

    val spec = new SpecSpace(Set(LSSpec(x::Nil, Nil, iBar_x_true, iFoo_x)))
    val s = st(AbstractTrace(rightOfArrow = iBar_a_b::iFoo_a::Nil), Map(a->p1, b->p2))
    val sFalse = s.addPureConstraint(PureConstraint(p2, Equals, IntVal(0)))
    assert(stateSolver.witnessed(sFalse, spec).isEmpty)

    val sTrue = s.addPureConstraint(PureConstraint(p2, Equals, IntVal(1)))
    assert(stateSolver.witnessed(sTrue,spec).isDefined)

    val specNot = new SpecSpace(Set(LSSpec(x::Nil, Nil, Not(iBar_x_true), iFoo_x)))
    assert(stateSolver.simplify(sFalse, specNot).isDefined)
    assert(stateSolver.simplify(sTrue, specNot).isEmpty)


  }
  test("|>x.call() can subsume |> y.unsubscribe() |> x.call()"){ f =>
    val stateSolver = f.stateSolver
    // Test with no wildcards
    val callSig = SpecSignatures.RxJava_call
    val unsubSig = SpecSignatures.RxJava_unsubscribe
    val subSig = SpecSignatures.RxJava_subscribe
    val s = NamedPureVar("s")
    val s1 = NamedPureVar("s1")
    val l = NamedPureVar("l")
    val l1 = NamedPureVar("l1")

    val subI = AbsMsg(CIExit, subSig, s::TopVal::l::Nil)
    val unsubI = AbsMsg(CIExit, unsubSig, TopVal::s::Nil)
    val unsubITgt = AbsMsg(CIExit, unsubSig, TopVal :: s1 :: Nil)
    val callI = AbsMsg(CBEnter, callSig, TopVal::l::Nil)
    val callITgt = AbsMsg(CBEnter, callSig, TopVal::l1::Nil)
    val spec = new SpecSpace(Set(
      LSSpec(l::Nil, s::Nil, NS(subI, unsubI),callI)
    ))
    val callSpec = RxJavaSpec.call
    val specReal = new SpecSpace(Set(callSpec))
    val s_1 = st(AbstractTrace(callITgt::Nil), Map(l1 -> p1))
    val s_2 = st(AbstractTrace(unsubITgt::callITgt::Nil), Map(s1->p2, l1->p1))
    assert(f.canSubsume(s_1,s_2, specReal))
    assert(!f.canSubsume(s_2,s_1,specReal)) // forall v ... arg(omega(...)) != v ...?

    // Test with real spec
    val callTgt_x = SpecSignatures.RxJava_call_entry.copyMsg(lsVars = TopVal::x::Nil)
    val unsubTgt_y =  SpecSignatures.RxJava_unsubscribe_exit.copyMsg(lsVars = TopVal::y::Nil)
    val destTgt_z = SpecSignatures.Activity_onDestroy_exit.copyMsg(lsVars = TopVal::z::Nil)
    val st1 = st(AbstractTrace(callTgt_x::Nil),Map(x->p1))
      .addTypeConstraint(p1,BitTypeSet(BitSet(1)))

    val s1h = st1.copy(sf = st1.sf.copy(heapConstraints = Map(
      FieldPtEdge(p3, "subscription")-> p2,
    )))

    val s2 = st(AbstractTrace(unsubTgt_y::destTgt_z::callTgt_x::Nil), Map(x->p1, y->p2, z->p3))
      .addTypeConstraint(p1,BitTypeSet(BitSet(1)))
      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))


    val s2h = s2.copy(sf = s2.sf.copy(heapConstraints = Map(
      FieldPtEdge(p3, "subscription")-> p2,
    )))

    assert(stateSolver.simplify(s1h,specReal).isDefined)
    assert(stateSolver.simplify(s2h,specReal).isDefined)

    assert(f.canSubsume(s1h,s1h,specReal))
    assert(!f.canSubsume(s2h,s1h,specReal))
    assert(f.canSubsume(s1h,s2h, specReal))

    val spec2 = new SpecSpace(LifecycleSpec.spec + callSpec)

    assert(f.canSubsume(s1h,s2h, spec2))
    assert(!f.canSubsume(s2h,s1h,spec2))
  }

  test("|>v.onClick() subsume |> v2 = a.findViewByID() |>v.onClick()"){ f =>
    val stateSolver = f.stateSolver
    val v = NamedPureVar("v")
    val v2 = NamedPureVar("v2")
    val clickTgt = AbsMsg(CBEnter, ViewSpec.onClick, TopVal::v::Nil)
    val clickTgt_x = AbsMsg(CBEnter, ViewSpec.onClick, TopVal::x::Nil)
    val findVTgt = AbsMsg(CBEnter, SpecSignatures.Activity_findView, v2::a::Nil)
    val findVTgt_yz = AbsMsg(CBEnter, SpecSignatures.Activity_findView, y::z::Nil)
    val findV = AbsMsg(CBEnter, SpecSignatures.Activity_findView, v::a::Nil)


    // Test for timeout with simplified click spec
    val spec = new SpecSpace(Set(
      LSSpec(v::Nil, a::Nil, findV, clickTgt),
      ViewSpec.viewOnlyReturnedFromOneActivity
    ))
    val st1 = st(AbstractTrace(clickTgt_x::Nil), Map(x -> p1, z->p4))
    val st2 = st(AbstractTrace(FreshRef(c)::findVTgt_yz::clickTgt_x::Nil),
      Map(x -> p1, y -> p2, z -> p3, c->p4))
    //val s1enc = EncodingTools.rhsToPred(st1.sf.traceAbstraction.rightOfArrow, spec)
    //val s2enc = EncodingTools.rhsToPred(st2.sf.traceAbstraction.rightOfArrow, spec)
    //For s2 we can choose p-y and p-z such that empty trace is accepted.
    //s1 cannot accept the empty trace
    // Therefore s1 can be subsumed by s2 but not vis versa
    assert(!f.canSubsume(st1,st2, spec))
    assert(f.canSubsume(st2, st1, spec))

//    val specfull = new SpecSpace(Set(
//      ViewSpec.clickWhileActive,
//      ViewSpec.viewOnlyReturnedFromOneActivity
//    ))
//    val res3 = f.canSubsume(st1, st2, spec)
//    val res4 = f.canSubsume(st2,st1, spec)
  }
  ignore("duplicate resume/onClickListener should subsume"){ f =>
    val stateSolver = f.stateSolver
    val specs = new SpecSpace(Set(ViewSpec.clickWhileNotDisabled, ViewSpec.viewOnlyReturnedFromOneActivity))

    // I(CBEnter I_CBEnter_Activity_onResume ( _,p-5 );
    // I(CIExit I_CIExit_Activity_findView ( p-4,p-5 );
    // FreshRef(p-3);
    // I(CIExit I_CIExit_View_setOnClickListener ( _,p-4,p-3 );

    // I(CBEnter I_CBEnter_Activity_onPause ( _,p-1 );
    // I(CBExit I_CBExit_Activity_onPause ( _,p-1 );
    // I(CBEnter I_CBEnter_ViewOnClickListener_onClick ( _,p-2 )))
    val s1 = st(AbstractTrace( //TODO: finish filling out abstract state to test - I suspect that this should subsume one "loop" but isn't in the real version
      FreshRef(p3)::
        ViewSpec.setOnClickListenerI.copy(lsVars = TopVal::p4::p3::Nil)::
        Nil),
      Map())
    val s2 = st(AbstractTrace( Nil),Map())
    ???
  }
  test("|>y = _.subscribe(x)|> y.unsubscribe() |> x.call() should be subsumed by |> x.call()"){ f =>
    val stateSolver = f.stateSolver
    // Test with no wildcards
    val s = NamedPureVar("s")
    val s1 = NamedPureVar("s1")
    val s2 = NamedPureVar("s2")
    val l = NamedPureVar("l")
    val l1 = NamedPureVar("l1")
    val l2 = NamedPureVar("l2")
    val callSig = SpecSignatures.RxJava_call
    val unsubSig = SpecSignatures.RxJava_unsubscribe
    val subSig = SpecSignatures.RxJava_subscribe

    val subI = AbsMsg(CIExit, subSig, s::l::Nil)
    val subITgt = AbsMsg(CIExit, subSig, s1::l1::Nil)
    val unsubI = AbsMsg(CIExit, unsubSig, TopVal::s::Nil)
    val unsubITgt = AbsMsg(CIExit, unsubSig, TopVal::s2::Nil)
    val callI = AbsMsg(CBEnter, callSig, l::Nil)
    val callITgt = AbsMsg(CBEnter, callSig, l2::Nil)
    val spec = new SpecSpace(Set(
      LSSpec(l::Nil, s::Nil, NS(subI, unsubI),callI)
    ))
    val st1 = st(AbstractTrace(subITgt::unsubITgt::callITgt::Nil), Map(s1->p2, l1->p1))
//    assert(stateSolver.simplify(s,spec).isEmpty) //Note: case exists where there may be a second sub
    val st2 = st(AbstractTrace(callITgt::Nil), Map(l2->p1)) //TODO: Shouldn't this subsume since s2.unsub may be same as s1?
    // val st2Enc = EncodingTools.rhsToPred(st2.sf.traceAbstraction.rightOfArrow, spec)
    // val st1Enc = EncodingTools.rhsToPred(st1.sf.traceAbstraction.rightOfArrow, spec)
    // Note: with no constraint on unsubscribe it may be different value resulting in wit
    assert(!f.canSubsume(st2,st1,spec))

    val s_1 = st(AbstractTrace(subITgt::unsubITgt::callITgt::Nil), Map(s2->p2,s1->p2, l2->p1, l1->p1))
    val s_2 = st(AbstractTrace(callITgt::Nil), Map(l2->p1))
    assert(f.canSubsume(s_2,s_1,spec))
  }
  test("A trace that requires an object be used before it is created should be refuted"){f =>
    val callSig = SpecSignatures.RxJava_call
    val unsubSig = SpecSignatures.RxJava_unsubscribe
    val subSig = SpecSignatures.RxJava_subscribe
    val s = NamedPureVar("s")
    val s1 = NamedPureVar("s1")
    val s2 = NamedPureVar("s2")
    val l = NamedPureVar("l")
    val l1 = NamedPureVar("l1")
    val l2 = NamedPureVar("l2")
    val x1 = NamedPureVar("x1")

    val subI = AbsMsg(CIExit, subSig, s::l::Nil)
    val subITgt = AbsMsg(CIExit, subSig, s1::l1::Nil)
    val unsubI = AbsMsg(CIExit, unsubSig, TopVal::s::Nil)
    val unsubITgt = AbsMsg(CIExit, unsubSig, TopVal::s2::Nil)
    val callI = AbsMsg(CBEnter, callSig, l::Nil)
    val callITgt = AbsMsg(CBEnter, callSig, l2::Nil)
    val spec = new SpecSpace(Set(
      LSSpec(l::Nil, s::Nil, NS(subI, unsubI),callI)
    ))
    val stateSolver = f.stateSolver
    val s_ref = st(AbstractTrace(FreshRef(x1)::callITgt::Nil),
      Map(l2->p2, x1->p2))
    assert(stateSolver.simplify(s_ref,spec).isEmpty)
  }
  test("an arbitrary state s1 should subsume s1 with a ref added"){f =>
    val stateSolver = f.stateSolver
    val s1 = st(AbstractTrace(FreshRef(x)::Nil), Map(x->p1)).setSimplified()
    val s2 = st(AbstractTrace(FreshRef(x)::FreshRef(y)::Nil), Map(x->p1,y->p2)).setSimplified()

    assert(f.canSubsume(s1,s2,esp))
    //Note that an erroneous "OR" between Refs causes timeout, may cause timeouts in future due to negation

    // Note: both s1 and s2 should be infeasible since variable x can't point to addr p1 and p1 is created in the future
    // Sound to drop this constraint
    // Precision is not lost since transfer functions handle this constraint
    // assert(f.canSubsume(s2,s1,esp))
    val s2NE = s2.addPureConstraint(PureConstraint(p1, NotEquals, p2))
    assert(f.canSubsume(s2NE,s1,esp))
  }
  test("|> y.onDestroy() |>null = x.getActivity() not refuted"){fTest =>
    val stateSolver = fTest.stateSolver
    val f = NamedPureVar("f")
    val g = NamedPureVar("g")
    val getActivityTgt_e_f = SpecSignatures.Fragment_get_activity_exit.copy(lsVars = p1::p2::Nil)
    val onDestroyTgt_d = SpecSignatures.Fragment_onDestroy_exit.copy(lsVars = TopVal::p3::Nil)
    val onCreateTgt_g= SpecSignatures.Fragment_onActivityCreated_entry.copy(lsVars = TopVal::p3::Nil)

    val s = st(AbstractTrace(onDestroyTgt_d::getActivityTgt_e_f::Nil),Map())
      .addPureConstraint(PureConstraint(p1, Equals, NullVal))
    val spec = new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNonNull,
      FragmentGetActivityNullSpec.getActivityNull))
    assert(stateSolver.simplify(s,spec).isDefined)

    // empty trace in abstraction if x = y
    val s2 = s.addPureConstraint(PureConstraint(p2, Equals, p3))
    assert(stateSolver.witnessed(s2,spec).isDefined)

    // |> y.onCreate() |> null = x.getActivity() not refuted unless x = y
    val s3 = st(AbstractTrace(onCreateTgt_g::getActivityTgt_e_f::Nil), Map())
      .addPureConstraint(PureConstraint(p1, Equals, NullVal))
    assert(stateSolver.simplify(s3,spec).isDefined)

    val s4 = s3.addPureConstraint(PureConstraint(p3, Equals, p2))
    assert(stateSolver.simplify(s4, spec).isEmpty)
  }
  test("|>null = x.getActivity() can not subsume |> x.onDestroy() |>null = x.getActivity()"){ fTest =>
    val stateSolver = fTest.stateSolver
    val f = NamedPureVar("f")
    val g = NamedPureVar("g")
    val getActivityTgt_e_f = SpecSignatures.Fragment_get_activity_exit.copy(lsVars = p1::p2::Nil)
    val onDestroyTgt_d = SpecSignatures.Fragment_onDestroy_exit.copy(lsVars = TopVal::p2::Nil)
    val unsubscribe_g = SpecSignatures.RxJava_unsubscribe_exit.copy(lsVars = TopVal::g::Nil)
    val s1 = st(AbstractTrace(getActivityTgt_e_f::Nil), Map())
      .addPureConstraint(PureConstraint(p1, Equals, NullVal))
    val s2 = st(AbstractTrace(onDestroyTgt_d::getActivityTgt_e_f::Nil),Map())
      .addPureConstraint(PureConstraint(p1, Equals, NullVal))
    val spec = new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNonNull,
      FragmentGetActivityNullSpec.getActivityNull))

    assert(!fTest.canSubsume(s1,s2,spec))
    assert(fTest.canSubsume(s2,s1, spec))
  }
  ignore("I(x.foo(y)) can subsume I(x1.foo(y1)) && not ref(z)"){ f =>
    //TODO: |>
    val stateSolver = f.stateSolver
    val x1 = NamedPureVar("x1")
    val y1 = NamedPureVar("y1")
    val fooM = SubClassMatcher("","foo","foo")
    //    val iFoo_x_y = I(CBEnter, fooM, "x" :: "y" :: Nil)
    //    val iFoo_x1_y1 = I(CBEnter, fooM, "x1"::"y1" :: Nil)

    val iFoo_x_y = AbsMsg(CBEnter, fooM, x::y :: Nil)
    val iFoo_x1_y1 = AbsMsg(CBEnter, fooM, x1::y1 :: Nil)


    val pvy = PureVar(1)
    val pvy2 = PureVar(2)
    val pvy3 = PureVar(3)


    val t2 = AbstractTrace(iFoo_x1_y1, Nil, Map("y1" -> pvy2))
    val t3 = AbstractTrace(Not(FreshRef(z)), Nil, Map(z -> pvy3))
    val s1 = st(AbstractTrace(iFoo_x_y::Nil), Map(y-> pvy))
//    val s2 = s(Set(t2,t3))
    val s2 = ???
    val startTime1 = System.currentTimeMillis()
    val res = f.canSubsume(s1,s2,esp)
    println(s"s1 can subsume s2 time: ${(System.currentTimeMillis() - startTime1).toFloat/1000}")
    assert(res)

    val startTime2 = System.currentTimeMillis()
    val res2 = f.canSubsume(s2,s1,esp)
    println(s"s1 can subsume s2 time: ${(System.currentTimeMillis() - startTime2).toFloat/1000}")
    assert(!res2)
  }
  test("I(x.foo(y)) && y:T1 cannot subsume I(x1.foo(y1)) && y:T2"){ f =>
    // cannot subsume if types must be different
    val stateSolver = f.stateSolver
    val fooM = SubClassMatcher("","foo","foo")
    val iFoo_x_y = AbsMsg(CBEnter, fooM, x :: y :: Nil)
    val iFoo_x1_y1 = AbsMsg(CBEnter, fooM, x1::y1 :: Nil)
    val tgt_foo1_x_y = AbsMsg(CBEnter, SubClassMatcher("","tgt_foo_1","tgt_foo_1"),x::y::Nil)
    val tgt_foo1_a_b = AbsMsg(CBEnter, SubClassMatcher("","tgt_foo_1","tgt_foo_1"),a::b::Nil)
    val tgt_foo2_x1_y1 = AbsMsg(CBEnter, SubClassMatcher("","tgt_foo_2","tgt_foo_2"),x1::y1::Nil)
    val tgt_foo2_c_d = AbsMsg(CBEnter, SubClassMatcher("","tgt_foo_2","tgt_foo_2"),c::d::Nil)
    val spec = new SpecSpace(Set(
      LSSpec(x::y::Nil,Nil,iFoo_x_y, tgt_foo1_x_y),
      LSSpec(x1::y1::Nil,Nil,iFoo_x1_y1, tgt_foo2_x1_y1)
    ))

    val t1 = (AbstractTrace(tgt_foo1_a_b::Nil), Map(b-> p1, a->p3))
    val t2 = (AbstractTrace(tgt_foo2_c_d::Nil), Map(d -> p2, c->p3))
    val s1 = st(t1).addTypeConstraint(p3,BitTypeSet(BitSet(1)))
      .addTypeConstraint(p1, BitTypeSet(BitSet(1)))
    val s2 = st(t2).addTypeConstraint(p3, BitTypeSet(BitSet(1)))
      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))
    val res = f.canSubsume(s1,s2,spec)
    assert(!res)
    assert(!f.canSubsume(s2,s1,spec))

    //s3: I(x.foo(y)) && y:T1 can subsume s4: I(x1.foo(y1)) && y:T1
    // can subsume when types are compatible
    val s3 = st(t1).addTypeConstraint(p3,BitTypeSet(BitSet(1)))
      .addTypeConstraint(p1, BitTypeSet(BitSet(2)))
    val s4 = st(t2).addTypeConstraint(p3, BitTypeSet(BitSet(1)))
      .addTypeConstraint(p2,BitTypeSet(BitSet(2)))
    assert(f.canSubsume(s3,s4,spec))
    assert(f.canSubsume(s4,s3,spec))
  }
  ignore("I(x.foo(y)) && y:T1 cannot subsume I(x.foo(y))|>I(x1.foo(y1)) && I(x2.foo(y2)) && y2:T2"){f =>
    //TODO: |>
    val stateSolver = f.stateSolver
    val x2 = NamedPureVar("x2")
    val y2 = NamedPureVar("y2")
    val fooM = SubClassMatcher("","foo","foo")
    val iFoo_x_y = AbsMsg(CBEnter, fooM, x :: y :: Nil)
    val iFoo_x1_y1 = AbsMsg(CBEnter, fooM, x1::y1 :: Nil)
    val iFoo_x2_y2 = AbsMsg(CBEnter, fooM, x2::y2 :: Nil)
    val pvy = PureVar(1)
    val pvy2 = PureVar(2)
    //I(x.foo(y)) && y:T1
    val s1 = st(AbstractTrace(iFoo_x_y::Nil), Map(y->pvy)).addTypeConstraint(pvy, BitTypeSet(BitSet(1)))

    //I(x.foo(y))|>I(x1.foo(y1)) && I(x2.foo(y2)) && y:T1 && y2:T2
    //"y"->pvy, "y2"->pvy2
    val t2 = (AbstractTrace(iFoo_x_y::iFoo_x1_y1::Nil),Map(y->pvy))
    val t3 = (AbstractTrace(iFoo_x2_y2::Nil),Map(y2->pvy2))
    // add y:T1 && y2:T2
//    val s2 = s(Set(t3))
//    val s2 = s(Set(t2,t3))
//      .addTypeConstraint(pvy2, BitTypeSet(BitSet(2)))
//      .addTypeConstraint(pvy, BitTypeSet(BitSet(1)))
    val s2 = ???
    val res = f.canSubsume(s1,s2,esp)
    assert(!res)
  }
  ignore("I(x.foo()) && I(x.bar()) |> y.foo() cannot subsume I(x.foo()) && I(x.bar()) |> y.bar()") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver
    // I(x.foo()) && I(x.bar())
    val v = NamedPureVar("v")
    val fooM = SubClassMatcher("","foo","foo")
    val barM = SubClassMatcher("","bar","bar")
    val iFoo = AbsMsg(CBEnter, fooM, a :: Nil)
    val iBar = AbsMsg(CBEnter, barM, a :: Nil)
    val iFoo_b = AbsMsg(CBEnter, fooM, b :: Nil)
    val iBar_b = AbsMsg(CBEnter, barM, b :: Nil)
    val foobar = And(iFoo,iBar)
    val followsFoo = AbstractTrace(foobar, iFoo_b::Nil,Map())
    val followsBar = AbstractTrace(foobar, iBar_b::Nil, Map())
    val res = f.canSubsume(st(followsFoo,Map()),st(followsBar,Map()),esp)
    assert(!res)

    // a: I(v = findView(a)) && NI( onDestroy(a) , onCreate(a))
    val fv = SubClassMatcher("","findView","findView")
    val de = SubClassMatcher("","onDestroy","onDestroy")
    val cr = SubClassMatcher("","onCreate","onCreate")
    val findView = AbsMsg(CIExit, fv, v::a::Nil)
    val onDestroy = AbsMsg(CBExit, de, TopVal::a::Nil)
    val onCreate = AbsMsg(CBEnter, cr, TopVal::a::Nil)
    val acl = And(findView, NS(onDestroy, onCreate))

    val subsumer = AbstractTrace(acl, AbsMsg(CBEnter, cr, TopVal::b::Nil)::
      AbsMsg(CIExit,fv,v::b::Nil)::Nil,Map())

    val subsumee = AbstractTrace(acl, AbsMsg(CBExit,de,TopVal::b::Nil)::Nil,Map())
    val res2 = f.canSubsume(st(subsumer,Map()),st(subsumee,Map()),esp)
    assert(!res2)
    val res3 = f.canSubsume(st(subsumee,Map()), st(subsumer,Map()),esp)
    assert(res3)
  }
  ignore("Subsumption of unrelated trace constraint") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver

    val ifooa = AbsMsg(CBEnter, Set(("", "foo")), a :: Nil)
    val ifoob = AbsMsg(CBEnter, Set(("", "foo")), b :: Nil)
    val state0 = State.topState.copy(sf = State.topState.sf.copy(
      traceAbstraction = AbstractTrace(ifooa, Nil, Map(a->p1))
    ))
    val state1 = State.topState.copy(sf = State.topState.sf.copy(
      pureFormula = Set(PureConstraint(p1, NotEquals, p2)),
      traceAbstraction = AbstractTrace(ifooa, ifoob::Nil, Map(a->p1, b->p2))
    ))
    assert(f.canSubsume(state0,state1, esp))
  }

  ignore("Subsumption of abstract trace where type info creates disalias") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver

    val p1t = BoundedTypeSet(Some("String"), None, Set())
    val p2t = BoundedTypeSet(Some("Foo"), None, Set())
    val loc = AppLoc(fooMethod, SerializedIRLineLoc(1), isPre = false)

    assert(p1t.intersect(p2t).isEmpty)


    val ifoo = AbsMsg(CBEnter, Set(("", "foo")), a :: Nil)
    val ifoob = AbsMsg(CBEnter, Set(("", "foo")), b :: Nil)
    val state = State.topState.copy(sf = State.topState.sf.copy(traceAbstraction = AbstractTrace(ifoo, Nil, Map(a->p1))))
    val state2 = State.topState.copy(sf = State.topState.sf.copy(
      traceAbstraction = AbstractTrace(ifoo, ifoob::Nil, Map(a->p1, b->p2)),
//      pureFormula = Set(PureConstraint(p1, NotEquals, p2)) // this constraint is enforced by the type constraints below
      typeConstraints = Map(p1 -> p1t, p2->p2t)
    ))
    assert(f.canSubsume(state,state2, esp))
  }

  ignore("Refute trace with multi arg and multi var (bad arg fun skolemization caused bug here)") { f =>
    //TODO: |>
    val stateSolver = f.stateSolver

    val loc = AppLoc(fooMethod, SerializedIRLineLoc(1), isPre = false)

    val ifoo = AbsMsg(CBEnter, Set(("", "foo")),  TopVal::a :: Nil)
    val ibar = AbsMsg(CBEnter, Set(("", "bar")),  TopVal::a :: Nil)
    val ibarc = AbsMsg(CBEnter, Set(("", "bar")), TopVal::c :: Nil)

    val at = AbstractTrace(NS(ifoo,ibar), ibarc::Nil, Map(a->p1, c->p1))
    val state = State(StateFormula(
      CallStackFrame(dummyLoc, None, Map(StackVar("x") -> p1)) :: Nil, Map(), Set(),Map(), at), 0)
    val res = stateSolver.simplify(state,esp)
    assert(res.isEmpty)
  }
  test("Subsumption of pure formula including type information"){ f =>
    val stateSolver = f.stateSolver
    // (x->p1 && p1 <: Object) can not be subsumed by (x->p1 && p1 <:Foo)
    val state_ = state.copy(sf = state.sf.copy(
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("Foo"),None,Set())),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    val state__ = state.copy(sf = state.sf.copy(
      typeConstraints = Map(p1 -> BoundedTypeSet(Some("java.lang.Object"),None,Set())),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    assert(!f.canSubsume(state_, state__,esp))

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
    assert(f.canSubsume(state1__, state1_,esp))
    assert(!f.canSubsume(state1_, state1__,esp))

    // (x->p1 && p1 <: Foo) can be subsumed by (x->p1 && p1 <:Object)
    assert(f.canSubsume(state__, state_,esp))
    assert(f.canSubsume(state_, state_,esp))

    // Combine type constraints and trace constraints
    val iFoo = AbsMsg(CBEnter, Set(("", "foo")), a :: Nil)
    val iBar = AbsMsg(CBEnter, Set(("", "bar")), a :: Nil)
    val iBaz = AbsMsg(CBEnter, Set(("", "baz")), a :: Nil)
    val iBaz_b = AbsMsg(CBEnter, Set(("", "baz")), b :: Nil)
    val spec = new SpecSpace(Set(LSSpec(a::Nil,Nil,NS(iFoo,iBar),iBaz)))

    val formula = (AbstractTrace(iBaz_b::Nil), Map(b->p1))
    val state2_ = state_.copy(sf = state_.sf.copy(
      traceAbstraction = formula._1, pureFormula = state_.pureFormula ++ mapToPure(formula._2) ,
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    val state2__ = state__.copy(sf = state__.sf.copy(
      traceAbstraction = formula._1,pureFormula = state__.pureFormula ++ mapToPure(formula._2),
      heapConstraints = Map(StaticPtEdge("foo","bar") -> p1)
    ))
    assert(f.canSubsume(state2__, state2_,spec))
    assert(!f.canSubsume(state2_, state2__,spec))
  }
  test("Subsumption of pure formula in states"){ f =>
    val stateSolver = f.stateSolver

    val loc = AppLoc(fooMethod, SerializedIRLineLoc(1), isPre = false)

    val state = State(
      StateFormula(CallStackFrame(dummyLoc,None,Map(StackVar("x") -> p1))::Nil, Map(),Set(),Map(),
        AbstractTrace( Nil)),0)

    // x->p1 * y->p2 can be subsumed by x->p1
    val state_x_y = state.copy(sf = state.sf.copy(
      callStack = CallStackFrame(dummyLoc,None,Map(
        StackVar("x") -> p1,
        StackVar("y") -> p2
      ))::Nil,
      pureFormula = Set(PureConstraint(p1, NotEquals, p2))
    ))
    assert(f.canSubsume(state,state_x_y,esp))
    assert(!f.canSubsume(state_x_y,state,esp))

  }

  test("Trace contained in abstraction") { f =>
    val stateSolver = f.stateSolver
    implicit val zCTX: Z3SolverCtx = stateSolver.getSolverCtx

    val foo = FwkMethod(Signature("foo", "()"))
    val bar = FwkMethod(Signature("bar", "()"))

    val i_foo_x = AbsMsg(CIEnter, Set(("foo","\\(\\)"),("foo2","\\(\\)")), x::Nil)
    val i_foo_y = AbsMsg(CIEnter, Set(("foo","\\(\\)"),("foo2","\\(\\)")), y::Nil)
    val i_bar_x = AbsMsg(CIEnter, Set(("bar","\\(\\)"),("bar2","\\(\\)")), x::Nil)
    val i_bar_y = AbsMsg(CIEnter, Set(("bar","\\(\\)"),("bar2","\\(\\)")), y::Nil)
    val trace = Trace(List(
      TMessage(CIEnter, foo, ConcreteAddr(1)::Nil),
      TMessage(CIEnter, bar, ConcreteAddr(1)::Nil)
    ))

    val ni_foo_x_bar_x = NS(i_foo_x, i_bar_x)
    val ni_bar_x_foo_x = NS(i_bar_x, i_foo_x)
    val targetFoo_x = AbsMsg(CIExit, Set(("","targetFoo\\(\\)")), x::Nil)
    val targetFoo_y = AbsMsg(CIExit, Set(("","targetFoo\\(\\)")), y::Nil)
    val spec = new SpecSpace(Set(
      LSSpec(x::Nil, Nil, i_foo_x, targetFoo_x)
    ))
    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    // I(x.foo()) models @1.foo();@1.bar()
    val stIFooX = state.copy(
      sf = state.sf.copy(traceAbstraction = AbstractTrace(targetFoo_y :: Nil),
        pureFormula = state.pureFormula ++ mapToPure(Map(y -> pv1))))
    assert(stateSolver.traceInAbstraction(
      stIFooX,spec,
      trace).isDefined)
    //TODO: failing for some reason, possibly due to trace contained negation problem
    //assert(!stateSolver.traceInAbstraction(stIFooX,spec,trace,negate = true, debug = true))

    // I(x.foo()) ! models empty
    assert(stateSolver.traceInAbstraction(
      stIFooX,spec,
      Trace.empty).isEmpty)
    //TODO: negation issue
    //assert(stateSolver.traceInAbstraction(stIFooX,spec,Nil, negate = true))

    val specNotFoo = new SpecSpace(Set(
      LSSpec(x::Nil, Nil, Not(i_foo_x), targetFoo_x)
    ))
    // not I(x.foo()) models empty
    assert(stateSolver.traceInAbstraction(
      state = stIFooX,
      specNotFoo,
      trace = Trace.empty
    ).isDefined)


    // not I(x.foo()) or I(x.bar()) models empty

    val spec_NotFoo_OrBar = new SpecSpace(Set(
      LSSpec(x::Nil, Nil,Or(Not(i_foo_x), i_bar_x), targetFoo_x)
    ))
    assert(stateSolver.traceInAbstraction(
      state = stIFooX,
      spec_NotFoo_OrBar ,
      trace = Trace.empty
    ).isDefined)

    val spec_NiFooBar = new SpecSpace(Set(
      LSSpec(x::Nil, Nil, ni_foo_x_bar_x, targetFoo_x)
    ))
    assert(stateSolver.traceInAbstraction(
      state = stIFooX,
      spec_NiFooBar,
      trace = Trace.empty
    ).isEmpty)


    // NI(x.foo(), x.bar()) ! models @1.foo();@1.bar()
    assert(stateSolver.traceInAbstraction(
      state = stIFooX,
      spec_NiFooBar,
      trace = trace,
      debug=true
    ).isEmpty)

    // empty(trace) models NI(x.foo(),x.bar()) |> x.foo()
    val res = stateSolver.traceInAbstraction(
      st(AbstractTrace(i_foo_y::targetFoo_y::Nil), Map(y->pv1)),
      spec_NiFooBar,
      Trace.empty
    )
    assert(res.isDefined)

    //@1.bar() models NI(x.foo(),x.bar()) |> x.foo()
    assert(
      stateSolver.traceInAbstraction(
        st(AbstractTrace(i_foo_y::targetFoo_y::Nil),Map(y->pv1)),
        spec_NiFooBar,
        Trace(TMessage(CIEnter, bar, ConcreteAddr(1)::Nil)::Nil)
      ).isDefined)

    // NI(x.foo(),x.bar()) |> x.foo() models @1.foo();@1.bar()
    assert(
      stateSolver.traceInAbstraction(
        st(AbstractTrace(i_foo_y::targetFoo_y::Nil),Map(y->pv1)),
        spec_NiFooBar,
        trace
      ).isDefined)

    // NI(x.foo(),x.bar()) |> x.bar() ! models empty
    assert(
      stateSolver.traceInAbstraction(
        st(AbstractTrace(i_bar_y::targetFoo_y::Nil),Map(y->pv1)),
        spec_NiFooBar,
        trace
      ).isEmpty)

    // Not NI(x.foo(), x.bar())  models @1.foo();@1.bar()
    val spec_not_NiFooBar = new SpecSpace(Set(
      LSSpec(x::Nil, Nil, Or(ni_bar_x_foo_x, Not(i_bar_x)), targetFoo_x)
    ))
    assert(
      stateSolver.traceInAbstraction(
        st(AbstractTrace(targetFoo_y::Nil),Map(y->pv1)),
        spec_not_NiFooBar,
        trace
      ).isDefined)
//    assert(
//      stateSolver.traceInAbstraction(
//        state.copy(sf = state.sf.copy(traceAbstraction = Set(AbstractTrace(Not(ni_foo_x_bar_x), Nil,Map())))),esp,
//        trace
//      ))

    // I(foo(x,y)) models foo(@1,@2)
    val i_foo_x_y = AbsMsg(CIEnter, Set(("foo","\\(\\)"),("foo2","\\(\\)")), x::y::Nil)
    val targetFoo_x_y = AbsMsg(CIExit, Set(("","targetFoo\\(\\)")), x::y::Nil)
    val targetFoo_a_b = AbsMsg(CIExit, Set(("","targetFoo\\(\\)")), a::b::Nil)
    val spec_Foo_x_y = new SpecSpace(Set(
      LSSpec(x::y::Nil, Nil, i_foo_x_y, targetFoo_x_y)
    ))
    assert(
      stateSolver.traceInAbstraction(
        st(AbstractTrace(targetFoo_a_b::Nil),Map(a->pv1,b->pv2)),
        spec_Foo_x_y,
        trace = Trace(TMessage(CIEnter, foo, ConcreteAddr(1)::ConcreteAddr(2)::Nil)::Nil)
      ).isDefined
    )

    // foo(@1,@2);bar(@1,@2) !models [¬I(foo(x,y))] /\ I(bar(x,y))
    val i_bar_x_y = AbsMsg(CIEnter, Set(("bar",""),("bar2","")), x::y::Nil)
    val spec_NotFoo_Bar_x_y = new SpecSpace(Set(
      LSSpec(x::y::Nil, Nil,And(Not(i_foo_x_y), i_bar_x_y), targetFoo_x_y)
    ))
    assert(
      stateSolver.traceInAbstraction(
        st(AbstractTrace(targetFoo_a_b::Nil),Map(a->pv1,b->pv2)),
        spec_NotFoo_Bar_x_y,
        Trace(List(
          TMessage(CIEnter, foo, ConcreteAddr(1)::ConcreteAddr(2)::Nil),
          TMessage(CIEnter, bar, ConcreteAddr(1)::ConcreteAddr(2)::Nil)
        ))
      ).isEmpty
    )

    // foo(@1,@2);bar(@1,@1) models [¬I(foo(x,y))] /\ I(bar(x,y))
    assert(
      stateSolver.traceInAbstraction(
        st(AbstractTrace(targetFoo_a_b::Nil),Map(a->pv1,b->pv2)),
        spec_NotFoo_Bar_x_y,
        Trace(List(
          TMessage(CIEnter, foo, ConcreteAddr(1)::ConcreteAddr(2)::Nil),
          TMessage(CIEnter, bar, ConcreteAddr(1)::ConcreteAddr(1)::Nil)
        ))
      ).isDefined
    )

    // I(foo(y,y) !models foo(@1,@2)
    val i_foo_y_y = AbsMsg(CIEnter, Set(("foo","\\(\\)"),("foo2","\\(\\)")), y::y::Nil)
    val targetFoo_y_y = AbsMsg(CIExit, Set(("","targetFoo\\(\\)")), y::y::Nil)
    val targetFoo_a_a = AbsMsg(CIExit, Set(("","targetFoo\\(\\)")), a::a::Nil)
    val spec_Foo_y_y = new SpecSpace(Set(
      LSSpec(x::y::Nil, Nil, i_foo_y_y, targetFoo_x_y)
    ))
    assert(
      stateSolver.traceInAbstraction(
        st(AbstractTrace(targetFoo_a_a::Nil),Map(a -> PureVar(1))),
        spec_Foo_y_y,
        trace = Trace(TMessage(CIEnter, foo, ConcreteAddr(1)::ConcreteAddr(2)::Nil)::Nil),
        debug = true
      ).isEmpty
    )

    // I(foo(y,y) models foo(@2,@2)
    assert(
      stateSolver.traceInAbstraction(
        st(AbstractTrace(targetFoo_a_b::Nil),Map(a->pv1, b->pv2)),
        spec_Foo_y_y,
        trace = Trace(TMessage(CIEnter, foo, ConcreteAddr(2)::ConcreteAddr(2)::Nil)::Nil)
      ).isDefined
    )
  }
  test("app mem restricted trace contained"){f =>
    val stateSolver = f.stateSolver
    implicit val zCTX: Z3SolverCtx = stateSolver.getSolverCtx

    val pv1 = PureVar(1)
    val pv2 = PureVar(2)
    val foo = FwkMethod(Signature("foo", "()"))
    val bar = FwkMethod(Signature("bar", "()"))

    val i_foo_x = AbsMsg(CIEnter, Set(("foo","\\(\\)"),("foo2","\\(\\)")), x::Nil)
    val i_bar_x = AbsMsg(CIEnter, Set(("bar","\\(\\)"),("bar2","\\(\\)")), x::Nil)
    val targetFoo_x_y = AbsMsg(CIExit, Set(("","targetFoo\\(\\)")), x::y::Nil)
    val targetFoo_a_b = AbsMsg(CIExit, Set(("","targetFoo\\(\\)")), a::b::Nil)
    val trace = Trace(List(
      TMessage(CIEnter, foo, ConcreteAddr(1)::Nil),
      TMessage(CIEnter, bar, ConcreteAddr(1)::Nil)
    ))
    val spec = new SpecSpace(Set(
      LSSpec(x::y::Nil, Nil, NS(i_foo_x, i_bar_x), targetFoo_x_y,
        Set(LSConstraint(x, Equals, NullVal))),
      LSSpec(x::y::Nil, Nil, LSTrue, targetFoo_x_y, Set(LSConstraint(x, NotEquals, NullVal)))
    ))
    val stateNull = st(AbstractTrace(targetFoo_a_b::Nil), Map(a->pv1, b->pv2))
      .addPureConstraint(PureConstraint(pv1, Equals, NullVal))

    val simplStateNull = stateSolver.simplify(stateNull,spec)
    println(simplStateNull)
    val resIsNull = stateSolver.traceInAbstraction(
      stateNull,
      spec,
      trace
    )
    assert(
      resIsNull.isEmpty
    )
    val resNonNull = stateSolver.traceInAbstraction(
      stateNull.copy(sf = stateNull.sf.copy(pureFormula = Set(PureConstraint(pv1, NotEquals, NullVal)))),
      spec,
      trace
    )
    assert(resNonNull.isDefined)
  }



  test("Empty trace should not be contained in incomplete abstract trace") { f =>
    val stateSolver = f.stateSolver

    val iFoo_a = AbsMsg(CBEnter, Set(("", "foo")), a :: Nil)
    val iFoo_b = AbsMsg(CBEnter, Set(("", "foo")), b :: Nil)
    val iBar_a = AbsMsg(CBEnter, Set(("", "bar")), a::Nil)
    val spec = new SpecSpace(Set(LSSpec(a::Nil, Nil, iBar_a,iFoo_a,Set())),Set())
//    def s(at:AbstractTrace):State = {
//      val ts = State.topState
//      ts.copy(sf = ts.sf.copy(traceAbstraction = at))
//    }
    val pv = PureVar(1)
    val at = (AbstractTrace( iFoo_b::Nil), Map(b -> pv))

    val res = stateSolver.witnessed(st(at),spec)
    assert(res.isEmpty)
  }
  ignore("Empty trace should not be contained in incomplete abstract trace with conditional spec") { fTest =>
    //TODO: Why is this test ignored???====
    //TODO: |>
    val stateSolver:Z3StateSolver = fTest.stateSolver

    val f = NamedPureVar("f")

    val iFoo_ac = AbsMsg(CBEnter, Set(("", "foo")), c::a :: Nil)
    val iFoo_null_c =  AbsMsg(CBEnter, Set(("", "foo")), NullVal::a :: Nil)
    val iFoo_bd = AbsMsg(CBEnter, Set(("", "foo")), d::b :: Nil)
    val iBar_a = AbsMsg(CBEnter, Set(("", "bar")), a::Nil)
    val s1 = LSSpec(a::c::Nil, Nil, iBar_a,iFoo_ac,Set(LSConstraint(c, Equals, NullVal)))
    val s2 = LSSpec(a::c::Nil, Nil, LSTrue, iFoo_ac,Set(LSConstraint(c, NotEquals, NullVal)))
    val spec = new SpecSpace(Set(s1,s2))

    val pv = PureVar(1)
    val pv2 = PureVar(2)
    val at = (AbstractTrace( iFoo_bd::Nil), Map(d -> pv, b -> pv2))

    val res = stateSolver.witnessed(st(at).addPureConstraint(PureConstraint(pv, Equals, NullVal)),spec)
    assert(res.isEmpty)
    val res2 = stateSolver.witnessed(st(at).addPureConstraint(PureConstraint(pv, NotEquals, NullVal)),spec)
    assert(res2.isDefined)

    val s3 = LSSpec(c::Nil, a::Nil, iBar_a, iFoo_null_c, Set())
    val spec2 = new SpecSpace(Set(s2,s3))
    val res3 = stateSolver.witnessed(st(at).addPureConstraint(PureConstraint(pv, Equals, NullVal)), spec2)
    assert(res3.isEmpty)

    val pv3 = PureVar(3)
    val iBaz_e = AbsMsg(CBEnter, Set(("", "baz")), e::Nil)
    val iBaz_f = AbsMsg(CBEnter, Set(("", "baz")), f::Nil)

    val s4 = LSSpec(e::Nil, Nil, LSTrue,iBaz_e, Set())
//    val spec4 = new SpecSpace(Set(s2,s3,s4))
    val spec4 = new SpecSpace(Set(s3,s4))
    val at4 = (AbstractTrace( iBaz_f::iFoo_bd::Nil), Map(f -> pv3, d -> pv, b -> pv2))

    val res4 = stateSolver.witnessed(st(at4).addPureConstraint(PureConstraint(pv, Equals, NullVal)),spec4,debug = true)
    assert(res4.isEmpty)
  }
  test("Prepending required enable message to trace should prevent subsumption") { fTest =>
    val stateSolver = fTest.stateSolver

    val g = NamedPureVar("g")
    val f = NamedPureVar("f")
    val iFoo_ac = AbsMsg(CBEnter, Set(("", "foo")), c::a :: Nil)
    val iFoo_null_c =  AbsMsg(CBEnter, Set(("", "foo")), NullVal::a :: Nil)
    val iFoo_bd = AbsMsg(CBEnter, Set(("", "foo")), d::b :: Nil)
    val iBar_a = AbsMsg(CBEnter, Set(("", "bar")), a::Nil)
    val iBar_e = AbsMsg(CBEnter, Set(("", "bar")), e::Nil)
    val iBaz_f = AbsMsg(CBEnter, Set(("", "baz")), f::Nil)
    val iBaz_g = AbsMsg(CBEnter, Set(("", "baz")), g::Nil)
    val iWap_g = AbsMsg(CBEnter, Set(("", "wap")), g::Nil)
    val s1 = LSSpec(a::c::Nil, Nil, iBar_a,iFoo_ac,Set(LSConstraint(c, Equals, NullVal)))
    val s2 = LSSpec(a::c::Nil, Nil, iBar_a, iFoo_ac,Set(LSConstraint(c, NotEquals, NullVal))) //TODO: does LSTrue cause issues?
    val s3 = LSSpec(g::Nil, Nil, iWap_g, iBaz_g, Set())
    val spec = new SpecSpace(Set(s1,s2, s3))
//    def s(at:AbstractTrace, pc:Set[PureConstraint]):State = {
//      val ts = State.topState
//      ts.copy(sf = ts.sf.copy(traceAbstraction = at, pureFormula = pc))
//    }
    val pv = PureVar(1)
    val pv2 = PureVar(2)
    val pv3 = PureVar(3)
    val pv4 = PureVar(4)
    val at1 = (AbstractTrace( iBaz_f::iFoo_bd::Nil), Map(d -> pv, b -> pv2, f ->pv4))
    val at2 = (AbstractTrace( iBar_e::iBaz_f::iFoo_bd::Nil), Map(d -> pv, b -> pv2, e -> pv3, f -> pv4))
    val pc = PureConstraint(pv, Equals, NullVal)

    val s_1 = st(at1).addPureConstraint(pc)
    val isFeasible1 = stateSolver.simplify(s_1,spec)
    assert(isFeasible1.isDefined)
    val s_2 = st(at2).addPureConstraint(pc)
    val isFeasible2 = stateSolver.simplify(s_2, spec)
    assert(isFeasible2.isDefined)


    val res = fTest.canSubsume(s_1, s_2, spec)
    assert(!res)
  }

  test("|>x.onDestroy() should subsume |>x.onDestroy()|>y.onDestroy()"){f =>
    val stateSolver = f.stateSolver
    val w = NamedPureVar("w")
    val p = NamedPureVar("p")
    val specs = new SpecSpace(Set(FragmentGetActivityNullSpec.getActivityNull,
      FragmentGetActivityNullSpec.getActivityNonNull,
    ) ++ LifecycleSpec.spec ++ RxJavaSpec.spec)
    val destTgtX = AbsMsg(CBExit, SpecSignatures.Activity_onDestroy, TopVal::x::Nil)
    val createTgtX = AbsMsg(CBEnter, SpecSignatures.Activity_onCreate, TopVal::x::Nil)
    val destTgtY = AbsMsg(CBExit, SpecSignatures.Activity_onDestroy, TopVal::y::Nil)
    val callTgtZ = AbsMsg(CBEnter, SpecSignatures.RxJava_call, TopVal::z::Nil)
    val unsubTgtW = AbsMsg(CIExit, SpecSignatures.RxJava_unsubscribe, TopVal::w::Nil)
    val subTgtWP = AbsMsg(CIExit, SpecSignatures.RxJava_subscribe, w::TopVal::p::Nil)
    val s1 = st(AbstractTrace(FreshRef(z)::destTgtX::callTgtZ::Nil), Map(x->p1, z->p3, w->p4))
    val s2 = st(AbstractTrace(FreshRef(z)::destTgtY::destTgtX::callTgtZ::Nil), Map(x->p1, y->p2, z->p3, w->p4))
      .addPureConstraint(PureConstraint(p1,NotEquals,p2))
    assert(f.canSubsume(s1,s2, specs))

    val specs2 = new SpecSpace(
      Set(FragmentGetActivityNullSpec.getActivityNull, FragmentGetActivityNullSpec.getActivityNonNull) ++
        RxJavaSpec.spec ++
        LifecycleSpec.spec)
    val s_1 = st(AbstractTrace(
      createTgtX::subTgtWP::unsubTgtW::destTgtX::callTgtZ::Nil),
      Map(x->p1,z->p2,w->p4,p->p5))
    val s_2 = st(AbstractTrace(
      destTgtY::createTgtX::subTgtWP::unsubTgtW::destTgtX::callTgtZ::Nil),
      Map(x->p1,z->p2,w->p4,p->p5, y->p6))

    //    //TODO: remove dbg code
//    val s_1_pre = EncodingTools.rhsToPred(s_1.traceAbstraction.rightOfArrow, specs2).map(EncodingTools.simplifyPred)
//    val s_2_pre = EncodingTools.rhsToPred(s_2.traceAbstraction.rightOfArrow, specs2).map(EncodingTools.simplifyPred)
//    println("test test test")
//
//    s_1.setSimplified()
//    assert(stateSolver.canSubsume(s_1, s_2, specs2))
//    assert(stateSolver.canSubsumeSet(Set(s_1), s_2_simp, specs2))
    //TODO: dbg code
    //TODO: is it a problem that this times out without simp?
    val s_2_simp = stateSolver.simplify(s_2, specs2)

    assert(f.canSubsume(s_1,s_2_simp.get,specs2))

    val s_1_ = st(AbstractTrace(
      createTgtX::Nil),
      Map(x->p1))
    val s_2_ = st(AbstractTrace(
      destTgtY::createTgtX::Nil),
      Map(x->p1, y->p6))
    assert(stateSolver.simplify(s_1_,specs2).isDefined)
    assert(stateSolver.simplify(s_2_,specs2).isDefined)
    assert(f.canSubsume(s_1_,s_1_,specs2))
    assert(f.canSubsume(s_2_,s_2_,specs2))
    assert(f.canSubsume(s_1_,s_2_,specs2))
  }

  test("Can subsume disjuncted has not temporal formula 1"){ f =>
    val pa2 = NamedPureVar("p-a2")
    val p8 = NPureVar(8)
    val oFindView = AbsMsg(CIExit, SpecSignatures.Activity_findView, p6::pa2::Nil)

    val p = Forall(pa2::Nil, Or(Not(oFindView), LSConstraint(p8,Equals,pa2)))
    assert(f.canSubsumePred(p,p))

  }

  ignore("test enc of ns negation"){f =>
    //TODO:  possible way of negating?
    val w = NamedPureVar("w")
    val p = NamedPureVar("p")
    val unsubTgtW = AbsMsg(CIExit, SpecSignatures.RxJava_unsubscribe, TopVal :: w :: Nil)
    val subTgtWP = AbsMsg(CIExit, SpecSignatures.RxJava_subscribe, w :: TopVal :: p :: Nil)
    val p1 = Not(NS(subTgtWP,unsubTgtW))
    val p2 = Or(Not(subTgtWP), NS(unsubTgtW,subTgtWP))
    assert(f.canSubsumePred(p1,p2))
    assert(f.canSubsumePred(p2,p1))

  }

  ignore("z3 to smtlib conversions test and extraneous quantifier removal"){ f=>
    // Test the conversions between smtlib and z3
    val stateSolver = f.stateSolver
    val busted =
      """|
         |(let ((a!1 (exists ((npv-s!10 Addr))
         |               (let ((a!1 (exists ((msg_j!11 Msg))
         |                            (and (traceFn msg_j!11)
         |                                 (= (namefn_ msg_j!11) I_CIExit_RxJavasubscribe)
         |                                 (= (argfun_0 msg_j!11) npv-s!10)
         |                                 (= (argfun_2 msg_j!11) npv-z!1)
         |                                 (forall ((msg_j!12 Msg))
         |                                   (let ((a!1 (not (and (= (namefn_ msg_j!12)
         |                                                           I_CIExit_rxJavaunsubscribe)
         |                                                        (= (argfun_1 msg_j!12)
         |                                                           npv-s!10)))))
         |                                   (let ((a!2 (=> (and (msgLTE msg_j!11
         |                                                               msg_j!12)
         |                                                       (not (= msg_j!11
         |                                                               msg_j!12)))
         |                                                  a!1)))
         |                                     (=> (traceFn msg_j!12) a!2))))))))
         |               (let ((a!2 (and a!1
         |                               (or (not (= npv-s!10 npv-w!9))
         |                                   (not (= npv-z!1 npv-p!4))))))
         |                 (and (or (and (= npv-s!10 npv-w!9) (= npv-z!1 npv-p!4)) a!2)
         |                      (not (= npv-w!9 npv-s!10)))))))
         |        (a!2 (exists ((msg_j!13 Msg))
         |               (and (traceFn msg_j!13)
         |                    (= (namefn_ msg_j!13) I_CIExit_RxJavasubscribe)
         |                    (= (argfun_0 msg_j!13) npv-w!9))))
         |        (a!3 (exists ((msg_j!14 Msg))
         |               (and (traceFn msg_j!14)
         |                    (= (namefn_ msg_j!14) I_CBEnter_ActivityonCreate)
         |                    (= (argfun_1 msg_j!14) npv-x!8)))))
         |    (and (= npv-z!1 pv-2!3)
         |         (= npv-w!9 pv-4!2)
         |         (= npv-p!4 pv-5!7)
         |         (= npv-x!8 pv-1!0)
         |         (= npv-y!6 pv-6!5)
         |         a!1
         |         (not a!2)
         |         (not a!3)))
        |         """.stripMargin
      implicit val zCtx = stateSolver.getSolverCtx
      try {
        zCtx.acquire()
        val expr = stateSolver.stringExprToSmtLib(busted)
        val parsedBusted = stateSolver.smtToZ3(expr)
        val pruned = stateSolver.pruneUnusedQuant(parsedBusted)
        assert(
          parsedBusted.toString.replace("\n","") ==
            pruned.toString.replace("\n",""))

        val expr2 = stateSolver.stringExprToSmtLib(s"(exists ((stupidAst Addr)) ${busted})")
        val parsed2 = stateSolver.smtToZ3(expr2)
        val pruned2 = stateSolver.pruneUnusedQuant(parsed2)
        assert(!pruned2.toString.contains("stupidAst"))
      }finally{
        zCtx.release()
      }

  }
  //TODO: test subsumption of specifications
//  test("Subsumption of specifications") { f =>
//    val stateSolver = f.stateSolver
//    val iFoo_ac = AbsMsg(CBEnter, Set(("", "foo")), c::a :: Nil)
//    val iBar_a = AbsMsg(CBEnter, Set(("", "bar")), a::Nil)
//    ???
//  }
  test("z3 scratch"){f=>
    val timeout = File(getClass.getResource("/timeout.smt").getPath).contentAsString
    val solver = f.stateSolver
    val lexer = new Lexer(new StringReader(timeout))
    val parser = new Parser(lexer)
    val script: List[Command] = {
      val cmds = new ListBuffer[Command]
      try {
        var cmd:Command = null
        while({cmd = parser.parseCommand; cmd != null})
          cmds.append(cmd)
      }catch{
        case e:UnknownCommandException =>
          ???
      }
      cmds.toList
    }
  }



}
