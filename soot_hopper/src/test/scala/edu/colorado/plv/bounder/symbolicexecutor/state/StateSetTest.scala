package edu.colorado.plv.bounder.symbolicexecutor.state

import com.microsoft.z3.Context
import edu.colorado.plv.bounder.ir.{AppLoc, BitTypeSet, CallbackMethodReturn, LocalWrapper, TestIRLineLoc, TestIRMethodLoc, TypeSet}
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, SolverTypeSolving, Z3StateSolver}
import org.scalatest.funsuite.AnyFunSuite

import scala.collection.BitSet

class StateSetTest extends AnyFunSuite {
  val ctx = new Context
  val hierarchy : Map[String, Set[String]] =
    Map("java.lang.Object" -> Set("String", "Foo", "Bar", "java.lang.Object"),
      "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
  val solver = ctx.mkSolver()

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

  val ch = new ClassHierarchyConstraints(hierarchy,Set("Runnable"),intToClass)
  val stateSolver = new Z3StateSolver(ch)

  private val fooMethod = TestIRMethodLoc("","foo", List(Some(LocalWrapper("@this","Object"))))
  private val barMethod = TestIRMethodLoc("","bar", List(Some(LocalWrapper("@this","Object"))))
  private val lineLoc = TestIRLineLoc(-1)
  private val dummyLoc1 = CallbackMethodReturn(tgtClazz = "", fmwName="void foo()", fooMethod, None)
  private val dummyLoc2 = CallbackMethodReturn(tgtClazz = "", fmwName="void bar()", barMethod, None)
  val pv0 = PureVar(0)
  val pv1 = PureVar(1)
  val locals1 = Map(StackVar("foo")->pv0)
  def pn(state:State):IPathNode = {
    MemoryPathNode(Qry(state,AppLoc(fooMethod,lineLoc, false), Live),Nil,Set.empty,5,0)
  }
  val emptySet = StateSet.emptyStateSet

  test("Add state"){
    val s1 = State.topState.copy(sf = State.topState.sf.copy(
      callStack = CallStackFrame(dummyLoc1,None,locals1)::Nil,
      typeConstraints = Map(
        pv0-> BoundedTypeSet(Some("Foo"),None,Set()),
        pv1-> BoundedTypeSet(Some("String"),None,Set())
      ),
      heapConstraints = Map(FieldPtEdge(pv0,"f")->pv1)),
      nextAddr = 3
    )

    val set1 = StateSet.add(pn(s1), emptySet)

    val subsumee1 = s1.swapPvUnique(pv0, pv1)
    val posSubsState = StateSet.getPossibleSubsuming(pn(subsumee1), set1)
//    (s1,s2) => stateSolver.canSubsumeSlow(s1,s2))
    val subsState = posSubsState.find(other =>
      stateSolver.canSubsume(subsumee1, other.qry.state,new SpecSpace(Set())))
    assert(subsState.isDefined)
    assert(subsState.get == pn(s1))
  }

  test("Filter out states with mismatched stacks"){
    val s1 = State.topState.copy(sf = State.topState.sf.copy(callStack = CallStackFrame(dummyLoc1, None,locals1)::Nil))
    val s2 = State.topState.copy(sf = State.topState.sf.copy(callStack = CallStackFrame(dummyLoc2, None,locals1)::Nil))
    val set1 = StateSet.add(pn(s1), emptySet)
    assert(StateSet.getPossibleSubsuming(pn(s2), set1).isEmpty)
  }

  test("Don't filter out states with substring stacks"){
    val s1 = State.topState.copy(sf = State.topState.sf.copy(callStack = CallStackFrame(dummyLoc1, None,locals1)::Nil))
    val s2 = State.topState.copy(sf = State.topState.sf.copy(
      callStack = CallStackFrame(dummyLoc1, None,locals1)::CallStackFrame(dummyLoc2, None,locals1)::Nil))
    val set1 = StateSet.add(pn(s1), emptySet)
    assert(StateSet.getPossibleSubsuming(pn(s2), set1).nonEmpty)
  }

  test("Filter subsumed by should test subsumption of states that may be subsumed"){
    //TODO: implement this method and call from symbolic executor
    val s1 = State.topState.copy(sf = State.topState.sf.copy(callStack = CallStackFrame(dummyLoc1, None,locals1)::Nil))
    val s2 = State.topState.copy(sf = State.topState.sf.copy(callStack = CallStackFrame(dummyLoc2, None,locals1)::Nil))
    val s3 = State.topState.copy(sf = State.topState.sf.copy(
      callStack = CallStackFrame(dummyLoc1, None,locals1)::CallStackFrame(dummyLoc2, None,locals1)::Nil))

    val twoState = StateSet.add(pn(s3),StateSet.add(pn(s2),emptySet))
    val resSet = StateSet.filterSubsumedBy(pn(s1),twoState, (_,_)=>true)
    assert(resSet.allStates.contains(pn(s2)))
    assert(!resSet.allStates.contains(pn(s3)))
  }

  test("Filter subsumed based on heap edges"){
    val s1 = State.topState.copy(sf = State.topState.sf.copy(heapConstraints = Map(FieldPtEdge(pv0,"foo") -> pv1)))
    val s2 = State.topState.copy(sf = State.topState.sf.copy(
      heapConstraints = Map(FieldPtEdge(pv0,"foo") -> pv1, FieldPtEdge(pv0,"bar") -> pv1)))
    val s1set = StateSet.add(pn(s1),emptySet)
    assert(StateSet.getPossibleSubsuming(pn(s2), s1set).nonEmpty)
  }

}
