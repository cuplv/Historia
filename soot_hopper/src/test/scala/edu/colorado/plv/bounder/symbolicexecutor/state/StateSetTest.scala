package edu.colorado.plv.bounder.symbolicexecutor.state

import com.microsoft.z3.Context
import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodReturn, LocalWrapper, TestIRLineLoc, TestIRMethodLoc}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, SolverTypeSolving, Z3StateSolver}
import org.scalatest.funsuite.AnyFunSuite

class StateSetTest extends AnyFunSuite {
  val ctx = new Context
  val hierarchy : Map[String, Set[String]] =
    Map("java.lang.Object" -> Set("String", "Foo", "Bar", "java.lang.Object"),
      "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
  val solver = ctx.mkSolver()

  val ch = new ClassHierarchyConstraints(hierarchy,Set("Runnable"), SolverTypeSolving)
  val stateSolver = new Z3StateSolver(ch)

  private val fooMethod = TestIRMethodLoc("","foo", List(Some(LocalWrapper("@this","Object"))))
  private val lineLoc = TestIRLineLoc(-1)
  private val dummyLoc = CallbackMethodReturn(fmwClazz = "",
    fmwName="void foo()", fooMethod, None)
  test("Add state"){
    //TODO: state set is work in progress and not used yet
    def pn(state:State):IPathNode = {
      MemoryPathNode(SomeQry(state,AppLoc(fooMethod,lineLoc, false)),Nil,None,5,0)
    }
    val set = StateSet.init
    val pv0 = PureVar(0)
    val pv1 = PureVar(1)
    val locals1 = Map(StackVar("foo")->pv0)
    val s1 = State.topState.copy(
      callStack = CallStackFrame(dummyLoc,None,locals1)::Nil,
      typeConstraints = Map(
        pv0-> BoundedTypeSet(Some("Foo"),None,Set()),
        pv1-> BoundedTypeSet(Some("String"),None,Set())
      ),
      heapConstraints = Map(FieldPtEdge(pv0,"f")->pv1),
      nextAddr = 3
    )

    val set1 = StateSet.add(pn(s1), set)

    val subsumee1 = s1.swapPvUnique(pv0, pv1)
    val subsState = StateSet.findSubsuming(pn(subsumee1), set1,
    (s1,s2) => stateSolver.canSubsumeSlow(s1,s2))
    assert(subsState.isDefined)
    assert(subsState.get == pn(s1))
  }

}
