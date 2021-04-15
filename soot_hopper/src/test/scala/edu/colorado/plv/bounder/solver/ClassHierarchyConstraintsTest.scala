package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{Context, Status}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BoundedTypeSet, ClassType, DisjunctTypeSet, SubclassOf, SuperclassOf}
import org.scalatest.funsuite.AnyFunSuite

class ClassHierarchyConstraintsTest extends AnyFunSuite {
  //TODO: test hierarchy constraints for TypeSet
  val hierarchy : Map[String, Set[String]] =
    Map("java.lang.Object" -> Set("String", "Foo", "Bar", "java.lang.Object"),
      "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"), "Runnable" -> Set("Foo","Bar"))
  implicit val ch = new ClassHierarchyConstraints(hierarchy,Set("Runnable"), SolverTypeSolving)


  test("contains"){
    //TODO: contains method of DisjunctTypeSet is clearly not working:
    // p-2:<:com.example.createdestroy.MyActivity$1<: I( com.example.createdestroy.MyActivity$SomethingAble) disj,
    // p-2:<:com.example.createdestroy.MyActivity$1 >:com.example.createdestroy.MyActivity$1<: I( com.example.createdestroy.MyActivity$SomethingAble) disj)
    val bts = BoundedTypeSet(Some("Foo"), None, Set())
    val isTs = BoundedTypeSet(Some("Foo"), Some("Foo"),Set())
    assert(bts.contains(isTs))

    val isTsIface = BoundedTypeSet(Some("Foo"), Some("Foo"), Set("Runnable"))
    assert(bts.contains(isTsIface))
    assert(isTs.contains(isTsIface))

    val dBts = DisjunctTypeSet(Set(bts))
    val dIsTs = DisjunctTypeSet(Set(isTs))
    assert(dBts.contains(dIsTs))
    assert(bts.contains(dIsTs))
    assert(dBts.contains(isTs))
    //=========

  }
  test("Subtype"){


    val stateSolver:StateSolver[com.microsoft.z3.AST, Z3SolverCtx] = new Z3StateSolver(ch)
    implicit val zctx = stateSolver.getSolverCtx

    //TODO: test type function etc
//    val tc1 = stateSolver.addTypeConstraint("a", ch("Bar"))
//    solver.add(tc1)
//    val tc2 = ch.addTypeConstraint("a", SubclassOf("Foo"))
//    solver.add(tc2)
//    assert(solver.check() == Status.SATISFIABLE)

//    val tc3 = ch.addTypeConstraint("b", SuperclassOf("String"))
//    solver.add(tc3)
//    val tc4 = ch.addTypeConstraint("b", SubclassOf("String"))
//    solver.add(tc4)

//    val tc6 = ch.addTypeConstraint("b", SuperclassOf("String"))
//    solver.add(tc6)
//    val tc7 = ch.addTypeConstraint("b", SubclassOf("Foo"))
//    solver.add(tc7)
//    assert(solver.check() == Status.UNSATISFIABLE)

  }


}
