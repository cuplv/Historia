package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{Context, Status}
import edu.colorado.plv.bounder.symbolicexecutor.state.{SubclassOf, SuperclassOf}

class PersistantConstraintsTest extends org.scalatest.FunSuite {
  test("Subtype"){
    val ctx = new Context
//    val hierarchy = List(("Object", "String"), ("Object" , "Foo"), ("Foo", "Bar"))
    val hierarchy : Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val solver = ctx.mkSolver()
    val ch = new PersistantConstraints(ctx, solver, hierarchy)
    assert(solver.check() == Status.SATISFIABLE)
    val tc1 = ch.addTypeConstraint("a", SuperclassOf("Bar"))
    solver.add(tc1)
    val tc2 = ch.addTypeConstraint("a", SubclassOf("Foo"))
    solver.add(tc2)
//    println(solver.getAssertions.mkString("\n"))
    assert(solver.check() == Status.SATISFIABLE)

//    println(ch.typeToInt)
    val tc3 = ch.addTypeConstraint("b", SuperclassOf("String"))
    solver.add(tc3)
    val tc4 = ch.addTypeConstraint("b", SubclassOf("String"))
    solver.add(tc4)

    assert(solver.check() == Status.SATISFIABLE)
//    println(solver.getModel())

    val tc6 = ch.addTypeConstraint("b", SuperclassOf("String"))
    solver.add(tc6)
    val tc7 = ch.addTypeConstraint("b", SubclassOf("Foo"))
    solver.add(tc7)
    assert(solver.check() == Status.UNSATISFIABLE)
    ctx.close()
  }

}
