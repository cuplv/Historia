package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{Context, Status}

class ClassHierarchyTest extends org.scalatest.FunSuite {
  test("Subtype"){
    val ctx = new Context
//    val hierarchy = List(("Object", "String"), ("Object" , "Foo"), ("Foo", "Bar"))
    val hierarchy : Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val solver = ctx.mkSolver()
    val ch = new ClassHierarchy(ctx, solver, hierarchy)
    assert(solver.check() == Status.SATISFIABLE)
    ch.addTypeConstraint("a", SuperclassOf("Bar"))
    ch.addTypeConstraint("a", SubclassOf("Foo"))
//    println(solver.getAssertions.mkString("\n"))
    assert(solver.check() == Status.SATISFIABLE)

//    println(ch.typeToInt)
    ch.addTypeConstraint("b", SuperclassOf("String"))
    ch.addTypeConstraint("b", SubclassOf("String"))

    assert(solver.check() == Status.SATISFIABLE)
//    println(solver.getModel())

    ch.addTypeConstraint("b", SuperclassOf("String"))
    ch.addTypeConstraint("b", SubclassOf("Foo"))
    assert(solver.check() == Status.UNSATISFIABLE)
    ctx.close()
  }

}
