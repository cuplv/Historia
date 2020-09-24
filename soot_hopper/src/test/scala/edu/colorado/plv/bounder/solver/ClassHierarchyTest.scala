package edu.colorado.plv.bounder.solver

import com.microsoft.z3.Context

class ClassHierarchyTest extends org.scalatest.FunSuite {
  test("Subtype"){
    val ctx = new Context
    val hierarchy = List(("Object", "String"), ("Object" , "Foo"), ("Foo", "Bar"))
    val solver = ctx.mkSolver()
    val ch = new ClassHierarchy(ctx, solver, hierarchy)
    println(s"check ${solver.check()}")
    println("model")
    println(solver.getModel())
    println(s"assertions : ${solver.getAssertions().mkString(",")}")
    ctx.close()
  }

}
