package edu.colorado.plv.bounder.solver

import com.microsoft.z3.{Context, Solver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{Equals, NullVal, PureConstraint, PureVar, State}

class Z3StateSolverTest extends org.scalatest.FunSuite {
  test("solve a simple ast") {
    val ctx = new Context
    val solver: Solver = ctx.mkSolver()
    val hierarchy : Map[String, Set[String]] =
      Map("Object" -> Set("String", "Foo", "Bar", "Object"),
        "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"))
    val pc = new PersistantConstraints(ctx, solver, hierarchy)
    val statesolver = new Z3StateSolver(pc)
//    val refutableState = State(List(), )
  }

}
