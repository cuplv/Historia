package edu.colorado.plv.bounder.solver

import edu.colorado.plv.bounder.symbolicexecutor.state.{Equals, NullVal, PureAtomicConstraint, PureVar}

class Z3SolverTest extends org.scalatest.FunSuite {
  test("solve a simple ast") {
    val solver = new Z3Solver()
    val x = PureVar()
    solver.toAST(PureAtomicConstraint(x, Equals, NullVal))
  }

}
