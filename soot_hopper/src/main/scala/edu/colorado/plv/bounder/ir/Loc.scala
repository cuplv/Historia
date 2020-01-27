package edu.colorado.plv.bounder.ir

/**
 * A source code location
 * TODO: find a way to make the type system enforce locations are not used cross wrapper implementations
 */
trait MethodLoc
trait LineLoc
case class Loc(method: MethodLoc, line: LineLoc)
