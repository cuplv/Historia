package edu.colorado.plv.bounder.state

import edu.colorado.plv.bounder.ir.{Loc, MethodLoc}

//case class CallStack(frames: List[CallStackFrame])

case class CallStackFrame(methodLoc : Loc,
                          retLoc: Option[Loc],
                          locals: Map[StackVar, Val]){
  override def toString:String = {
    "[" + methodLoc.toString + " locals: " + locals.map(k => k._1.toString + ":" + k._2.toString).mkString(",") + "]"
  }
}
