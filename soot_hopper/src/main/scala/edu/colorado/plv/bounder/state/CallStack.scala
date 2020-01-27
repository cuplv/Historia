package edu.colorado.plv.bounder.state

import edu.colorado.plv.bounder.ir.MethodLoc

case class CallStack(frames: List[CallStackFrame])

case class CallStackFrame(methodLoc : MethodLoc, locals: Set[LocalPtEdge])
