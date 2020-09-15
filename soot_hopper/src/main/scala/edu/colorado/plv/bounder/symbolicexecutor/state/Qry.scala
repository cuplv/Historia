package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, IRWrapper, InternalMethodReturn, LineLoc, Loc, LocalWrapper, MethodWrapper, VirtualInvoke}
import edu.colorado.plv.bounder.symbolicexecutor.SymbolicExecutorConfig
import soot.SootMethod

object Qry {
  private var qryIdCounter = 0
  private def getFreshQryId = { qryIdCounter += 1; qryIdCounter }
  def make[M,C](config: SymbolicExecutorConfig[M,C], loc:AppLoc, locals : Map[StackVar, PureVar], pureFormula: Set[PureConstraint]):Qry = {
    // Note: no return location for arbitrary query
//    val queryStack = List(CallStackFrame(loc,None, locals))

    val acr = config.c.getResolver
    val cbexit = acr.resolveCallbackEntry(loc.method) match{
      case Some(CallbackMethodInvoke(clazz, name, loc)) =>
        CallbackMethodReturn(clazz,name, loc)
      case None => {

        InternalMethodReturn(loc.method.classType, loc.method.simpleName, loc.method)
      }
      case _ =>
        throw new IllegalArgumentException
    }
    val queryStack = List(CallStackFrame(cbexit, None,locals))
//    val queryStack = Nil
    SomeQry(State(queryStack,Map(), pureFormula),loc)
  }
  def makeReceiverNonNull[M,C](config: SymbolicExecutorConfig[M,C],
                               w:IRWrapper[M,C],
                               className:String,
                               methodName:String, line:Int):Qry = {
    val locs = w.findLineInMethod(className, methodName,line)

    val derefLocs: Iterable[AppLoc] = locs.filter(pred = a => {
      w.cmdAfterLocation(a).isInstanceOf[AssignCmd[_, _]]
    })
    assert(derefLocs.size == 1)
    // Get location of query
    val derefLoc: AppLoc = derefLocs.iterator.next
    // Get name of variable that should not be null
    val varname = w.cmdAfterLocation(derefLoc) match {
      case a@AssignCmd(_, VirtualInvoke(LocalWrapper(name,_),_,_,_,_), _, _) => name
      case _ => ???
    }

    val pureVar = PureVar()
    Qry.make(config, derefLoc, Map((StackVar(varname,"java.lang.Object"),pureVar)),
      Set(PureConstraint(pureVar, Equals, NullVal)))
  }

}
//TODO: add extra constraints into query later
//heapConstraints : Set[HeapPtEdge],
//pureConstraints : Set[PureConstraint],
sealed trait Qry {
  def loc: Loc
}
//Query consists of a location and an abstract state defined at the program point just before that location.
case class SomeQry(state:State, loc: Loc) extends Qry {
  override def toString:String = loc.toString + "  " + state.toString
}
// Infeasible precondition, path refuted
case class BottomQry(loc:Loc) extends Qry {
  override def toString:String = "refuted"
}