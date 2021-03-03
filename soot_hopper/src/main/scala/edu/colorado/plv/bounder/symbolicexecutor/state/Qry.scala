package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.symbolicexecutor.{SymbolicExecutor}
import upickle.default.{macroRW, ReadWriter => RW}

import scala.util.matching.Regex

object Qry {
  implicit val rw:RW[Qry] = RW.merge(macroRW[SomeQry], macroRW[BottomQry], macroRW[WitnessedQry])

  def makeReach[M,C](ex: SymbolicExecutor[M,C],
                     w:IRWrapper[M,C],
                     className:String,
                     methodName:String, line:Int):Set[Qry] = {
    val locs = w.findLineInMethod(className, methodName,line)
    assert(locs.nonEmpty, "found no locations")
    val targetLoc = locs.head
    val containingMethodPos: List[Loc] = BounderUtil.resolveMethodReturnForAppLoc(ex.getAppCodeResolver, targetLoc)
    containingMethodPos.map{method =>
      val queryStack = List(CallStackFrame(method, None,Map()))
      val state0 = State.topState.copy(callStack = queryStack)
      SomeQry(state0, targetLoc)
    }.toSet
  }

  def makeCallinReturnNull[M,C](ex: SymbolicExecutor[M,C],
                                w:IRWrapper[M,C],
                                className:String,
                                methodName:String,
                                line:Int,
                                callinMatches:Regex):Set[Qry] ={
    val locs = w.findLineInMethod(className, methodName,line)
    val callinLocals = locs.flatMap(a => {
      w.cmdAtLocation(a) match{
        case AssignCmd(target : LocalWrapper, i:Invoke, loc) if callinMatches.matches(i.targetMethod) =>
          Some((target,loc.copy(isPre = false)))
        case _ => None
      }
    })
    assert(callinLocals.size == 1, s"Wrong number of locations found while making query " +
      s"got: ${callinLocals.size}, expected 1")
    val (local, location) = callinLocals.head

    //local.method
    val containingMethodPos: List[Loc] = BounderUtil.resolveMethodReturnForAppLoc(ex.getAppCodeResolver, location)

    containingMethodPos.map { pos =>
      val queryStack = List(CallStackFrame(pos, None, Map()))
      val state = State.topState.copy(callStack = queryStack)
      val (pv,state1) = state.getOrDefine(local)
      val state2 = state1.copy(pureFormula = Set(PureConstraint(pv, Equals, NullVal)))
      SomeQry(state2, location)
    }.toSet
  }

  def makeReceiverNonNull[M,C](ex: SymbolicExecutor[M,C],
                               w:IRWrapper[M,C],
                               className:String,
                               methodName:String, line:Int):Set[Qry] = {
    val locs = w.findLineInMethod(className, methodName,line)

    val derefLocs: Iterable[AppLoc] = locs.filter(a => w.cmdAtLocation(a) match {
      case AssignCmd(_, _:VirtualInvoke, _) => true
      case AssignCmd(_, _:SpecialInvoke, _) => true
      case InvokeCmd(_:VirtualInvoke,_) => true
      case InvokeCmd(_:SpecialInvoke,_) => true
      case _ => false
    })

    assert(derefLocs.size == 1)
    // Get location of query
    val derefLoc: AppLoc = derefLocs.iterator.next
    // Get name of variable that should not be null
    val varname = w.cmdAtLocation(derefLoc) match {
      case AssignCmd(_, VirtualInvoke(localWrapper,_,_,_), _) => localWrapper
      case InvokeCmd(VirtualInvoke(localWrapper,_,_,_),_) => localWrapper
      case _ => ???
    }

    val cbexits = BounderUtil.resolveMethodReturnForAppLoc(ex.getAppCodeResolver, derefLoc)
    cbexits.map { cbexit =>
      val queryStack = List(CallStackFrame(cbexit, None, Map()))
      val state0 = State.topState.copy(callStack = queryStack)


      val (pureVar, state1) = state0.getOrDefine(varname)
      SomeQry(state1.copy(pureFormula = Set(PureConstraint(pureVar, Equals, NullVal))), derefLoc)
    }.toSet
  }


}

sealed trait Qry {
  def loc: Loc
  def state: State
  def toString:String
}
//Query consists of a location and an abstract state defined at the program point just before that location.
case class SomeQry(state:State, loc: Loc) extends Qry {
  override def toString:String = loc.toString + "  " + state.toString
}
// Infeasible precondition, path refuted
case class BottomQry(state:State, loc:Loc) extends Qry {
  override def toString:String = "!!!refuted!!! loc: " + loc.toString + " state: " + state.toString
}

case class WitnessedQry(state:State, loc:Loc) extends Qry {
  override def toString:String = "!!!witnessed!!! loc: " + loc.toString + " state: " + state.toString
}
