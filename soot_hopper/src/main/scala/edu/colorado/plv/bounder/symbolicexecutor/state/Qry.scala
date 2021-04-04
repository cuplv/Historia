package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.symbolicexecutor.SymbolicExecutor
import ujson.Value
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
      val state0 = State.topState.copy(callStack = queryStack, nextCmd = List(targetLoc))
      SomeQry(state0, targetLoc)
    }.toSet
  }

  def makeCallinReturnNull[M,C](ex: SymbolicExecutor[M,C],
                                w:IRWrapper[M,C],
                                className:String,
                                methodName:String,
                                line:Int,
                                callinMatches:Regex):Set[Qry] ={
    implicit val ch = ex.getClassHierarchy
    val locs = w.findLineInMethod(className, methodName,line)
    val callinLocals = locs.flatMap(a => {
      w.cmdAtLocation(a) match{
        case AssignCmd(target : LocalWrapper, i:Invoke, loc) if callinMatches.matches(i.targetMethod) =>
          Some((target,loc.copy(isPre = false)))
        case InvokeCmd(i,loc) if callinMatches.matches(i.targetMethod) =>
          throw new IllegalStateException("Callin return not assigned to variable.")
        case c =>
          None
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
      val state2 = state1.copy(pureFormula = Set(PureConstraint(pv, Equals, NullVal)), nextCmd = List(location))
      SomeQry(state2, location)
    }.toSet
  }

  def makeReceiverNonNull[M,C](ex: SymbolicExecutor[M,C],
                               w:IRWrapper[M,C],
                               className:String,
                               methodName:String,
                               line:Int,
                               fieldOrMethod: Option[Regex] = None
                              ):Set[Qry] = {
    implicit val ch = ex.getClassHierarchy

    val locs = w.findLineInMethod(className, methodName,line)
    val isTarget = fieldOrMethod.getOrElse("(.*)".r)
    val derefLocs = locs.filter(a => w.cmdAtLocation(a) match {
      case AssignCmd(_, _:VirtualInvoke, _) => true
      case AssignCmd(_, _:SpecialInvoke, _) => true
      case InvokeCmd(_:VirtualInvoke,_) => true
      case InvokeCmd(_:SpecialInvoke,_) => true
      case AssignCmd(_, FieldReference(base,_,_, isTarget(name)),_) => true
      case _ => false
    })

//    assert(derefLocs.size == 1)
    // Get location of query
    // Find last dereference on line if not specified
    val derefLoc: AppLoc = derefLocs.toList.last
    // Get name of variable that should not be null
    val varname = w.cmdAtLocation(derefLoc) match {
      case AssignCmd(_, VirtualInvoke(localWrapper,_,_,_), _) => localWrapper
      case InvokeCmd(VirtualInvoke(localWrapper,_,_,_),_) => localWrapper
      case AssignCmd(_, FieldReference(base,_,_,_),_)  => base
      case _ => ???
    }

    val cbexits = BounderUtil.resolveMethodReturnForAppLoc(ex.getAppCodeResolver, derefLoc)
    cbexits.map { cbexit =>
      val queryStack = List(CallStackFrame(cbexit, None, Map()))
      val state0 = State.topState.copy(callStack = queryStack)


      val (pureVar, state1) = state0.getOrDefine(varname)
      SomeQry(state1.copy(pureFormula = Set(PureConstraint(pureVar, Equals, NullVal)),
        nextCmd = List(derefLoc)), derefLoc)
    }.toSet
  }


}
sealed trait InitialQuery{
  def make[M,C](sym:SymbolicExecutor[M,C], w:IRWrapper[M,C]):Set[Qry]
}
object InitialQuery{
  private def vToJ(v:(String,Any)):(String,Value) = v match{
    case (k,v:String) => k -> ujson.Str(v)
    case (k,v:Integer) => k -> ujson.Num(v.toDouble)
  }
  implicit val rw:RW[InitialQuery] = upickle.default.readwriter[ujson.Value].bimap[InitialQuery](
    {
      case Reachable(className, methodName, line) =>
        val m = Map(
          "t" -> "Reachable",
          "className" -> className,
          "methodName" -> methodName,
          "line" -> line
        ).map(vToJ)
        ujson.Obj.from(m)
      case ReceiverNonNull(className, methodName, line) =>
        val m = Map(
          "t" -> "ReceiverNonNull",
          "className" -> className,
          "methodName" -> methodName,
          "line" -> line
        ).map(vToJ)
        ujson.Obj.from(m)
      case CallinReturnNonNull(className, methodName, line, callinRegex) =>
        val m = Map(
          "t" -> "CallinReturnNull",
          "className" -> className,
          "methodName" -> methodName,
          "line" -> line,
          "callinRegex" -> callinRegex
        ).map(vToJ)
        ujson.Obj.from(m)
    },
    json => json.obj("t").str match{
      case "Reachable" => Reachable(json.obj("className").str, json.obj("methodName").str,json.obj("line").num.toInt)
      case "ReceiverNonNull" =>
        ReceiverNonNull(json.obj("className").str, json.obj("methodName").str,json.obj("line").num.toInt)
      case "CallinReturnNonNull" =>
        CallinReturnNonNull(json.obj("className").str, json.obj("methodName").str,json.obj("line").num.toInt,
          json.obj("callinRegex").str)
    }
  )
}
case class Reachable(className:String, methodName:String, line:Integer) extends InitialQuery {
  override def make[M, C](sym: SymbolicExecutor[M, C], w: IRWrapper[M, C]): Set[Qry] =
    Qry.makeReach(sym,w,className, methodName, line)
}
case class ReceiverNonNull(className:String, methodName:String, line:Integer) extends InitialQuery {
  override def make[M, C](sym: SymbolicExecutor[M, C], w: IRWrapper[M, C]): Set[Qry] =
    Qry.makeReceiverNonNull(sym,w, className, methodName, line)
}
case class CallinReturnNonNull(className:String, methodName:String,
                               line:Integer, callinRegex:String) extends InitialQuery{
  override def make[M, C](sym: SymbolicExecutor[M, C], w: IRWrapper[M, C]): Set[Qry] =
    Qry.makeCallinReturnNull(sym,w, className, methodName, line, callinRegex.r)
}

sealed trait Qry {
  def loc: Loc
  def state: State
  def toString:String
  def copyWithNewLoc(upd: Loc => Loc):Qry
  def copyWithNewState(state:State):Qry
}
//Query consists of a location and an abstract state defined at the program point just before that location.
case class SomeQry(state:State, loc: Loc) extends Qry {
  override def toString:String = loc.toString + "  " + state.toString

  override def copyWithNewLoc(upd: Loc => Loc): Qry = this.copy(loc = upd(loc))

  override def copyWithNewState(state: State): Qry = this.copy(state = state)
}
// Infeasible precondition, path refuted
case class BottomQry(state:State, loc:Loc) extends Qry {
  override def toString:String = "!!!refuted!!! loc: " + loc.toString + " state: " + state.toString
  override def copyWithNewLoc(upd: Loc => Loc): Qry = this.copy(loc = upd(loc))
  override def copyWithNewState(state: State): Qry = this.copy(state = state)
}

case class WitnessedQry(state:State, loc:Loc) extends Qry {
  override def toString:String = "!!!witnessed!!! loc: " + loc.toString + " state: " + state.toString
  override def copyWithNewLoc(upd: Loc => Loc): Qry = this.copy(loc = upd(loc))
  override def copyWithNewState(state: State): Qry = this.copy(state = state)
}
