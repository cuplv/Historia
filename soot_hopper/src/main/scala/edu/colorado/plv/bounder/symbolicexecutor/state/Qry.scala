package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.LSSpec
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.{SymbolicExecutor, TransferFunctions}
import ujson.Value
import upickle.default.{macroRW, ReadWriter => RW}

import scala.jdk.CollectionConverters.CollectionHasAsScala
import scala.util.matching.Regex

object Qry {

  implicit val rw:RW[Qry] = RW.merge(macroRW[LiveQry], macroRW[BottomQry], macroRW[WitnessedQry])

  def makeReach[M,C](ex: SymbolicExecutor[M,C],
                     className:String,
                     methodName:String, line:Int):Set[Qry] = {
    val locs = ex.w.findLineInMethod(className, methodName,line)
    assert(locs.nonEmpty, "found no locations")
    val targetLoc = locs.head
    val containingMethodPos: List[Loc] = BounderUtil.resolveMethodReturnForAppLoc(ex.getAppCodeResolver, targetLoc)
    val res:Set[Qry] = containingMethodPos.map{method =>
      val queryStack = List(CallStackFrame(method, None,Map()))
      val state0 = State.topState.copy(sf = State.topState.sf.copy(callStack = queryStack), nextCmd = List(targetLoc))
      LiveQry(state0, targetLoc)
    }.toSet
    res
  }

  def makeCallinReturnNull[M,C](ex: SymbolicExecutor[M,C],
                                className:String,
                                methodName:String,
                                line:Int,
                                callinMatches:Regex):Set[Qry] ={
    implicit val wr: IRWrapper[M, C] = ex.w
    implicit val ch: ClassHierarchyConstraints = ex.getClassHierarchy
    val locs = wr.findLineInMethod(className, methodName,line)
    val callinLocals = locs.flatMap(a => {
      wr.cmdAtLocation(a) match{
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
      val state = State.topState.copy(sf = State.topState.sf.copy(callStack = queryStack))
      val (pv,state1) = state.getOrDefine(local, None)
      val state2 = state1.addPureConstraint(PureConstraint(pv, Equals, NullVal)).copy(nextCmd = List(location))
      LiveQry(state2, location)
    }.toSet
  }

  def makeAllReceiverNonNull[M,C](ex:SymbolicExecutor[M,C],className: String): Set[Qry] = {
    //TODO: clean up this method
    implicit val wra: IRWrapper[M, C] = ex.w
    implicit val ch: ClassHierarchyConstraints = wra.getClassHierarchyConstraints
    val jw = wra.asInstanceOf[JimpleFlowdroidWrapper]
    val c = jw.getClassByName(className)
    val cmds = (for {
      cl <-c
      m <- cl.getMethods.asScala
      cmd <- m.getActiveBody.getUnits.asScala
        .map(v => jw.makeCmd(v,m, Some(AppLoc(JimpleMethodLoc(m),JimpleLineLoc(v,m),isPre = true))))
    } yield cmd).toSet

    val qrys = cmds.map{cmd =>
      val baseV = cmd match {
        case AssignCmd(_, VirtualInvoke(localWrapper,_,_,_), _) => Some(localWrapper)
        case AssignCmd(_, SpecialInvoke(localWrapper,_,_,_), _) => Some(localWrapper)
        case InvokeCmd(VirtualInvoke(localWrapper,_,_,_),_) => Some(localWrapper)
        case InvokeCmd(SpecialInvoke(localWrapper,_,_,_),_) => Some(localWrapper)
        case AssignCmd(_, FieldReference(base,_,_,_),_)  => Some(base)
        case AssignCmd(FieldReference(base,_,_,_),_,_)  => Some(base)
        case _ => None
      }
      baseV.map { v =>
        val cbexits = BounderUtil.resolveMethodReturnForAppLoc(ex.getAppCodeResolver, cmd.getLoc)
        assert(cbexits.nonEmpty, s"Malformed IR, method has no returns:  ${cmd.getLoc.method}")
        val queryStack = List(CallStackFrame(cbexits.head, None, Map()))
        val state0 = State.topState.copy(sf = State.topState.sf.copy(callStack = queryStack))
        val (pureVar, state1) = state0.getOrDefine(v, None)
        LiveQry(state1.addPureConstraint(PureConstraint(pureVar, Equals, NullVal)).copy(
          nextCmd = List(cmd.getLoc)), cmd.getLoc)
      }
    }

    val out = qrys.flatten
    out.map(a => a)
  }

  def makeReceiverNonNull[M,C](ex: SymbolicExecutor[M,C],
                               className:String,
                               methodName:String,
                               line:Int,
                               fieldOrMethod: Option[Regex] = None
                              ):Set[Qry] = {
    implicit val wr: IRWrapper[M, C] = ex.w
    implicit val ch: ClassHierarchyConstraints = ex.getClassHierarchy

    val locs = wr.findLineInMethod(className, methodName,line)
    val isTarget = fieldOrMethod.getOrElse("(.*)".r)
    val derefLocs = locs.filter(a => wr.cmdAtLocation(a) match {
      case AssignCmd(_, _:VirtualInvoke, _) => true
      case AssignCmd(_, _:SpecialInvoke, _) => true
      case InvokeCmd(_:VirtualInvoke,_) => true
      case InvokeCmd(_:SpecialInvoke,_) => true
      case AssignCmd(_, FieldReference(base,_,_, isTarget(name)),_) => true
      case AssignCmd(_, FieldReference(base,_,_, isTarget()),_) => true
      case _ => false
    })

//    assert(derefLocs.size == 1)
    // Get location of query
    // Find last dereference on line if not specified
    val derefLoc: AppLoc = derefLocs.toList.last
    // Get name of variable that should not be null
    val varname = wr.cmdAtLocation(derefLoc) match {
      case AssignCmd(_, VirtualInvoke(localWrapper,_,_,_), _) => localWrapper
      case AssignCmd(_, SpecialInvoke(localWrapper,_,_,_), _) => localWrapper
      case InvokeCmd(VirtualInvoke(localWrapper,_,_,_),_) => localWrapper
      case InvokeCmd(SpecialInvoke(localWrapper,_,_,_),_) => localWrapper
      case AssignCmd(_, FieldReference(base,_,_,_),_)  => base
      case o =>
        println(o)
        ???
    }

    val cbexits = BounderUtil.resolveMethodReturnForAppLoc(ex.getAppCodeResolver, derefLoc)
    cbexits.map { cbexit =>
      val queryStack = List(CallStackFrame(cbexit, None, Map()))
      val state0 = State.topState.copy(sf = State.topState.sf.copy(callStack = queryStack))
      val (pureVar, state1) = state0.getOrDefine(varname, cbexit.containingMethod)
      LiveQry(state1.addPureConstraint(PureConstraint(pureVar, Equals, NullVal)).copy(
        nextCmd = List(derefLoc)), derefLoc)
    }.toSet
  }


}
sealed trait InitialQuery{
  def make[M,C](sym:SymbolicExecutor[M,C]):Set[Qry]
}
object InitialQuery{
  private def vToJ(v:(String,Any)):(String,Value) = v match{
    case (k,v:String) => k -> ujson.Str(v)
    case (k,v:Integer) => k -> ujson.Num(v.toDouble)
    case (_,v) => throw new IllegalArgumentException(s"type ${v.getClass.toString} not supported")
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
      case ReceiverNonNull(className, methodName, line, matcher) =>

        val m = Map(
          "t" -> "ReceiverNonNull",
          "className" -> className,
          "methodName" -> methodName,
          "line" -> line
        )
        val m2 = if(matcher.isEmpty) m else m + ("matcher" -> matcher.get)
        val m3 = m2.map(vToJ)
        ujson.Obj.from(m3)
      case CallinReturnNonNull(className, methodName, line, callinRegex) =>
        val m = Map(
          "t" -> "CallinReturnNull",
          "className" -> className,
          "methodName" -> methodName,
          "line" -> line,
          "callinRegex" -> callinRegex
        ).map(vToJ)
        ujson.Obj.from(m)
      case AllReceiversNonNull(className) =>
        val m = Map(
          "t" -> "AllReceiversNonNull",
          "className" -> className
        ).map(vToJ)
        ujson.Obj.from(m)
    },
    json => json.obj("t").str match{
      case "Reachable" => Reachable(json.obj("className").str, json.obj("methodName").str,json.obj("line").num.toInt)
      case "ReceiverNonNull" =>
        val matcher = if(json.obj.contains("matcher")) Some(json.obj("matcher").str) else None
        ReceiverNonNull(json.obj("className").str, json.obj("methodName").str,json.obj("line").num.toInt, matcher)
      case "CallinReturnNonNull" =>
        CallinReturnNonNull(json.obj("className").str, json.obj("methodName").str,json.obj("line").num.toInt,
          json.obj("callinRegex").str)
      case "AllReceiversNonNull" =>
        AllReceiversNonNull(json.obj("className").str)
    }
  )
}
case class Reachable(className:String, methodName:String, line:Integer) extends InitialQuery {
  override def make[M, C](sym: SymbolicExecutor[M, C]): Set[Qry] =
    Qry.makeReach(sym,className, methodName, line)
}
case class ReceiverNonNull(className:String, methodName:String, line:Integer,
                           receiverMatcher:Option[String] = None) extends InitialQuery {
  override def make[M, C](sym: SymbolicExecutor[M, C]): Set[Qry] =
    Qry.makeReceiverNonNull(sym, className, methodName, line,fieldOrMethod = receiverMatcher.map(_.r))
}
case class AllReceiversNonNull(className:String) extends InitialQuery {
  override def make[M, C](sym: SymbolicExecutor[M, C]): Set[Qry] =
    Qry.makeAllReceiverNonNull(sym,className)
}
case class CallinReturnNonNull(className:String, methodName:String,
                               line:Integer, callinRegex:String) extends InitialQuery{
  override def make[M, C](sym: SymbolicExecutor[M, C]): Set[Qry] =
    Qry.makeCallinReturnNull(sym, className, methodName, line, callinRegex.r)
}

case class DisallowedCallin(className:String, methodName:String, s:LSSpec) extends InitialQuery{
  assert(s.target.mt == CIEnter, "Disallow must be callin entry.")
  private def invokeMatches(i:Invoke)(implicit ch:ClassHierarchyConstraints):Option[(String,String)] = {
    val iClazz = i.targetClass
    val iSign = i.targetMethod
    val res = s.target.signatures.matches(iClazz, iSign)
    if(res) Some(iClazz, iSign) else None
  }

  private def getMatchingCallin(cmd:CmdWrapper)
                               (implicit ch:ClassHierarchyConstraints):Option[(String,String)] = cmd match {
    case AssignCmd(_, i:Invoke, _) => invokeMatches(i)
    case InvokeCmd(method, _) => invokeMatches(method)
    case _ => None
  }
  override def make[M, C](sym: SymbolicExecutor[M, C]): Set[Qry] = {
    //TODO: Bug where this is empty
    implicit val ch = sym.w.getClassHierarchyConstraints
    val locations: Set[AppLoc] = sym.w.findInMethod(className, methodName, cmd => getMatchingCallin(cmd).isDefined).toSet
    assert(locations.nonEmpty, s"Empty target locations matching disallow: $s")
//    val containingMethodPos =
//      locations.flatMap(location => BounderUtil.resolveMethodReturnForAppLoc(sym.getAppCodeResolver, location))
    locations.map { location =>
      val cmd = sym.w.cmdAtLocation(location)
      val retLoc = BounderUtil.resolveMethodReturnForAppLoc(sym.getAppCodeResolver, location)
      val sf = CallStackFrame(retLoc.head, None, Map())
      val state = State.topState.copy(sf = State.topState.sf.copy(callStack = sf :: Nil))
      val allVar = TransferFunctions.inVarsForCall(location,sym.w)
      val stateWithDisallow = sym.transfer.newDisallowTransfer(location.method,
        CIEnter, getMatchingCallin(cmd).get, allVar, state,Some(s))
      assert(stateWithDisallow.size == 1)
      LiveQry(stateWithDisallow.head, location.copy(isPre = true))
    }
  }
}

sealed trait Qry {
  def loc: Loc
  def getState: Option[State]
  def toString:String
  def copyWithNewState(state:State):Qry
}
//Query consists of a location and an abstract state defined at the program point just before that location.
case class LiveQry(state:State, loc: Loc) extends Qry {
  override def toString:String = loc.toString + "  " + getState.toString

  override def copyWithNewState(state: State): Qry = this.copy(state = state)

  override def getState: Option[State] = Some(state)
}
// A live query where we didn't retain the state to save space
// This query can only come from reading the output of a truncated run
//TODO: alter types so that getState doesn't need to return option
case class LiveTruncatedQry(loc:Loc) extends Qry{
  override def getState: Option[State] = None

  override def copyWithNewState(state: State): Qry = this
}
case class WitnessedTruncatedQry(loc:Loc, explanation: WitnessExplanation) extends Qry{
  override def getState: Option[State] = None

  override def copyWithNewState(state: State): Qry = this
}
case class BottomTruncatedQry(loc:Loc) extends Qry{
  override def getState: Option[State] = None

  override def copyWithNewState(state: State): Qry = this
}
// Infeasible precondition, path refuted
case class BottomQry(state:State, loc:Loc) extends Qry {
  override def toString:String = "!!!refuted!!! loc: " + loc.toString + " state: " + getState.toString
  override def copyWithNewState(state: State): Qry = this.copy(state = state)

  override def getState: Option[State] = Some(state)
}

case class WitnessedQry(state:State, loc:Loc, explain:WitnessExplanation) extends Qry {
  override def toString:String = "!!!witnessed!!! loc: " + loc.toString + " state: " + getState.toString
  override def copyWithNewState(state: State): Qry = this.copy(state = state)

  override def getState: Option[State] = Some(state)
}
