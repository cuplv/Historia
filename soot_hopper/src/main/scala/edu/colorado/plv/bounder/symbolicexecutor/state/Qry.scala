package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir._
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, Signature}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.{AbstractInterpreter, MustExecutor, TransferFunctions}
import ujson.Value
import upickle.default.{macroRW, read, write, ReadWriter => RW}

import java.util.Objects
import java.util.regex.PatternSyntaxException
import scala.jdk.CollectionConverters.CollectionHasAsScala
import scala.util.matching.Regex

object Qry {

  implicit val rw:RW[Qry] = macroRW

  def makeReach[M,C](ex: AbstractInterpreter[M,C],
                     sig:Signature, line:Int):Set[Qry] = {
    val locs = ex.w.findLineInMethod(sig,line)
    assert(locs.nonEmpty, "found no locations")
    val targetLoc = locs.head
    val containingMethodPos: List[Loc] = BounderUtil.resolveMethodReturnForAppLoc(ex.getAppCodeResolver, targetLoc)
    val res:Set[Qry] = containingMethodPos.map{method =>
      val queryStack = List(CallStackFrame(method, None,Map()))
      val state0 = State.topState.copy(sf = State.topState.sf.copy(callStack = queryStack), nextCmd = List(targetLoc))
      Qry(state0, targetLoc, Live)
    }.toSet
    res
  }

  def makeCallinReturnNull[M,C](ex: AbstractInterpreter[M,C],
                                sig:Signature,
                                line:Int,
                                callinMatches:Regex):Set[Qry] ={
    implicit val wr: IRWrapper[M, C] = ex.w
    implicit val ch: ClassHierarchyConstraints = ex.getClassHierarchy
    val locs = wr.findLineInMethod(sig,line)
    val callinLocals = locs.flatMap(a => {
      wr.cmdAtLocation(a) match{
        case AssignCmd(tgt : LocalWrapper, i:Invoke, loc) if callinMatches.matches(i.targetSignature.methodSignature) =>
          Some((tgt,loc.copy(isPre = false)))
        case InvokeCmd(i,loc) if callinMatches.matches(i.targetSignature.methodSignature) =>
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
      Qry(state2, location, Live)
    }.toSet
  }

  def makeAllReceiverNonNull[M,C](ex:AbstractInterpreter[M,C], className: String): Set[Qry] = {
    //TODO: clean up this method
    implicit val wra: IRWrapper[M, C] = ex.w
    implicit val ch: ClassHierarchyConstraints = wra.getClassHierarchyConstraints
    val jw = wra.asInstanceOf[SootWrapper]
    val c = jw.getClassByName(className)
    val cmds = (for {
      cl <-c
      m <- cl.getMethods.asScala
      cmd <- if(m.isAbstract || !m.hasActiveBody) List.empty else m.getActiveBody.getUnits.asScala //abstract catches iface and abst classes
        .map(v => SootWrapper.makeCmd(v,m, AppLoc(JimpleMethodLoc(m),JimpleLineLoc(v,m),isPre = true)))
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
        Qry(state1.addPureConstraint(PureConstraint(pureVar, Equals, NullVal)).copy(
          nextCmd = List(cmd.getLoc)), cmd.getLoc, Live)
      }
    }

    val out = qrys.flatten
    out.map(a => a)
  }

  def makeReceiverNonNull[M,C](ex: AbstractInterpreter[M,C],
                               sig:Signature,
                               line:Int,
                               fieldOrMethod: Option[Regex] = None
                              ):Set[Qry] = {
    implicit val wr: IRWrapper[M, C] = ex.w
    implicit val ch: ClassHierarchyConstraints = ex.getClassHierarchy

    val locs = wr.findLineInMethod(sig, line)
    val isTarget = fieldOrMethod.getOrElse("(.*)".r)
    val derefLocs = locs.filter(a => wr.cmdAtLocation(a) match {
      case AssignCmd(_, i:VirtualInvoke, _) =>
        isTarget.matches(i.toString)
      case AssignCmd(_, i:SpecialInvoke, _) =>
        isTarget.matches(i.toString)
      case InvokeCmd(i:VirtualInvoke,_) =>
        isTarget.matches(i.toString)
      case InvokeCmd(i:SpecialInvoke,_) =>
        isTarget.matches(i.toString)
      case AssignCmd(_, fr@FieldReference(base,_,_, isTarget(name)),_) => true
      case AssignCmd(_, FieldReference(base,_,_, isTarget()),_) => true
      case _ => false
    })

    assert(derefLocs.size == 1, s"Exception: Too many locations found: \n ${derefLocs.mkString("\\n")}")
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
      Qry(state1.addPureConstraint(PureConstraint(pureVar, Equals, NullVal)).copy(
        nextCmd = List(derefLoc)), derefLoc, Live)
    }.toSet
  }


}
sealed trait InitialQuery{
  def fileName:String

  def make[M,C](sym:AbstractInterpreter[M,C]):Set[Qry]
}
object InitialQuery{
  private def vToJ(v:(String,Any)):(String,Value) = v match{
    case (k,v:String) => k -> ujson.Str(v)
    case (k,v:Integer) => k -> ujson.Num(v.toDouble)
    case (_,v) => throw new IllegalArgumentException(s"type ${v.getClass.toString} not supported")
  }
  implicit val rw:RW[InitialQuery] = upickle.default.readwriter[ujson.Value].bimap[InitialQuery](
    {
      case Reachable(sig, line) =>
        val m = Map(
          "t" -> "Reachable",
          "className" -> sig.base,
          "methodName" -> sig.methodSignature,
          "line" -> line
        ).map(vToJ)
        ujson.Obj.from(m)
      case ReceiverNonNull(sig, line, matcher) =>

        val m = Map(
          "t" -> "ReceiverNonNull",
          "className" -> sig.base,
          "methodName" -> sig.methodSignature,
          "line" -> line
        )
        val m2 = if(matcher.isEmpty) m else m + ("matcher" -> matcher.get)
        val m3 = m2.map(vToJ)
        ujson.Obj.from(m3)
      case CallinReturnNonNull(sig, line, callinRegex) =>
        val m = Map(
          "t" -> "CallinReturnNull",
          "className" -> sig.base,
          "methodName" -> sig.methodSignature,
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
      case DisallowedCallin(className, methodName, s) =>
        val m = Map(
          "t" -> "DisallowedCallin",
          "className" -> className,
          "methodName" -> methodName,
          "s" -> write[LSSpec](s)
        ).map(vToJ)
        ujson.Obj.from(m)
    },
    json => json.obj("t").str match{
      case "Reachable" =>
        Reachable(Signature(json.obj("className").str, json.obj("methodName").str),json.obj("line").num.toInt)
      case "ReceiverNonNull" =>
        val matcher = if(json.obj.contains("matcher")) Some(json.obj("matcher").str) else None
        ReceiverNonNull(Signature(json.obj("className").str, json.obj("methodName").str),
          json.obj("line").num.toInt, matcher)
      case "CallinReturnNonNull" =>
        CallinReturnNonNull(Signature(json.obj("className").str, json.obj("methodName").str),json.obj("line").num.toInt,
          json.obj("callinRegex").str)
      case "AllReceiversNonNull" =>
        AllReceiversNonNull(json.obj("className").str)
      case "DisallowedCallin" =>
        DisallowedCallin(json.obj("className").str, json.obj("methodName").str, read[LSSpec](json.obj("s").str))
    }
  )
}
case class Reachable(sig:Signature, line:Integer) extends InitialQuery {
  override def make[M, C](sym: AbstractInterpreter[M, C]): Set[Qry] =
    Qry.makeReach(sym,sig, line)

  override def fileName: String = s"Reachable_${sig}_${line}"
}

case class DirectInitialQuery(qry:Qry) extends InitialQuery{
  def fileName = {
    val appLoc = qry.loc.asInstanceOf[AppLoc]
    val method = appLoc.method
    val line = appLoc.line.lineNumber
    BounderUtil.sanitizeString(s"${method.classType}__${method.simpleName}__" +
    s"line_${line}__${qry.loc.hashCode()}__${qry.state.hashCode()}") + ".cfg"
  }

  override def make[M, C](sym: AbstractInterpreter[M, C]): Set[Qry] = Set(qry)
}

case class ReceiverNonNull(sig:Signature, line:Integer,
                           receiverMatcher:Option[String]) extends InitialQuery {
  override def make[M, C](sym: AbstractInterpreter[M, C]): Set[Qry] = {
    try {
      val matcherTrimmed = receiverMatcher.map(m => if(m.contains("(")) s".*${m.split("\\(").head}.*" else m)
      Qry.makeReceiverNonNull(sym, sig, line, fieldOrMethod = matcherTrimmed.map(_.r))
    } catch{
      case _:PatternSyntaxException => {
        // receiver matcher wasn't a regex, attempt to automatically convert
        val newRecMat:Option[String] = receiverMatcher.map(v => s".*${MustExecutor.parseJavaSignature(v)._2}.*")
        Qry.makeReceiverNonNull(sym, sig, line, fieldOrMethod = newRecMat.map(_.r))
      }
    }
  }

  override def fileName: String = s"ReceiverNonNull_${sig}_${line}_" +
    s"${receiverMatcher.map(BounderUtil.sanitizeString).getOrElse("")}"
}
case class AllReceiversNonNull(className:String) extends InitialQuery {
  override def make[M, C](sym: AbstractInterpreter[M, C]): Set[Qry] =
    Qry.makeAllReceiverNonNull(sym,className)

  override def fileName: String = ???
}
case class CallinReturnNonNull(sig:Signature,
                               line:Integer, callinRegex:String) extends InitialQuery{
  override def make[M, C](sym: AbstractInterpreter[M, C]): Set[Qry] =
    Qry.makeCallinReturnNull(sym, sig, line, callinRegex.r)

  override def fileName: String = s"CallinReturnNonNull_${sig}_${line}_${BounderUtil.sanitizeString(callinRegex)}"
}

object DisallowedCallin{
  def mk(loc:AppLoc, s:LSSpec):DisallowedCallin = {
    val className = loc.method.classType
    val methodName = loc.method.simpleName
    DisallowedCallin(className, methodName,s)
  }
}
case class DisallowedCallin(className:String, methodName:String, s:LSSpec) extends InitialQuery{
  assert(s.target.mt == CIEnter, s"Disallow must be callin entry. found: ${s.target}")
  def fileName:String = BounderUtil.sanitizeString(s"${this.className}__${this.methodName}__" +
    s"disallow_${this.s.target.identitySignature}") + ".cfg"
  private def invokeMatches(i:Invoke)(implicit ch:ClassHierarchyConstraints):Option[Signature] = {
    val tgtSig = i.targetSignature
    val res = s.target.signatures.matches(tgtSig)
    if(res) Some(tgtSig) else None
  }

  private def getMatchingCallin(cmd:CmdWrapper)
                               (implicit ch:ClassHierarchyConstraints):Option[Signature] = cmd match {
    case AssignCmd(_, i:Invoke, _) => invokeMatches(i)
    case InvokeCmd(method, _) => invokeMatches(method)
    case _ => None
  }
  override def make[M, C](sym: AbstractInterpreter[M, C]): Set[Qry] = {
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
      Qry(stateWithDisallow.head, location.copy(isPre = true), Live)
    }
  }
}

object SearchState{
  def apply(str:String):SearchState = str match {
    case "unknown" => Unknown
    case "live" => Live
    case "refuted" => BottomQry
    case "witnessed" => WitnessedQry(None)
    case other =>
      throw new IllegalArgumentException(s"""Search state "$other" is unknown""")
  }
  implicit val rw:RW[SearchState] = RW.merge(macroRW[Unknown.type],
    macroRW[Live.type],
    macroRW[BottomQry.type],
    WitnessedQry.rw
  )
}
sealed trait SearchState
case object Unknown extends SearchState{
  override def toString:String = "unknown"
}
case object Live extends SearchState{
  override def toString:String = "live"
}
case object BottomQry extends SearchState{
  override def toString:String = "refuted"
}
case class WitnessedQry(explanation: Option[WitnessExplanation]) extends SearchState{
  override def toString:String = "witnessed"
}
case object WitnessedQry{
  implicit val rw:RW[WitnessedQry] = macroRW
}

sealed case class Qry(state:State, loc:Loc, searchState:SearchState) {
  override def toString:String = loc.toString + "  " + state.toString
  def isLive:Boolean = searchState match {
    case Unknown => ???
    case Live => true
    case BottomQry => false
    case WitnessedQry(_) => true
  }
  def isWitnessed:Boolean = searchState match {
    case Unknown => ???
    case Live => false
    case BottomQry => false
    case WitnessedQry(_) => true
  }
}