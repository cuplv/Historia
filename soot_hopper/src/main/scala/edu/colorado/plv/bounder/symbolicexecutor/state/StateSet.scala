package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, IRWrapper, InternalMethodInvoke, InternalMethodReturn, InvokeCmd, Loc, SpecialInvoke, StaticInvoke, VirtualInvoke}

sealed trait StateRefinementEdge {
  def contains(other: StateRefinementEdge): Boolean

}



case class StateSet(edges: Map[String, StateSet], states: Set[IPathNode])

sealed trait PVMap
case class OnePVMap(tgt:PureVar) extends PVMap
case class TwoPVMap(src:PureVar,tgt:PureVar) extends PVMap

object StateSet {
  def init: StateSet = StateSet(Map(),Set())
  private def localEdgeFromFrame(sf:CallStackFrame,
                                           state:State,
                                           stackDepth:Int):Seq[String] =
    sf.locals.toList.map{
      case(StackVar(vName),_) => s"#${vName}_$stackDepth"
    }
  private def localEdgeFromState(state:State): Seq[String] = {
    val unsortedLocals = state.callStack.zipWithIndex.flatMap{
      case (sf@CallStackFrame(_, _, _), stackDepth) => localEdgeFromFrame(sf,state,stackDepth)
    }
    unsortedLocals.sorted
  }
  private def heapEdgesFromState(state:State):Seq[String] = {
    val unsortedHeap = state.heapConstraints.toSeq.map{
      case (FieldPtEdge(_,name),_) => s"##$name"
    }
    unsortedHeap.sorted
  }
  def add(pathNode:IPathNode, stateSet: StateSet):StateSet = {
    def iEdges(edges: Seq[String], state:IPathNode,current: StateSet):StateSet = edges match{
      case edge::t if current.edges.contains(edge)=>
        val nextS = iEdges(t,state,current.edges(edge))
        current.copy(edges = current.edges + (edge -> nextS))
      case edge::t =>
        val nextS = iEdges(t,state,init)
        current.copy(edges = current.edges + (edge -> nextS))
      case Nil =>
        current.copy(states = current.states + state)//
    }
    val local = localEdgeFromState(pathNode.qry.state)
    val heap = heapEdgesFromState(pathNode.qry.state)
    iEdges(local ++ heap,pathNode, stateSet)
  }
  private def dbgAllSubs(pathNode:IPathNode, stateSet:StateSet, canSubsume: (State,State)=> Boolean):(Option[IPathNode], Int) = {
    var subsCount:Int = 0
    def iDbg(pathNode:IPathNode, stateSet:StateSet, canSubsume: (State,State)=> Boolean):Option[IPathNode] = {
      val res = stateSet.states.find { subsuming =>
        subsCount = subsCount + 1
        canSubsume(subsuming.qry.state, pathNode.qry.state)
      }
      object Subs {
        def unapply(s: StateSet): Option[IPathNode] = {
          iDbg(pathNode, s, canSubsume)
        }
      }
      if (res.isDefined)
        res
      else
        stateSet.edges.collectFirst { case (_, Subs(s)) => s }
    }
    (iDbg(pathNode, stateSet, canSubsume), subsCount)
  }
  def findSubsuming(pathNode:IPathNode, stateSet:StateSet, canSubsume: (State,State)=> Boolean):Option[IPathNode] = {
    val local = localEdgeFromState(pathNode.qry.state)
    val heap = heapEdgesFromState(pathNode.qry.state)
    var fastCount:Int = 0
    def iFind(edges: List[String], pathNode:IPathNode, current:StateSet):Option[IPathNode] = {
      val currentCanSubs = current.states.find{ subsuming =>
        fastCount = fastCount + 1
        canSubsume(subsuming.qry.state, pathNode.qry.state)
      }
      if(currentCanSubs.isDefined)
        return currentCanSubs
      edges match{
        case h::t if current.edges.contains(h) =>
          val withEdge = iFind(t,pathNode, current.edges(h))
          if ( withEdge.isDefined)
             withEdge
          else {
            // Check with current node again but drop all states since subsumption was already checked,
            // we only care about out edges
            iFind(t,pathNode,current.copy(states = Set()))
          }
        case _::t =>
          iFind(t,pathNode,current.copy(states = Set()))
        case Nil => None // Any further edges would mean that the subsuming state has edges the subsumee doesn't
      }
    }

    val out = iFind((local ++ heap).toList, pathNode, stateSet)
//    val (dbgOut,dbgCount) = dbgAllSubs(pathNode, stateSet, canSubsume)
//    println(s"baseCount: $dbgCount  fastCount: $fastCount")
//    if(dbgOut != out){
//      println("ERROR!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")
//    }

    out
  }
}

sealed trait SubsumableLocation
case class CodeLocation(loc:Loc)extends SubsumableLocation
case object FrameworkLocation extends SubsumableLocation
object SwapLoc {
  def unapply[M,C](loc: Loc)(implicit w:IRWrapper[M,C]): Option[SubsumableLocation] = loc match {
    case _: CallbackMethodInvoke => Some(FrameworkLocation)
    case _: CallbackMethodReturn => None
    case AppLoc(_,_,false) => None
    case a@AppLoc(_,_,true) if w.isLoopHead(a) => Some(CodeLocation(a))
    case _: CallinMethodInvoke => None // message locations don't remember program counter so subsumption is unsound
    case _: CallinMethodReturn => None
    case _: GroupedCallinMethodInvoke => None
    case _: GroupedCallinMethodReturn => None
    case _: InternalMethodInvoke => None
    case _: InternalMethodReturn => None
    case a@AppLoc(_,_,true) =>
      w.cmdAtLocation(a) match {
        case InvokeCmd(_, _) => Some(CodeLocation(a))
        case AssignCmd(_, VirtualInvoke(_,_,_,_),_) => Some(CodeLocation(a))
        case AssignCmd(_, SpecialInvoke(_,_,_,_),_) => Some(CodeLocation(a))
        case AssignCmd(_, StaticInvoke(_,_,_),_) => Some(CodeLocation(a))
        case _ => None
      }
  }
  def apply[M,C](loc:Loc)(implicit w:IRWrapper[M,C]):Option[SubsumableLocation] =
    unapply(loc)
}