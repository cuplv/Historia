package edu.colorado.plv.bounder.symbolicexecutor.state

import edu.colorado.plv.bounder.ir.{AppLoc, AssignCmd, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, IRWrapper, InternalMethodInvoke, InternalMethodReturn, Invoke, InvokeCmd, Loc, NopCmd, ReturnCmd, SkippedInternalMethodInvoke, SkippedInternalMethodReturn, SwitchCmd, ThrowCmd, VirtualInvoke}
import edu.colorado.plv.bounder.symbolicexecutor.ControlFlowResolver


sealed trait PVMap
case class OnePVMap(tgt:PureVar) extends PVMap
case class TwoPVMap(src:PureVar,tgt:PureVar) extends PVMap

sealed trait StateSetNode{
  def allStates:Set[IPathNode]
}
object StateSet {
  def emptyStateSet: StateSetNode = iEmptyStateSet
  private def iEmptyStateSet: IStateSetNode = IStateSetNode(Map(),Set())

  private sealed trait Edge{
    def subsetOf(other:Edge):Boolean
  }
  private case class HeapEdge(v:HeapPtEdge) extends Edge{
    def subsetOf(other:Edge):Boolean = (v,other) match {
      case (FieldPtEdge(_,fn1), HeapEdge(FieldPtEdge(_,fn2))) => fn1 == fn2
      case (StaticPtEdge(clazz1, fn1), HeapEdge(StaticPtEdge(clazz2, fn2))) => clazz1 == clazz2 && fn1 == fn2
      case (ArrayPtEdge(_,_),HeapEdge(ArrayPtEdge(_,_))) => true
      case (_,_) => false
    }
  }
  private case class StackEdge(v:CallStackFrame) extends Edge{
    def subsetOf(other:Edge):Boolean = other match {
      case HeapEdge(_) => false
      case StackEdge(CallStackFrame(exitLoc, retLoc, locals)) => {
        val exitComp = exitLoc == v.exitLoc
        val retLocComp = (v.retLoc,retLoc) match{
          case (Some(_), None) => true // no return location defined is more abstract than some defined location
          case (None,Some(_)) => false
          case (vr,or) => vr == or //Some or none must match (including contained value)
        }
        val localsComp = locals.forall{ case (stackVar, _) => v.locals.contains(stackVar)}
        exitComp && retLocComp && localsComp
      }
    }
  }

  private case class IStateSetNode(edges: Map[Edge, IStateSetNode], states: Set[IPathNode]) extends StateSetNode{
    def allStates: Set[IPathNode] = states.union(edges.flatMap{ case(_,v) => v.allStates}.toSet)
  }

  private def edgeComparable(e1:Edge, e2:Edge):Boolean = e1.getClass == e2.getClass


  private def edgesFromState(state:State):Seq[Edge] = {
    //Heap edges
    val heapEdge:Seq[Edge] = state.sf.heapConstraints.keySet.toSeq
      .sortBy(_.ordBy)
      .map{HeapEdge}
    //stack edges
    val stackEdge:Seq[Edge] = state.sf.callStack.map(e => StackEdge(e))

    heapEdge ++ stackEdge
  }

  def add(pathNode:IPathNode, stateSet: StateSetNode):StateSetNode = {
    def iEdges(edges: Seq[Edge], state:IPathNode,current: IStateSetNode):IStateSetNode = edges match{
      case edge::t if current.edges.contains(edge)=>
        val nextS = iEdges(t,state,current.edges(edge))
        current.copy(edges = current.edges + (edge -> nextS))
      case edge::t =>
        val nextS = iEdges(t, state, iEmptyStateSet)
        current.copy(edges = current.edges + (edge -> nextS))
      case Nil =>
        //TODO: ===== add separate method for pruning states
//        val currentDropSubs = current.states.filter(sOld => !canSubsume(state.qry.getState.get,sOld.qry.getState.get) )
        current.copy(states = current.states + state)//
//        current.copy(states = current.states + state) //TODO: ====== check if this improves things
    }
    val edges = edgesFromState(pathNode.qry.state)
    iEdges(edges,pathNode, stateSet.asInstanceOf[IStateSetNode])
  }
  def dbgAllSubs(pathNode:IPathNode,
                         stateSet:StateSetNode, canSubsume: (State,State)=> Boolean):(Option[IPathNode], Int) = {
    var subsCount:Int = 0 //l
    def iDbg(pathNode:IPathNode, stateSet:IStateSetNode, canSubsume: (State,State)=> Boolean):Option[IPathNode] = {
      val res = stateSet.states.find { subsuming =>
        subsCount = subsCount + 1
        canSubsume(subsuming.qry.state, pathNode.qry.state)
      }
      object Subs {
        def unapply(s: IStateSetNode): Option[IPathNode] = {
          iDbg(pathNode, s, canSubsume)
        }
      }
      if (res.isDefined)
        res
      else
        stateSet.edges.collectFirst { case (_, Subs(s)) => s }
    }
    (iDbg(pathNode, stateSet.asInstanceOf[IStateSetNode], canSubsume), subsCount)
  }

  //TODO: This seems to be broken {foo} should be subset of {foo, bar} but the sorting thing breaks because it turns into [bar, foo]
  def getPossibleSubsuming(pathNode: IPathNode, stateSet: StateSetNode):Set[IPathNode] = {
//    val local = localEdgeFromState(pathNode.qry.getState.get)
//    val heap = heapEdgesFromState(pathNode.qry.getState.get)
    def iFind(edges: Seq[Edge], pathNode:IPathNode, current:IStateSetNode):Set[IPathNode] = {
      val currentOut: Set[IPathNode] = current.states
      val nextOut: Set[IPathNode] = edges match{
        case h::t =>
          val relevantEdges = current.edges.keySet.filter(e => !edgeComparable(e,h) || e.subsetOf(h))
          relevantEdges.flatMap(e => iFind(t,pathNode, current.edges(e)))
        case Nil => Set.empty // Any further edges would mean that the subsuming state has edges the subsumee doesn't
      }
      currentOut.union(nextOut)
    }

    val edges = edgesFromState(pathNode.qry.state)
    iFind(edges, pathNode, stateSet.asInstanceOf[IStateSetNode])
  }

  def filterSubsumedBy(pathNode: IPathNode, stateSet: StateSetNode, canSubsume: (State,State)=>Boolean):StateSetNode = {
    ??? //TODO: === remove states subsumed by recently added state
  }

}

sealed trait SubsumableLocation
case class CodeLocation(loc:Loc)extends SubsumableLocation
case object FrameworkLocation extends SubsumableLocation
object SwapLoc {
  def unapply[M,C](pathNode:IPathNode)(implicit r:ControlFlowResolver[M,C]): Option[SubsumableLocation] = pathNode.qry.loc match {
    case _: CallbackMethodInvoke =>
      Some(FrameworkLocation)
    case _: CallbackMethodReturn => None
    case a@AppLoc(_,_,true) if r.getWrapper.isLoopHead(a) => Some(CodeLocation(a))
    case a@AppLoc(_,_,true) => {
      r.getWrapper.cmdAtLocation(a) match {
        case InvokeCmd(_, _) =>
          codeLocationIfRecurse(pathNode, r, a)
          //None
        case AssignCmd(_,i:Invoke, _) =>
          codeLocationIfRecurse(pathNode, r, a)
          //None
        case ReturnCmd(returnVar, loc) =>
          codeLocationIfRecurse(pathNode, r, loc)
        case AssignCmd(target, source, loc) => None
        case NopCmd(loc) => None
        case SwitchCmd(key, targets, loc) => None
        case ThrowCmd(loc) => None
        case _ => None //TODO: Does any of this make a difference in runtime?
      }
    }
    case AppLoc(_,_,false) => None
    case _: CallinMethodInvoke => None // message locations don't remember program counter so subsumption is unsound
    case _: CallinMethodReturn => None
    case _: GroupedCallinMethodInvoke => None
    case _: GroupedCallinMethodReturn => None
    case _: InternalMethodInvoke => None
    case _: InternalMethodReturn => None
    case _: SkippedInternalMethodReturn => None
    case _: SkippedInternalMethodInvoke => None
  }

  private def codeLocationIfRecurse[C, M](pathNode: IPathNode, r: ControlFlowResolver[M, C], a: AppLoc) = {
    val method = a.method
    if (r.mayRecurse(method)) {
      Some(CodeLocation(a))
    } else None
  }
}