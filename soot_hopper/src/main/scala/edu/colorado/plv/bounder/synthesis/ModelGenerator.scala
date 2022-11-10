package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.ir.{Loc, TMessage, Trace}
import edu.colorado.plv.bounder.lifestate.LifeState.LSAtom
import edu.colorado.plv.bounder.lifestate.{SpecAssignment, SpecSpace}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.MustExecutor
import edu.colorado.plv.bounder.symbolicexecutor.state.{IPathNode, OutputMode, PureVar, State, StateFormula}

import scala.annotation.tailrec
import scala.collection.mutable


abstract class ModelGenerator(cha:ClassHierarchyConstraints) {
  //this: Z3ModelGenerator =>
  type PathNode = (LSAtom,State, Loc)
  sealed trait Classification
  case object Reachable extends Classification
  case object Unreachable extends Classification
  case object Unset extends Classification

  implicit val stateSolver = new Z3StateSolver(cha, timeout = 30000, randomSeed = 3578,
    defaultOnSubsumptionTimeout = _=>false, pushSatCheck = true)
  /**
   * A normalized path unifies the logic variables between abstract states at execution locations.
   *
   * @param leaves
   * @param target
   * @param dag
   * @param uid
   * @param classification
   */
  case class NormalizedPath(leaves:Set[PathNode], target:PathNode, dag:Map[PathNode,PathNode], uid:Int,
                            classification:Classification){

    def mkTraces:Set[Trace] = {
      //TODO: implement concrete executor here
      def iMkTraces(node:PathNode, underState:StateFormula):Set[Trace] = {

        println(leaves) //TODO ===
        ???

      }

      leaves.flatMap(n =>iMkTraces(n,StateFormula.initialState))
    }

    def name:String = {
      assert(uid >= 0, "UID must be greater than zero to be named")
      classification match {
        case Reachable => s"Reachable_$uid"
        case Unreachable => s"Unreachable_$uid"
        case Unset => throw new IllegalArgumentException("Classification must be set to be named")
      }
    }


    lazy val allNodes = findall(_ => true)
    private lazy val nodeToUid:Map[PathNode,Int] = allNodes.zipWithIndex.map{
      case (node, i) => node->i
    }.toMap
    def nodeUID(node:PathNode):Int = nodeToUid(node)

    lazy val allPv:Set[PureVar] = allNodes.flatMap{
      case (atom, state,_) => atom.lsVar ++ state.pureVars()
    }

    def succ(node:PathNode):Set[PathNode] = {
      dag.get(node).toSet
    }

    def pred(node:PathNode):Set[PathNode] = {
      //TODO construct reverse
      ???
    }

    def findall(toFind:PathNode => Boolean):Set[PathNode] = {
      @tailrec
      def iFind(worklist:List[PathNode], found:Set[PathNode]):Set[PathNode] = worklist match {
        case h::t =>
          val newList:List[PathNode] = (succ(h).toList) ++ t
          val toAdd = if(toFind(h)) Set(h) else Set.empty
          iFind( newList, found ++ toAdd)
        case Nil => found
      }
      iFind(leaves.toList, Set())
    }
  }

  /**
   * Make one normalized path for each target query.
   * @param leaves over-approximate earliest queries produced by `AbstractInterpreter`
   * @param outputMode storage technique for paths
   * @return set where each normalized path has a unique query target
   */
  def makePaths(leaves:Set[IPathNode])(implicit outputMode: OutputMode): Set[NormalizedPath] = {

    //TODO: make path merged in use equiv pvs where they match in the trace, use non-conflicting pv otherwise
    def merge(n1:NormalizedPath, n2:NormalizedPath):NormalizedPath = ???

    def mk(atoms:List[LSAtom],state:State,loc:Loc):NormalizedPath= atoms match {
      case head::next => {
        val headLeaf = (head,state, loc)
        var cLeaf = headLeaf
        var cNext = next
        val dag = new mutable.HashMap[PathNode,PathNode]()
        while(cNext.nonEmpty) {
          val nextNode = (cNext.head, State.topState, loc)
          dag.addOne(cLeaf -> nextNode)
          cNext = cNext.tail
          cLeaf = nextNode
        }
        NormalizedPath(Set(headLeaf), cLeaf, dag.toMap, -1, Unset)
      }
      case Nil => throw new IllegalArgumentException("empty message history")
    }

    def traverse(node:IPathNode):NormalizedPath = {
      val state = node.state
      val hist = state.sf.traceAbstraction.rightOfArrow
      val c = mk(hist,state, node.qry.loc)
      val next = node.succ.map(traverse)
      (c::next).reduce(merge)
    }
    val terminals = leaves.map(traverse)
    terminals.groupBy(a => a.target).map{
      case (_, value) => value.reduce(merge)
    }.toSet
  }

  def makeTraces(leaf:IPathNode, space:SpecSpace)(implicit outputMode: OutputMode): Set[Trace] = {
    def iTracesToN(state:StateFormula, leaf:IPathNode):Set[List[TMessage]] ={
      val nextState = MustExecutor.execute(state, leaf.qry.loc, leaf.state.sf)
      ???
    }
    iTracesToN(StateFormula.initialState, leaf).map(Trace(_))
  }


  /**
   *
   * @param posExamples set of traces representing reachable points (List in reverse execution order)
   * @param negExamples
   * @param rulesFor    learn rules restricting the back messages in this set
   * @return an automata represented by transition tuples (source state, transition symbol, target state)
   */
  def learnRulesFromExamples(target: Set[IPathNode],
                             reachable: Set[IPathNode],
                             space:SpecSpace)(implicit outputMode: OutputMode): Option[SpecAssignment]

}