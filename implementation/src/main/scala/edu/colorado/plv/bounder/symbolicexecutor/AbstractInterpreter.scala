package edu.colorado.plv.bounder.symbolicexecutor

import java.time.Instant
import upickle.default.{macroRW, read, write, ReadWriter => RW}
import edu.colorado.plv.bounder.{BounderUtil, RunConfig}
import edu.colorado.plv.bounder.ir.{AppLoc, CBEnter, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, Goto, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, IRWrapper, InternalMethodInvoke, InternalMethodReturn, InvokeCmd, Loc, MethodLoc, NopCmd, ReturnCmd, SkippedInternalMethodInvoke, SkippedInternalMethodReturn, SwitchCmd, ThrowCmd, VirtualInvoke}
import edu.colorado.plv.bounder.lifestate.LifeState.OAbsMsg
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.solver.EncodingTools.repHeapCells
import edu.colorado.plv.bounder.solver.{EncodingTools, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{BottomQry, CallStackFrame, DBOutputMode, FieldPtEdge, FrameworkLocation, HashableStateFormula, HeapPtEdge, IPathNode, InitialQuery, Live, MemoryOutputMode, NPureVar, NoOutputMode, OrdCount, OutputMode, PathNode, PureExpr, Qry, State, StaticPtEdge, SubsumableLocation, SwapLoc, WitnessedQry}

import java.util.concurrent.atomic.{AtomicBoolean, AtomicInteger}
import scala.collection.parallel.immutable.ParIterable
import scala.annotation.tailrec
import upickle.default._

import scala.collection.concurrent.TrieMap
import scala.collection.mutable
import scala.collection.parallel.CollectionConverters.IterableIsParallelizable
import scala.collection.parallel.ForkJoinTaskSupport
import scala.concurrent.{Await, Future}
import scala.util.{Failure, Success, Using}
import scala.concurrent.ExecutionContext.Implicits.global
import scala.concurrent.duration.Duration

sealed trait CallGraphSource

/**
 * Use only the class hierarchy to create call graph (faster but less precise)
 */
case object CHACallGraph extends CallGraphSource

/**
 * Compute an application only call graph using spark from soot
 */
case object SparkCallGraph extends CallGraphSource

/**
 * Compute an app only call graph independently of soot
 * TODO: not used in a long time, needs work
 */
case object AppOnlyCallGraph extends CallGraphSource

sealed trait SubsumptionMode

/**
 * Encode each possible subsuming state one at a time
 */
case object SubsumptionModeIndividual extends SubsumptionMode

/**
 * Encode all possibly subsuming states at once
 */
case object SubsumptionModeBatch extends SubsumptionMode

/**
 * Run both batch and individual comparing results
 */
case object SubsumptionModeTest extends SubsumptionMode

sealed trait ApproxMode {
  def shouldDropState(state:State):Boolean
  /**
   * Called at loop heads to widen or discard states depending on over or under approx.
   * Widening is applied for over approx.
   * Discard state only considered for under approximations
   * @param existing states at the program location to widen
   * @param newState new state generated by transfer functions
   * @return None if no new state is to be considered, Some(state) if a state is to be added
   */
  def merge[M, C](existing: () => Iterable[IPathNode], newPN: IPathNode,
                           stateSolver: Z3StateSolver)(implicit w:ControlFlowResolver[M,C]): Option[IPathNode]

  /**
   * An over-approximate state may weaken by dropping materialized heap cells or tracking less precise constraints.
   * @return true if it is sound to weaken the abstract state, false if not
   */
  def canWeaken:Boolean
}



object ApproxMode{
  implicit val rw:RW[ApproxMode] = RW.merge(PreciseApproxMode.rw, LimitMaterializationApproxMode.rw)
}

sealed trait DropStatePolicy{
  def shouldDrop(state:State) : Boolean
}
object DropStatePolicy{
  implicit var rw:RW[DropStatePolicy] = RW.merge(LimitMsgCountDropStatePolicy.rw)
}

case class LimitMsgCountDropStatePolicy(count:Int) extends DropStatePolicy{

  def shouldDrop(state:State) : Boolean = {
    val shouldDrop = state.sf.traceAbstraction.rightOfArrow.filter{
        case OAbsMsg(CBEnter, _,_,_) => true
        case _ => false
      }
      .groupBy(_.identitySignature).exists{
      case (_, msgs) => msgs.size > count
    }
    if(shouldDrop) println(s"dropping state : ${state.sf.traceAbstraction.rightOfArrow}")
    shouldDrop
  }
}
object  LimitMsgCountDropStatePolicy{
  implicit val rw:RW[LimitMsgCountDropStatePolicy] = macroRW
}

/**
 * Materialize everything within reason.
 * @param canWeaken  true if its OK for the transfer functions to drop constraints, false if not
 */
case class PreciseApproxMode(canWeaken:Boolean, dropStatePolicy:List[DropStatePolicy] = List()) extends ApproxMode{

  /**
   *
   * @param existing states at the program location to widen
   * @param newState new state generated by transfer functions
   * @return None if no new state is to be considered, Some(state) if a state is to be added
   */
  override def merge[M,C](existing: () => Iterable[IPathNode], newState: IPathNode,
                     stateSolver: Z3StateSolver)(implicit w: ControlFlowResolver[M, C]): Option[IPathNode] =
    Some(newState)

  override def shouldDropState(state: State): Boolean = dropStatePolicy.exists{_.shouldDrop(state)}
}

object PreciseApproxMode {
  implicit val rw:RW[PreciseApproxMode] = macroRW
}


case class LimitMaterializationApproxMode(materializedFieldLimit:Int = 2) extends ApproxMode {

  override def canWeaken:Boolean = true
  override def merge[M,C](existing: () => Iterable[IPathNode], newPN:IPathNode,
                     stateSolver: Z3StateSolver)(implicit w:ControlFlowResolver[M,C]): Option[IPathNode] = {
    newPN match{
      case SwapLoc(_) => //Only widen where back edges exist
        val newState = newPN.state
        assert(newState.isSimplified, "State to merge must be simplified by StateSolver.")
        val collectedFields = newState.sf.heapConstraints.groupBy { c => repHeapCells(c) }
        val toRemove: Set[HeapPtEdge] = collectedFields.flatMap {
          case (_, fields) if fields.size < 2 => Set.empty
          case (_, fields) if fields.head._1.isInstanceOf[FieldPtEdge] =>
              val res = fields.toList.sortBy{
                case (FieldPtEdge(NPureVar(id),_),_) => id
                case _ => throw new IllegalStateException()
              }.map(_._1).drop(materializedFieldLimit)
              res
          case (_,_) => Set.empty
//            val min = fields.foldLeft() {
//              case (acc, (FieldPtEdge(NPureVar(id), _), _)) => if (id < acc) id else acc
//              case (acc, (StaticPtEdge(_, _), _)) => acc // can only have one static edge anyway
//              case (acc, (ArrayPtEdge(_, _), _)) =>
//                ??? // TODO: not sure how to handle this
//            }
//            fields.flatMap {
//              case (f@FieldPtEdge(NPureVar(id), _), _) => if (id == min) None else Some(f)
//              case (f, _) => Some(f)
//            }

        }.toSet
        val newSF = newState.sf
        val rmHeap = newSF.heapConstraints.removedAll(toRemove)
        val prunedStateOpt: Option[State] =
          EncodingTools.reduceStatePureVars(newState.copy(sf = newSF.copy(heapConstraints = rmHeap)).setSimplified())
        assert(prunedStateOpt.isDefined, "Removing a materialized heap cell should not refute state")
        val prunedState = prunedStateOpt.get

        // Drop calls if recursion detected
        val seen = mutable.Set[Loc]()
        val callStackUntil = prunedState.sf.callStack.takeWhile{
          case CallStackFrame(exitLoc, _, _) =>
            val seenYet = seen.contains(exitLoc)
            seen += (exitLoc)
            !seenYet
        }
        //TODO: perhaps check if the callback is needed in the abstract state

        // Note, can just call setSimplified here because dropping stack frames shouldn't affect feasibility
        val trimmedStateOpt =
          EncodingTools.reduceStatePureVars(
            prunedState.copy(sf = prunedState.sf.copy(callStack = callStackUntil)).setSimplified()
          )
        assert(trimmedStateOpt.isDefined, "Dropping calls should not refute state")
        val trimmedState = trimmedStateOpt.get
        //val simp = stateSolver.simplify(prunedState, SpecSpace.top)
        //assert(simp.isDefined, "merge should not cause refutation")
        //simp.map{s => newPN.copyWithNewQry(newPN.qry.copy(state = s))}
        Some(newPN.copyWithNewQry(newPN.qry.copy(state = trimmedState.setSimplified())))
      case _ =>
        Some(newPN)
    }

  }

  override def shouldDropState(state: State): Boolean = false
}

object LimitMaterializationApproxMode {
  implicit val rw:RW[LimitMaterializationApproxMode] = macroRW
}

/**
 * Configure how z3 behaves for timeouts in various circumstances
 * @param subsumeTryTimeLimit length of list is number of tries, each entry is the time limit for that try.
 * @param excludesInitTimeout how long should we wait for excludes initial check (usually doesn't timeout)
 * @param z3InstanceLimit number of simultaneous z3 instances to run (default is number of processors)
 */
case class Z3TimeoutBehavior(subsumeTryTimeLimit:List[Int] = List(40000, 220000), excludesInitTimeout:Int = 40000,
                             z3InstanceLimit:Int = Runtime.getRuntime.availableProcessors){
  assert(subsumeTryTimeLimit.size > 0, s"Invalid subumeTryTimeLimit: ${subsumeTryTimeLimit}, " +
    s"must have length of at least 1.")
}
object Z3TimeoutBehavior{
  implicit val rw:RW[Z3TimeoutBehavior] = macroRW
}

/**
 * @param stepLimit Number of back steps to take from assertion before timeout (-1 for no limit)
 * @param w  IR representation defined by IRWrapper interface
 * @param specSpace CFTL specifications
 * @param printAAProgress print steps taken
 * @param z3Timeout seconds that z3 can take on a query before timeout
 * @param component restrict analysis to callbacks that match the listed regular expressions
 * @tparam M Method type (IR wrapper)
 * @tparam C Command type (IR wrapper)
 */
case class ExecutorConfig[M,C](stepLimit: Int = -1,
                               w :  IRWrapper[M,C],
                               specSpace:SpecSpace,
                               printAAProgress : Boolean = sys.env.getOrElse("DEBUG","false") == "AbstractInterpreter",
                               z3Timeout : Z3TimeoutBehavior = Z3TimeoutBehavior(),
                               component : Option[Seq[String]] = None,
                               outputMode : OutputMode = MemoryOutputMode,
                               timeLimit:Int = 7200, // Note: connectbot click finish does not seem to go any further with 2h vs 0.5hr
                               subsumptionMode:SubsumptionMode = SubsumptionModeIndividual, //Note: seems to be faster without batch mode subsumption
                               approxMode:ApproxMode =  LimitMaterializationApproxMode(),
                               z3InstanceLimit:Int = -1,
                               z3ShouldRetryOnTimeout:Boolean = true
                               //PreciseApproxMode(true) //default is to allow dropping of constraints and no widen //TODO: === make thresher version that drops things == make under approx version that drops states
                                      ){
  def getAbstractInterpreter =
    new AbstractInterpreter[M, C](this)
}

class LexicalStackThenTopo[M,C](w:IRWrapper[M,C]) extends OrdCount{
  override def delta(current: Qry): Int = current.loc match {
    case _:CallbackMethodInvoke => 1
    case _:CallbackMethodReturn => 1
    case _ => 0
  }
  private def compareLocAtSameStack(l1:Loc, l2:Loc):Int = (l1,l2) match {
    case (AppLoc(m1,l1,isPre1), AppLoc(m2,l2,isPre2)) if m1 == m2 && l1 == l2 =>
      if(isPre1 == isPre2) {
        //            println(s"no ord:   p1: ${p1.qry.loc} p2: ${p2.qry.loc}")
        0
      }
      else if(isPre1)
        -1 // p2 is post line and should go first
      else {
        1 // p1 is post line and should go first
      }
    case (a1@AppLoc(m1,_,_), a2@AppLoc(m2,_,_)) if m1 == m2 =>
      val c1 = w.commandTopologicalOrder(w.cmdAtLocation(a1))
      val c2 = w.commandTopologicalOrder(w.cmdAtLocation(a2))
      c1 - c2 // reversed because topological order increases from beginning of function
    case (entry, AppLoc(_, _, _)) if entry.isEntry.contains(true) => -1
    case (AppLoc(_,_,_), entry) if entry.isEntry.contains(true) => 1
    case (exit, AppLoc(_,_,_)) if exit.isEntry.contains(false) => 1
    case (AppLoc(_,_,_), exit) if exit.isEntry.contains(false) => -1
    case (entry, exit) if exit.isEntry.contains(false) && entry.isEntry.contains(true) => -1
    case (exit, entry) if exit.isEntry.contains(false) && entry.isEntry.contains(true) => 1
    case (msg1,msg2) if msg1 == msg2 => 0
    case (msg1, msg2) if msg1.isEntry.isDefined && msg2.isEntry.isDefined =>
      if(msg1.toString < msg2.toString) 1 else -1
    case (AppLoc(m1,_,_), AppLoc(m2,_,_)) => if(m1.toString < m2.toString) 1 else -1 //TODO: remove toString here for performance
    case (v1,v2) =>
      println(v1)
      println(v2)
      ???
  }
  // return positive if p1 should be first
  // return negative if p2 should be first
  override def compare(p1: IPathNode, p2: IPathNode): Int = {
    if(p1.ordDepth != p2.ordDepth){
      // Prefer smaller number of callbacks
      return p2.ordDepth - p1.ordDepth
    }

    // comparing things from the base of the stack up, reversing for convenience
    val stack1 = ((None,Some(p1.qry.loc)):: p1.state.callStack.map(sf => (Some(sf.exitLoc),sf.retLoc))).reverse
    val stack2 = ((None,Some(p2.qry.loc)):: p2.state.callStack.map(sf => (Some(sf.exitLoc),sf.retLoc))).reverse

    @tailrec
    def iCompare(s1: List[(Option[Loc], Option[Loc])], s2:List[(Option[Loc], Option[Loc])]):Int = (s1,s2) match{
      case (Nil,Nil) =>
        p2.depth - p1.depth
      case (h1::t1, h2::t2) if h1 == h2 => iCompare(t1,t2)
      case (h1::t1, h2::t2) if h1._2.isDefined && h2._2.isDefined=>
        val res = compareLocAtSameStack(h1._2.get, h2._2.get)
        if(res == 0)
          iCompare(t1,t2)
        else res
      case (Nil,_) => -1
      case (_,Nil) => 1
      case (h1 :: t1, h2 :: t2) if h1._1.isDefined && h2._1.isEmpty => 1
      case (h1 :: t1, h2 :: t2) if h1._1.isEmpty && h2._1.isDefined => -1
      case (h1 :: t1, h2 :: t2) if h1._1.isDefined && h2._1.isDefined =>
        val res = compareLocAtSameStack(h1._1.get, h2._1.get)
        if (res == 0)
          iCompare(t1, t2)
        else res
      case (h1::t1, h2::t2) if h1._1 != h2._1 =>
        if(h1._1.toString < h2._1.toString) 1 else -1
    }
    iCompare(stack1,stack2)
  }
}
sealed trait QueryResult
case object QueryFinished extends QueryResult
case class QueryInterrupted(reason:String) extends QueryResult

case class QueryInterruptedException(terminals:Set[IPathNode], reason:String) extends Exception
class AbstractInterpreter[M,C](config: ExecutorConfig[M,C]) {

  def updateSpec(newSpec:SpecSpace):AbstractInterpreter[M,C] = {
    //TODO: be smarter about updating spec so we can use this in synthesis later and avoid recomputing
    config.copy(specSpace = newSpec).getAbstractInterpreter
  }

  def getConfig = config

  implicit val pathMode: OutputMode = config.outputMode
  implicit val w = config.w
  implicit val ord = new LexicalStackThenTopo[M,C](w)
  private val cha = w.getClassHierarchyConstraints

  //private val invarMap = mutable.HashMap[SubsumableLocation, Map[HashableStateFormula,IPathNode]]()



  def getClassHierarchy = cha
  val transfer = new TransferFunctions[M, C](w, config.specSpace, cha, config.approxMode.canWeaken)

  implicit val appCodeResolver = new DefaultAppCodeResolver[M,C](config.w)
  def getAppCodeResolver = appCodeResolver
  implicit val controlFlowResolver =
    new ControlFlowResolver[M,C](config.w,appCodeResolver, cha, config.component.map(_.toList), config)
  def writeIR():Unit = {
    val callbacks = appCodeResolver.getCallbacks
    config.outputMode match {
      case db:DBOutputMode =>
        appCodeResolver.appMethods.foreach{m =>
          db.writeMethod(m,callbacks.contains(m))
          val directCalls = controlFlowResolver.directCallsGraph(m).map{
            case InternalMethodReturn(clazz,name,m) => (name,clazz,false)
            case CallinMethodReturn(sig) => (sig.methodSignature,sig.base,true)
            case _ => throw new IllegalStateException()
          }
          directCalls.foreach{callee => db.writeCallEdge(m.simpleName,m.classType, callee._1,callee._2,callee._3)}
        }
      case _ =>
    }
  }
  // Dump debug info from soot analysis to sqlite
//  writeIR() //TODO: add debug flag to toggle this

  lazy val stateSolver = new Z3StateSolver(cha, config.outputMode match {
    case NoOutputMode => false
    case MemoryOutputMode => true
    case DBOutputMode(dbfile) => true
  },
    timeout = config.z3Timeout)


  case class QueryData(queryId:Int, location:Loc, terminals: Set[IPathNode], runTime:Long, result : QueryResult)

  type InvarMap = Map[SubsumableLocation, Set[IPathNode]]
  var isRunning:Boolean = false
  /**
   * Run the abstract interpretation starting at a syntactic location.
   * @param initialQuery defined syntactic location
   * @param outputMode how much information to store about exploration
   * @param cfg initial run configuration to be recorded in output  //TODO: only works with DBOutputMode
   * @param stopExplorationAt used to limit backwards exploration but keep searching other paths.
   *                          default is to not stop (return false)
   *                          (e.g. to find callbacks requiring non-null fields)
   * @return Query data with info on run
   */
  def run(initialQuery: InitialQuery, outputMode:OutputMode = MemoryOutputMode,
          cfg:RunConfig = RunConfig(), stopExplorationAt : Option[Qry => Boolean] = None) : Set[QueryData] = {
    assert(!isRunning, "Abstract interpreter does not support concurrency.")
    isRunning = true
    //TODO: trying this to see if synthesis random slowness can be resolved
    //TODO: hypothesis: z3 cache gets cluttered run to run
    //stateSolver.resetZ3Caches()
    val qry: Set[Qry] = initialQuery.make(this)
      .map{q => q.copy(state = stateSolver.simplify(q.state.setSimplified(), config.specSpace)
        .getOrElse(throw new IllegalArgumentException(s"Initial state was refuted: ${q.state}")))}
    val output = qry.groupBy(_.loc).map{ case(loc,qs) =>
      val startTime = Instant.now.getEpochSecond
      var id = -1
      try {
        val pathNodes: Set[IPathNode] = qs.map(q => PathNode(q.copy(state = q.state.setSimplified()), Nil, None))
        id = outputMode.initializeQuery(loc,cfg,initialQuery)

        val deadline = if(config.timeLimit > -1) Instant.now.getEpochSecond + config.timeLimit else -1
        val res: Set[IPathNode] = if(stopExplorationAt.isEmpty) {
          executeBackwardConc(pathNodes, config.stepLimit, deadline,
            invarMap = TrieMap[SubsumableLocation, Set[IPathNode]]())
        } else {
          val queue = new GrouperQ
          queue.addAll(pathNodes)
          executeBackward(queue, config.stepLimit, deadline,
          stopExplorationAt = stopExplorationAt.get,
          invarMap = TrieMap[SubsumableLocation, Set[IPathNode]]())
        }

        val interpretedRes = BounderUtil.interpretResult(res, QueryFinished)
        val char = BounderUtil.characterizeMaxPath(res)
        val endTime: Long = Instant.now.getEpochSecond - startTime
        outputMode.writeLiveAtEnd(res, id, interpretedRes.toString,interpretedRes,char,endTime)
        QueryData(id, loc, res,
          endTime, QueryFinished)
      }catch{
        case QueryInterruptedException(terminals, reason) =>
          QueryData(id, loc, terminals, Instant.now.getEpochSecond - startTime, QueryInterrupted(reason))
        case t:Throwable =>
          // print stack trace to stderr and continue
          t.printStackTrace(System.err)
          QueryData(id, loc, Set(), Instant.now.getEpochSecond - startTime, QueryInterrupted(t.getClass.toString))
      }
    }.toSet
    isRunning = false
    output
  }

  private def stopAtCB(qry:Qry):Boolean = qry.loc match {
    case _:CallbackMethodReturn => true
    case _ => false
  }

  @tailrec
  final def executeBackwardConc(qrySet: Set[IPathNode], limit: Int, deadline: Long,
                                refutedSubsumedOrWitnessed: Set[IPathNode] = Set(),
                                invarMap: TrieMap[SubsumableLocation, Set[IPathNode]]
                               ): Set[IPathNode] = {
    if (qrySet.isEmpty) {
      refutedSubsumedOrWitnessed
    } else {

//      if (config.printAAProgress) {
//        println(s"executeBackwardConc qry set size: ${qrySet.size}")
//        qrySet.foreach { (current: IPathNode) =>
//          println("Framework location query")
//          println(s"    State: ${current.qry.state}")
//          println(s"    Loc  : ${current.qry.loc}")
//          println(s"    depth: ${current.depth}")
//          println(s"    size of worklist: ${qrySet.size}")
//          println(s"    ord depth: ${current.ordDepth}")
//        }
//      }

      def reduceTup(v1: (Set[QueryInterruptedException], Set[IPathNode]),
                    v2: (Set[QueryInterruptedException], Set[IPathNode])):
      (Set[QueryInterruptedException], Set[IPathNode]) = {
        val exn = v1._1 ++ v2._1
        // don't bother joining invar map if exn occurred
        //val joinedInvarMap: InvarMap = if (exn.nonEmpty) Map.empty else joinInvarMap(v1._3, v2._3)
        val combinedSet = v1._2 ++ v2._2
        val qryGroups = combinedSet.groupBy(n => (n.qry.loc, n.qry.state.sf.makeHashable(config.specSpace)))
        val merged = qryGroups.map{case (_,nodes) =>
          val rep = nodes.head
          nodes.tail.foreach{n => n.setSubsumed(Set(rep))}
          rep
        }.toSet
        (exn, merged)
      }

      val isExn = new AtomicBoolean(false) // Cancel parallel ops on timeout
      val qrySetSorted = qrySet.toList
        .sortBy(n => n.state.sf.heapConstraints.map(EncodingTools.repHeapCells).size)

//      val mutInvarMap = TrieMap[SubsumableLocation, Set[IPathNode]]()
//      mutInvarMap.addAll(invarMap)

      def processNode(qry:IPathNode) = {
        val queue = new GrouperQ
        queue.addAll(Set(qry))
        try {
          if (!isExn.get()) {
            val live = executeBackward(queue, limit, deadline, Set.empty, stopAtCB, invarMap)
            (Set[QueryInterruptedException](), live)
          } else {
            (Set[QueryInterruptedException](), Set[IPathNode]())
          }
        } catch {
          case e: QueryInterruptedException =>
            isExn.set(true)
            val exn: Set[QueryInterruptedException] = Set(e)
            (exn, e.terminals)
        }
      }
      val futureCount = new AtomicInteger(qrySet.size)
      val futures: Seq[Future[(Set[QueryInterruptedException], Set[IPathNode])]] = qrySetSorted.map{qry =>
        Future{
          if (config.printAAProgress) {
            println(s"remaining tasks: ${futureCount.decrementAndGet()} / ${qrySet.size}")
            println(s"    ord depth: ${qry.ordDepth}")
            println(s"    State: ${qry.state}")
            println(s"    Loc  : ${qry.qry.loc}")
            println(s"    Method  : ${qry.qry.loc.containingMethod}")
          }
          processNode(qry)
        }
      }
      val (exn,newNodes) =
        Await.result(futures.reduce{(f1:Future[(Set[QueryInterruptedException], Set[IPathNode])],
                      f2:Future[(Set[QueryInterruptedException], Set[IPathNode])]) =>
          for{
            r1 <-f1
            r2 <-f2
          }yield {
            reduceTup(r1,r2)
          }
        }, Duration.Inf)

      //      val (exn, newNodes) = qrySetPar.map { case (qry,ind) =>
//        processNode(qry)
//      }.reduce(reduceTup)

      val noPred = mutable.Set[IPathNode]()
      if (exn.nonEmpty) {
        val extraTerm = exn.flatMap { e => e.terminals }
        refutedSubsumedOrWitnessed ++ extraTerm ++ newNodes
      } else if (newNodes.exists { n => n.qry.isWitnessed }) {
        refutedSubsumedOrWitnessed ++ newNodes
      } else {

        val nodes = newNodes.groupBy { n =>
          !n.qry.searchState.isInstanceOf[WitnessedQry] && n.subsumed.isEmpty && n.qry.searchState == Live
        }

        val liveNodes = nodes.getOrElse(true, Set.empty).flatMap { p2 =>
          try {
            val res = executeStep(p2.qry).map(q => PathNode(q, List(p2), None))
            if (res.isEmpty)
              noPred.addOne(p2)
            res
          } catch {
            case ze: Throwable =>
              // Get sequence trace to error when it occurs
              p2.setError(ze)
              ze.printStackTrace()
              throw QueryInterruptedException(refutedSubsumedOrWitnessed + p2, ze.getMessage)
          }
        }
        val deadNodes = if (config.outputMode == MemoryOutputMode) nodes.getOrElse(false, Set.empty) else Set.empty
        val nxt = refutedSubsumedOrWitnessed ++ deadNodes

        //val noPredDead = noPred.map{n => n.}

        executeBackwardConc(liveNodes, limit, deadline,
          nxt, invarMap)
      }
    }
  }

  def joinInvarMap(invarMap1:InvarMap, invarMap2:InvarMap)(implicit forkJoinPool: ForkJoinTaskSupport):InvarMap = {
    val allLoc: Set[SubsumableLocation] = invarMap1.keySet ++ invarMap2.keySet
    allLoc.map{loc =>
      val m1 = invarMap1.getOrElse(loc, Set.empty)
      val m2 = invarMap2.getOrElse(loc, Set.empty)
      (loc -> joinNodes(m1, m2))
    }.toMap
  }
  def joinNodes(nodes1:Set[IPathNode], nodes2:Set[IPathNode])
               (implicit forkJoinPool: ForkJoinTaskSupport): Set[IPathNode] = {
    val nodes1Par = nodes1.par
    nodes1Par.tasksupport = forkJoinPool
    val nodes1NonSubs =
      nodes1Par.filter{n => !nodes2.exists{n2 => stateSolver.canSubsume(n2.state, n.state, config.specSpace)}}
    val nodes2Par = nodes2.par
    nodes2Par.tasksupport = forkJoinPool
    val nodes2NonSubs =
      nodes2Par.filter{n => !nodes1NonSubs.exists{n2 => stateSolver.canSubsume(n.state, n2.state, config.specSpace)}}
    val res = (nodes1NonSubs.toSet ++ nodes2NonSubs.toSet).seq
    res
  }

  private var subsFastCount = 0
  def isSubsumed(pathNode:IPathNode, checkTimeout: ()=>Unit,
                 invarMap: scala.collection.concurrent.TrieMap[SubsumableLocation, Set[IPathNode]]):Set[IPathNode] =
    pathNode match{
    case SwapLoc(loc) if pathNode.qry.isInstanceOf[Qry] && invarMap.contains(loc) => {
      //val hashableState = pathNode.state.sf.makeHashable(config.specSpace)
      val nodes = invarMap(loc)
      val states = nodes.map(_.state)
      config.subsumptionMode match {
        case SubsumptionModeIndividual =>
          val thisNodeHashable = pathNode.state.sf.makeHashable(config.specSpace)
          val subsFast = nodes.find{n => n.qry.state.sf.makeHashable(config.specSpace) == thisNodeHashable}
          if(subsFast.isDefined){
            subsFastCount += 1
//            println(s"subs fast: $subsFastCount")
            subsFast.toSet
          }else {
            nodes.find(p => {
              checkTimeout()
              stateSolver.canSubsume(p.state, pathNode.state, config.specSpace)
            }).toSet
          }
        case SubsumptionModeBatch =>
          if (stateSolver.canSubsumeSet(states.toSet, pathNode.state, config.specSpace))
            nodes.toSet else Set[IPathNode]()
        case SubsumptionModeTest => {
          val singleResult = nodes.find(p => stateSolver.canSubsume(p.state, pathNode.state, config.specSpace)).toSet
          val batchResult = stateSolver.canSubsumeSet(states.toSet, pathNode.state, config.specSpace)
          if (singleResult.nonEmpty != batchResult) {
            //println(s"current state:\n    ${pathNode.state}")
            //println("subsuming states:")
            //states.foreach(s => println(s"    ${s.toString}"))
            //val batchResult2 = stateSolver.canSubsumeSet(states.toSet, pathNode.state, config.specSpace)
            //println()
          }
          singleResult
        }
      }
    }
    case _ => Set.empty
  }

  private def equivStates(s1:State, s2:State):Boolean = {
//    stateSolver.canSubsume(s1,s2) && stateSolver.canSubsume(s1,s2)
    s1.callStack == s2.callStack &&
      s1.heapConstraints == s2.heapConstraints &&
      s1.pureFormula == s2.pureFormula &&
      s1.traceAbstraction == s2.traceAbstraction
  }
  sealed trait GroupType
  case class IfGroup(loc:AppLoc) extends GroupType
  case class InvokeGroup(loc:Option[Loc]) extends GroupType

  private def nodeGroup(pn:IPathNode):Option[(GroupType, List[(Loc, Option[Loc])], Int)] = {
    val stack = pn.state.callStack
    val groupStack = stack.map(sf => (sf.exitLoc, sf.retLoc))
    lazy val retLoc = InvokeGroup(stack.head.retLoc)
    pn.qry.loc match {
      case l@AppLoc(_,_,false) =>
        val cmd = w.cmdAtLocation(l)
        cmd match{
          case Goto(_,_,_) => Some((IfGroup(l),groupStack,pn.ordDepth))
          case _ => None
        }
      case _:InternalMethodInvoke =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case _:CallinMethodInvoke =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case _:GroupedCallinMethodInvoke =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case _:SkippedInternalMethodInvoke =>
        Some((retLoc,groupStack.tail,pn.ordDepth))
      case _ => None
    }
  }
  class GrouperQ {
    val qrySet = new mutable.PriorityQueue[IPathNode]()
    val groupedQrySet = new mutable.PriorityQueue[IPathNode]()
    def isEmpty:Boolean = qrySet.isEmpty && groupedQrySet.isEmpty
    def size():Int = qrySet.size + groupedQrySet.size
    def toSet:Set[IPathNode] = qrySet.toSet ++ groupedQrySet.toSet
    def addAll(pathNodes:Set[IPathNode]):Unit =
      qrySet.addAll(pathNodes)
    private def group(qryList: List[IPathNode]): List[IPathNode] = {
      // Group states by next command to process, stack (excluding locals), and trace length
      val groups: Map[Option[(GroupType, List[(Loc, Option[Loc])], Int)], List[IPathNode]] = qryList.groupBy(nodeGroup)
      groups.flatMap {
        case (None, v) => v
        case (Some(group), v) =>
          val nodeSet = v.toSet
          val groupedNodes: Set[IPathNode] = nodeSet.foldLeft(Set[IPathNode]()) { case (acc, pathNode) =>
            acc.find(otherPathNode => equivStates(otherPathNode.qry.state, pathNode.qry.state)) match {
              case Some(other) =>
                (acc - other) + other.mergeEquiv(pathNode)
              case None => acc + pathNode
            }
          }
          val groupedWithAlt: Set[IPathNode] = groupedNodes.map { n =>
            val otherNodes = nodeSet - n
            otherNodes.foldLeft(n) { case (acc, v) => acc.addAlternate(v) }
          }
          groupedWithAlt
      }.toList
    }
    def nextWithGrouping():IPathNode = {
      if(groupedQrySet.nonEmpty){
        groupedQrySet.dequeue()
      }else {
        val next = qrySet.dequeue()
        val currentGroup = nodeGroup(next)
        if (currentGroup.isDefined) {
          val toGroup = mutable.ListBuffer[IPathNode]()
          toGroup += next
          while (qrySet.nonEmpty && nodeGroup(qrySet.head) == currentGroup) {
            toGroup += qrySet.dequeue()
          }
          val grouped = group(toGroup.toList)
          groupedQrySet.addAll(grouped)
          groupedQrySet.dequeue()
        } else {
          next
        }
      }
    }
  }


  def checkDeadline(deadline:Long, qrySet:GrouperQ, refutedSubsumedOrWitnessed: Set[IPathNode]):Unit = {
    val now = Instant.now.getEpochSecond
    if(deadline > -1 && now > deadline){
      throw QueryInterruptedException(qrySet.toSet ++ refutedSubsumedOrWitnessed, "timeout")
    }
  }
  /**
   *
   * @param qrySet Work list of locations and states to process
   * @param limit Step limit to terminate at (set to -1 for no limit)
   * @param deadline unix time to terminate if verification not complete (-1 for no limit)
   * @param refutedSubsumedOrWitnessed Terminal nodes
   * @param visited Map of visited states StackSize -> Location -> Set[State]
   * @return
   */
  @tailrec
  final def executeBackward(qrySet: GrouperQ, limit:Int, deadline:Long,
                            refutedSubsumedOrWitnessed: Set[IPathNode] = Set(),
                            stopExplorationAt:Qry => Boolean,
                            invarMap:scala.collection.concurrent.TrieMap[SubsumableLocation, Set[IPathNode]]
                           ):Set[IPathNode] = {
    checkDeadline(deadline,qrySet, refutedSubsumedOrWitnessed)
    if(qrySet.isEmpty){
      return refutedSubsumedOrWitnessed
    }

    val current: IPathNode = qrySet.nextWithGrouping()

//    if(config.printAAProgress) {
//      current match {
//        case SwapLoc(FrameworkLocation) =>
//          println("Framework location query")
//          println(s"    State: ${current.qry.state}")
//          println(s"    Loc  : ${current.qry.loc}")
//          println(s"    depth: ${current.depth}")
//          println(s"    size of worklist: ${qrySet.size}")
//          println(s"    ord depth: ${current.ordDepth}")
//        case _ =>
//      }
//    }
    current match {
      case p@PathNode(Qry(_,_,Live), true) =>
        // current node is subsumed
        executeBackward(qrySet, limit, deadline, refutedSubsumedOrWitnessed + p, stopExplorationAt, invarMap)
      case p@PathNode(Qry(_,_,BottomQry), _) =>
        // current node is refuted
        val newRef = if(config.outputMode != NoOutputMode)
          refutedSubsumedOrWitnessed + p
        else
          refutedSubsumedOrWitnessed
        executeBackward(qrySet, limit, deadline, newRef, stopExplorationAt, invarMap)
      case p@PathNode(Qry(_,_,WitnessedQry(_)), _) =>
        // current node is witnessed
        refutedSubsumedOrWitnessed.union(qrySet.toSet) + p
      case p: IPathNode if limit > 0 && p.depth > limit =>
        // max steps reached
        refutedSubsumedOrWitnessed.union(qrySet.toSet) + p
      case pLive@PathNode(qry@Qry(_,_,Live), false) =>

        // live path node
        val subsuming =
            isSubsumed(pLive, ()=> checkDeadline(deadline, qrySet,refutedSubsumedOrWitnessed), invarMap)

        subsuming match {
          case v if v.nonEmpty =>
            // Path node discovered to be subsumed
            val newRef = if (config.outputMode != NoOutputMode)
              refutedSubsumedOrWitnessed + pLive.setSubsumed(v)
            else
              refutedSubsumedOrWitnessed
            executeBackward(qrySet, limit, deadline, newRef, stopExplorationAt, invarMap)
          case v if v.isEmpty =>
            // widen if necessary
            config.approxMode.merge(() => ???, pLive, stateSolver) match {
              case Some(p2) =>
                // Add to invariant map if invariant location is tracked
                p2 match {
                  case SwapLoc(v) => {
                    val nodeSetAtLoc: Set[IPathNode] = invarMap.getOrElse(v, Set.empty)
                    // remove all states that may be subsumed by new state:
                    val filtNodeSet =
                      nodeSetAtLoc.par.filter{n => !stateSolver.canSubsume(p2.state, n.state, config.specSpace)}
                        .seq.toSet

                    if(config.printAAProgress) {
                      //println(s"loc: ${v}\n total at loc: ${nodeSetAtLoc.size} \n filteredAtLoc: ${filtNodeSet.size}")
                    }
                    assert(p2.state.isSimplified, "State must be simplified before adding to invariant map.")
                    invarMap.addOne(v -> (filtNodeSet +  p2))
                  }
                  case _ =>
                }
                if(stopExplorationAt(p2.qry)){
                  executeBackward(qrySet, limit, deadline, refutedSubsumedOrWitnessed + p2, stopExplorationAt, invarMap)
                }else {
                  val nextQryPreFilt = try {
                    executeStep(p2.qry).map(q => PathNode(q, List(p2), None))
                  } catch {
                    case ze: Throwable =>
                      // Get sequence trace to error when it occurs
                      current.setError(ze)
                      ze.printStackTrace()
                      throw QueryInterruptedException(refutedSubsumedOrWitnessed + p2, ze.getMessage)
                  }
                  val nextQry = nextQryPreFilt.filter{qry => !config.approxMode.shouldDropState(qry.state)}
                  qrySet.addAll(nextQry)
                  val addIfPredEmpty = if (nextQry.isEmpty && config.outputMode != NoOutputMode)
                    Some(p2.copyWithNewQry(p2.qry.copy(searchState = BottomQry))) else None
                  executeBackward(qrySet, limit, deadline, refutedSubsumedOrWitnessed ++ addIfPredEmpty,
                    stopExplorationAt, invarMap)
                }
              case None =>
                // approx mode indicates this state should be dropped (under approx)
                executeBackward(qrySet, limit, deadline, refutedSubsumedOrWitnessed, stopExplorationAt, invarMap)
            }
        }
    }
  }

  /**
   * Call methods to choose where to go with symbolic execution and apply transfer functions
   * @param qry location and state combination
   * @return
   */
  def executeStep(qry:Qry):Set[Qry] = qry match{
    case Qry(state, loc, Live) =>
      val predecessorLocations = controlFlowResolver.resolvePredicessors(loc,state)
      predecessorLocations.flatMap(l => { //see if .par here makes sense
        val newStates = transfer.transfer(state,l,loc)
        newStates.map(state => stateSolver.simplify(state, config.specSpace) match {
          case Some(state) if stateSolver.witnessed(state, config.specSpace).isDefined =>
            Qry(state, l, WitnessedQry(stateSolver.witnessed(state, config.specSpace)))
          case Some(state) => Qry(state, l, Live)
          case None =>
            Qry(state,l, BottomQry)
        })
      }).seq.toSet
    case Qry(_,_, BottomQry) => Set()
    case Qry(_,_,WitnessedQry(_)) =>
      //TODO: this was "Set()". Is there a reason we may want to step here?
      throw new IllegalStateException("Useless to take abstract step on witnessed query")
  }
}
