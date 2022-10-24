package edu.colorado.plv.bounder.synthesis

import com.microsoft.z3.{AST, BoolExpr, BoolSort, Context, Expr, FuncDecl, IntExpr, IntNum, Sort, UninterpretedSort}
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecAssignment, SpecSpace}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, Exists, Forall, LSAtom, LSConstraint, LSFalse, LSImplies, LSPred, LSSpec, LSTrue, NS, Not, Once, Or, UComb}
import edu.colorado.plv.bounder.solver.EncodingTools.Q
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, EncodingTools, Nameable, Z3SolverCtx, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{Equals, IPathNode, NamedPureVar, NotEquals, OutputMode, PureExpr, PureVal, PureVar, Qry, State}

import scala.annotation.tailrec
import scala.collection.mutable

class Z3ModelGenerator(persistentConstraints: ClassHierarchyConstraints)(implicit outputMode: OutputMode)
  extends Z3StateSolver(persistentConstraints, timeout = 30000,randomSeed=3578,
    defaultOnSubsumptionTimeout = _ => false, pushSatCheck = true
  ) with ModelGenerator {
  private def baseAxioms(implicit zCtx:Z3SolverCtx) = {
    List(a => initalizeConstAxioms(a), a => initializeNameAxioms(a), a => initializeFieldAxioms(a),
      a => initializeOrderAxioms(a))
  }
  //val ctx : Context = new Context

  //  *****  Syntax directed encoding *****
  def encodeMayContainInit(state:State)(implicit z3SolverCtx: Z3SolverCtx, specs:SpecSpace,
                                        messageTranslator: MessageTranslator):BoolExpr = {

    //Note: this is kinda negating things? But also substitutes false for things?
    //TODO: this is probably wrong, trying it out for testing
    def initify(pred:LSPred):LSPred = pred match {
      case Once(_,_,_) => LSFalse
      case NS(_,_) => LSFalse
      case Or(l1, l2) => Or(initify(l1), initify(l2))
      case And(l1, l2) => And(initify(l1), initify(l2))
      case Not(Once(_,_,_)) => ???  //false ish?
      case LSConstraint(v1, Equals, v2) => LSConstraint(v1,Equals, v2)
      case LSConstraint(v1, NotEquals, v2) => LSConstraint(v1,NotEquals, v2)
      case Forall(vars, p) => Forall(vars, initify(p))
      case Exists(vars, p) => Exists(vars, initify(p))
      case UComb(name, dep,false) => UComb(name,dep.map(initify),false)
      case UComb(name, dep,true) => throw new IllegalArgumentException("cannot initify already initified")
      case LSImplies(l1, l2) => ???
      case Not(l) => ???
      case LSTrue => LSTrue
      case LSFalse => LSFalse
      case atom: LSAtom => ???
    }
    val statePV = state.pureVars()
    val definedPvMap:Map[PureVar,AST] = statePV.map{pv => pv-> mkFreshPv(pv)}.toMap
    if(state.sf.heapConstraints.nonEmpty)
      ??? //TODO: excludes initial if heap cell must be non-null
    if(state.sf.callStack.nonEmpty)
      return mkBoolVal(false) // trivially excludes initial if call string is non-empty
    val pred = EncodingTools.rhsToPred(state.sf.traceAbstraction.rightOfArrow, specs)
      .map(EncodingTools.simplifyPred)
    val combinedPred:LSPred = initify(pred.reduce(Or))
    val encoded = encodePred(combinedPred, messageTranslator, definedPvMap, Map(), Map(),Map())
    val out = mkExistsAddr(definedPvMap, (whatever:Map[PureVar, AST]) => encoded)
    out
  }

  def encodeExcludesInit(state:State)
                        (implicit z3SolverCtx: Z3SolverCtx, specs:SpecSpace,
                         messageTranslator: MessageTranslator):BoolExpr = {
    //Note: this is kinda negating things? But also substitutes false for things?
    //TODO: this is probably wrong, trying it out for testing
    def notInitify(pred:LSPred):LSPred = pred match {
      case Once(_,_,_) => LSTrue
      case NS(_,_) => LSTrue
      case Or(l1, l2) => And(notInitify(l1), notInitify(l2))
      case And(l1, l2) => Or(notInitify(l1), notInitify(l2))
      case Not(Once(_,_,_)) => ???  //false ish?
      case LSConstraint(v1, Equals, v2) => LSConstraint(v1,NotEquals, v2)
      case LSConstraint(v1, NotEquals, v2) => LSConstraint(v1,Equals, v2)
      case Forall(vars, p) => Exists(vars, notInitify(p))
      case Exists(vars, p) => Forall(vars, notInitify(p))
      case UComb(name, dep,false) => UComb(name,dep.map(notInitify),true)
      case UComb(name, dep,true) => throw new IllegalArgumentException("cannot initify already initified")
      case LSImplies(l1, l2) => ???
      case Not(l) => ???
      case LSTrue => LSFalse
      case LSFalse => LSTrue
      case atom: LSAtom => ???
    }
    val statePV = state.pureVars()
    val definedPvMap:Map[PureVar,AST] = statePV.map{pv => pv-> mkFreshPv(pv)}.toMap
    if(state.sf.heapConstraints.nonEmpty)
      ??? //TODO: excludes initial if heap cell must be non-null
    if(state.sf.callStack.nonEmpty)
      return mkBoolVal(false) // trivially excludes initial if call string is non-empty
    val pred = EncodingTools.rhsToPred(state.sf.traceAbstraction.rightOfArrow, specs)
      .map(EncodingTools.simplifyPred)
    val combinedPred:LSPred = notInitify(pred.reduce(Or))
    val encoded = encodePred(combinedPred, messageTranslator, definedPvMap, Map(), Map(),Map())
    val out = mkForallAddr(definedPvMap, (whatever:Map[PureVar, AST]) => encoded)
    out
  }

  def encodeFeasible(state:State)(implicit z3SolverCtx: Z3SolverCtx, specs:SpecSpace):BoolExpr = {
    ???
  }

  def encodeNotFeasible(state:State)(implicit z3SolverCtx: Z3SolverCtx, specs:SpecSpace):BoolExpr = {
    ???
  }
  def learnRulesFromExamples_formula(target: Set[IPathNode], reachable: Set[IPathNode],
                                     space: SpecSpace)(implicit outputMode: OutputMode): Option[SpecAssignment] = {
    implicit val s = space
    implicit val zCtx: Z3SolverCtx = getSolverCtx
    try {
      zCtx.acquire()
      implicit val messageTranslator = MessageTranslator(collectStates(target), s)
      val orF = (v: List[BoolExpr]) => mkOr(v).asInstanceOf[BoolExpr]
      val andF = (v: List[BoolExpr]) => mkAnd(v).asInstanceOf[BoolExpr]
      val targetEnc = encodeTree(target, encodeExcludesInit, encodeNotFeasible, orF, andF)
      val reachEnc = encodeTree(target, encodeMayContainInit, encodeFeasible, andF, orF)
      zCtx.mkAssert(mkAnd(targetEnc, reachEnc))
      val res = checkSATOne(messageTranslator, baseAxioms)
      if(res){
        ???
      }else
        None
    }finally{
      zCtx.release()
    }
  }
  //end  *****  Syntax directed encoding *****

  type PathNode = (LSAtom,State)
  type UninExpr = Expr[UninterpretedSort]
  sealed trait Classification
  case object Reachable extends Classification
  case object Unreachable extends Classification
  case object Unset extends Classification

  case class NormalizedPath(leaves:Set[PathNode], target:PathNode, dag:Map[PathNode,PathNode], uid:Int,
                            classification:Classification){
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
      case (atom, state) => atom.lsVar ++ state.pureVars()
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
  def makePaths(leaves:Set[IPathNode]): Set[NormalizedPath] = {

    //TODO: make path merged in use equiv pvs where they match in the trace, use non-conflicting pv otherwise
    def merge(n1:NormalizedPath, n2:NormalizedPath):NormalizedPath = ???

    def mk(atoms:List[LSAtom],state:State):NormalizedPath= atoms match {
      case head::next => {
        val headLeaf = (head,state)
        var cLeaf = headLeaf
        var cNext = next
        val dag = new mutable.HashMap[PathNode,PathNode]()
        while(cNext.nonEmpty) {
          val nextNode = (cNext.head, State.topState)
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
      val c = mk(hist,state)
      val next = node.succ.map(traverse)
      (c::next).reduce(merge)
    }
    val terminals = leaves.map(traverse)
    terminals.groupBy(a => a.target).map{
      case (_, value) => value.reduce(merge)
    }.toSet
  }

  //  *****  Automata based encoding *****

  case class AutomataTranslator(states:Iterable[State], specSpace:SpecSpace, nStates:Int,
                                nRegisters:Int, modelGenerator: Z3ModelGenerator)
                               (implicit zCtx:Z3SolverCtx){
    private val ctx = zCtx.ctx
    val mt = MessageTranslator(states, specSpace)

    val autStates: Z3SetEncoder = Z3SetEncoder((0 until nStates).map(n => Q(n)).toSet, "AutQ")
    // state 0 is initial state
    val initialState = autStates.solverExprFor(Q(0))

    def mkStateVar():UninExpr = ctx.mkFreshConst("state", mkStateSort)

    val registers: Z3SetEncoder = Z3SetEncoder((0 until nRegisters).map(n => NamedPureVar(s"$n")).toSet, "Register")
    //register 0 is special don't care register
    val noCareReg = registers.solverExprFor(NamedPureVar("0"))


    lazy val transitionFunction:Map[Once,FuncDecl[BoolSort]] = {
      mt.inamelist
      ???
    }
    def mkTransition(oldState:Expr[UninterpretedSort], newState:Expr[UninterpretedSort], symbol:Once):BoolExpr = {
      ???
    }

    def mkAccept():FuncDecl[BoolSort] ={
      val sorts:Array[Sort] = Array(mkStateSort)
      ctx.mkFuncDecl("acceptState", sorts, ctx.mkBoolSort())
    }

    def mkStateSort:UninterpretedSort = autStates.getSort
    def mkRegSort:UninterpretedSort = registers.getSort

    def valuationFunction(np:NormalizedPath):FuncDecl[UninterpretedSort] = {
      val argSort:Array[Sort] = Array(mkRegSort)
      ctx.mkFuncDecl(s"val_${np.name}", argSort , modelGenerator.addrSort)
    }

    def axiomList:List[MessageTranslator => Unit] =
      List(autStates
        ,registers
      ).map(zSet=> _ => zCtx.mkAssert(zSet.getAxioms()))


  }

  case class InstantiationIdentifier(specUid:Int, locationUid:Int) extends Nameable {
    override def solverName: String = s"inst_${specUid}_${locationUid}"
  }

  case class InstPredIdentifier(inst:InstantiationIdentifier, predLocationUID:Int) extends Nameable {
    override def solverName: String = s"pred_${predLocationUID}_${inst.solverName}"
  }

  def encodeWithTgt(spec:LSSpec, specUid:Int, path:NormalizedPath, automataTranslator: AutomataTranslator,
                    pathNode: PathNode)(implicit zCtx:Z3SolverCtx):Expr[BoolSort] = {
    val leafState: Set[((LSAtom, State), Expr[UninterpretedSort])] =
      path.leaves.map(leaf => (leaf, automataTranslator.initialState)) //state for each leaf

    val instantiationIdentifier = InstantiationIdentifier(specUid, path.nodeUID(pathNode))

    val targetOnce = spec.target

    // acceptOp: operator to combine leaves of acceptance - or for positive example false for negative
    // acceptV: should the last state be accepting - true for positive example false for negative.
    val (acceptOp, acceptV) = path.classification match {
      case Reachable => ((v:Iterable[BoolExpr]) => mkOr(v), mkBoolVal(true))
      case Unreachable => ((v:Iterable[BoolExpr]) => mkAnd(v), mkBoolVal(false))
      case Unset => throw new IllegalArgumentException()
    }

    val nodeToIdent =
      path.allNodes.map{n => (n -> InstPredIdentifier(instantiationIdentifier, path.nodeUID(n)))}.toMap

    // ** quantified stuff **
    // pure variables in normalized path
    // pure variables are quantified over full path, normalization makes sure they are the same between states
    val allPureVars = path.allPv

    // make state variables for each pred location

    val nodeToState: Map[PathNode, Expr[UninterpretedSort]] = nodeToIdent.map{
      case (node, identifier) =>
        node -> zCtx.ctx.mkConst(s"state_${identifier.solverName}", automataTranslator.mkStateSort)
    }

    // make register variables for each pred location and arg in transition
    val nodeArgToRegister:Map[Once,Array[PureExpr]] = nodeToIdent.map{
      case ((o@Once(mt,sig,lsVars),_), identifier) => o -> lsVars.toArray
    }

    //List of variables to quantify later
    val nodeRegisters: Array[PureVar] = nodeArgToRegister.toArray.flatMap{
      case (_, pExpr) =>
        val out: Array[PureVar] = pExpr.flatMap{
          case p:PureVar => Some(p)
          case _ => None
        }
        out
    }
    // ** end quantified stuff**

    // assert one is accepting or all are not accepting based on classification
    // note: only one accepting TODO: rm acceptOp
    val tgtIsAccept = automataTranslator.mkAccept().apply(nodeToState(pathNode))

    // encode each transition - base case leaves are initial state
    def encodeTransitions(worklist:Set[(UninExpr, PathNode)]):BoolExpr = {
      if(worklist.size != 1) {
        ??? //TODO implement this
      }
      ???


    }
    val transitions = encodeTransitions(path.leaves.map{(node:PathNode) => (automataTranslator.initialState, node)})



    // combine all with quantifiers
    ??? //TODO quantify things
    mkAnd(List(tgtIsAccept, transitions)) //TODO
  }

  /**
   * Encoding is done on a per position, per sample, per spec basis
   * @param spec target back msg plus messages that may affect enabledness and aliasing
   * @param specUID unique identifier for specification
   * @param path
   * @param automataTranslator
   * @param zCtx
   * @return
   */
  def encode(spec:LSSpec, specUID:Int, path:NormalizedPath,
             automataTranslator: AutomataTranslator)(implicit zCtx:Z3SolverCtx):BoolExpr = {
    //TODO: find all instances of target in normalized path and encode aut for each
    //TODO: for now, we just find one

    val target = spec.target

    val preds = path.findall{
      case (atom, _) => atom.identitySignature == target.identitySignature
    }.map{
      case n:PathNode => encodeWithTgt(spec, specUID, path, automataTranslator, n)
    }


    ???
  }


  def learnRulesFromExamples_automata(target: Set[IPathNode], reachable: Set[IPathNode],
                                      space: SpecSpace): Option[SpecAssignment] = {
    def identNorm(value: Set[NormalizedPath], classification: Classification) =
      value.zipWithIndex.map{case (k,v) => k.copy(uid=v, classification = classification)}
    implicit val s = space
    implicit val zCtx: Z3SolverCtx = getSolverCtx
    try {
      zCtx.acquire()
      implicit val automataTranslator = AutomataTranslator(collectStates(target) ++ collectStates(reachable),
        s, 3,3,this)
      val samples:Set[NormalizedPath] =
        identNorm(makePaths(target), Unreachable) ++ identNorm(makePaths(reachable), Reachable)

      val encodedSamples =
        BounderUtil.repeatingPerm((i:Int) => if(i == 0)(space.getSpecs) else  samples, 2).map {
          case (spec:LSSpec)::(path:NormalizedPath):: Nil =>
            encode(spec, space.getSpecUID(spec), path, automataTranslator)
          case _ => ???
        }

      ???
      zCtx.mkAssert(???)
      val res = checkSATOne(automataTranslator.mt, baseAxioms ++ automataTranslator.axiomList)
      ???
    }finally{
      zCtx.release()
    }
  }

  // edges labeled with once or not once
  // variables on edge

  //end   *****  Automata based encoding *****

  def encodeLeg(node:IPathNode,termOp:State=>BoolExpr, ancestorOp:State=>BoolExpr,
                ancestorConn: List[BoolExpr]=> BoolExpr)
               (implicit z3SolverCtx: Z3SolverCtx, outputMode: OutputMode, specs:SpecSpace):BoolExpr = {
    var currentForm = termOp(node.state)
    var cNode = node
    while(cNode.succ.nonEmpty){
      assert(cNode.succ.size == 1, "multi succ not supported yet")
      cNode = cNode.succ.head
      currentForm = ancestorConn(List(currentForm, ancestorOp(cNode.state)))
    }
    currentForm
  }
  def encodeTree(tree:Set[IPathNode],
                  termOp: State => BoolExpr,
                  ancestorOp:State=>BoolExpr,
                  ancestorConn: List[BoolExpr]=> BoolExpr,
                  peerConn:List[BoolExpr] => BoolExpr,
                )(implicit z3SolverCtx: Z3SolverCtx, outputMode: OutputMode, space:SpecSpace):BoolExpr = {
    if(tree.isEmpty){
      return mkBoolVal(true)
    }
    val current = peerConn(tree.map(n => encodeLeg(n, termOp, ancestorOp, ancestorConn)).toList)
    val next = encodeTree(tree.flatMap(n => n.succ), termOp, ancestorOp, ancestorConn, peerConn)
    peerConn(List(current,next))
  }

  def collectStates(tree:Set[IPathNode])(implicit outputMode: OutputMode):Set[State] = {
    if(tree.isEmpty)
      return Set.empty
    val cur = tree.map(_.state)
    val next = tree.flatMap(_.succ)
    cur ++ collectStates(next)
  }

  /**
   *
   * @param posExamples set of traces representing reachable points (List in reverse execution order)
   * @param negExamples
   * @param rulesFor    learn rules restricting the back messages in this set
   * @return an automata represented by transition tuples (source state, transition symbol, target state)
   */
  override def learnRulesFromExamples(target: Set[IPathNode], reachable: Set[IPathNode],
                                      space: SpecSpace)(implicit outputMode: OutputMode): Option[SpecAssignment] =
    learnRulesFromExamples_automata(target, reachable, space)
}

