package edu.colorado.plv.bounder.synthesis

import com.microsoft.z3.{AST, BoolExpr, Context, Expr, IntExpr, IntNum}
import edu.colorado.plv.bounder.lifestate.{LifeState, SpecAssignment, SpecSpace}
import edu.colorado.plv.bounder.lifestate.LifeState.{And, Exists, Forall, LSAtom, LSConstraint, LSFalse, LSImplies, LSPred, LSTrue, NS, Not, Once, Or, PredicateSpace, UComb}
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, EncodingTools, Z3SolverCtx, Z3StateSolver}
import edu.colorado.plv.bounder.symbolicexecutor.state.{Equals, IPathNode, NotEquals, OutputMode, PureVar, Qry, State}

import scala.annotation.tailrec

class Z3ModelGenerator(persistentConstraints: ClassHierarchyConstraints)
  extends Z3StateSolver(persistentConstraints, timeout = 30000,randomSeed=3578,
    defaultOnSubsumptionTimeout = _ => false, pushSatCheck = true
  ) with ModelGenerator {
  //val ctx : Context = new Context

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
    val out = mkForallAddr(definedPvMap, (whatever:Map[PureVar, AST]) => encoded)
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
      return mkBoolVal(true).asInstanceOf[BoolExpr]
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
      val res = checkSATOne(messageTranslator, List(initalizeConstAxioms, initializeNameAxioms, initializeFieldAxioms, initializeOrderAxioms))
      if(res){
        ???
      }else
        None
    }finally{
      zCtx.release()
    }
  }
}

