package edu.colorado.plv.bounder.synthesis

import com.microsoft.z3.{AST, BoolExpr, Context, Expr, IntExpr, IntNum}
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState.{LSAtom, PredicateSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{PureVar, Qry, ReachingGraph, SomeQry, State}

import scala.annotation.tailrec

class Z3ModelGenerator extends ModelGenerator {
  val ctx : Context = new Context
  var id = 0
  def getNextZ3VarName(): String ={
    val cId = "v" + id
    id = id+1
    cId
  }
  val solver = {
    val solver = ctx.mkSolver
    val params = ctx.mkParams()
    params.add("timeout", 10000)
    solver.setParameters(params)
    solver
  }

  /**
   *
   * @param reachingGraph graph of queries
   * @param lsInterp
   * @param theta
   */
  def learnRulesFromNodeGraph(reachingGraph: ReachingGraph,
                              lsInterp: Map[Qry, LifeState.LSPred], theta: Map[String, PureVar]): Unit = {
    ???
  }


  def encodeNodeReachability(qry:Qry, pred: LifeState.LSPred, theta: Map[String, PureVar],
                             predSpace : PredicateSpace) : Unit = qry match {
    case SomeQry(State(stack, heap, pure, _,_,_,_,_), loc) => {
      val targetSig = loc.msgSig.get
      val edges = predSpace.getEdgeSet
      ???
    }
    case _ =>
      ???
  }

  @tailrec
  private final def mapMessageIdentifiers(example: List[TraceMessage], counter:Int = 0, acc: Map[String,Int]
  = Map()):(Map[String,Int],Int) = example match{
    case Nil => (acc,counter+1)
    case h::t if acc.contains(h.ident) => mapMessageIdentifiers(t, counter, acc)
    case h::t => mapMessageIdentifiers(t, counter + 1, acc + (h.ident -> counter))
  }

  case class RuleTemplate(ruleIdent:Int, mident_target:Int){
    val mident = ctx.mkInt(mident_target)
    // matcher identifies encoded matcher row in table
    // 0 indicates "True"
    val matcher = ctx.mkIntConst(s"r${ruleIdent}_matcher")

    // Constraints to keep matcher in defined range
    def must = ctx.mkOr(ctx.mkEq(matcher,ctx.mkInt(0)), ctx.mkEq(matcher,ctx.mkInt(1)))
  }
  trait MatcherTemplate
  case class NIMatcherTemplate(matcherIdent:Int) extends MatcherTemplate{
    val mIdentEnable = ctx.mkIntConst(s"m${matcherIdent}_identEnable")
    val mIdentDisable = ctx.mkIntConst(s"m${matcherIdent}_identEnable")
  }
  /**
   *
   * @param posExamples set of traces representing reachable points (List in reverse execution order)
   * @param negExamples
   * @param rulesFor learn rules restricting the back messages in this set
   * @return an automata represented by transition tuples (source state, transition symbol, target state)
   */
  override def learnRulesFromExamples(posExamples: Set[List[TraceMessage]],
                                      negExamples: Set[List[TraceMessage]],
                                      rulesFor:List[TraceMessage]): Unit = {


    //TODO:
    val messageIdentMap1 = posExamples.foldLeft((Map[String,Int](),0)){
      (acc,v) => mapMessageIdentifiers(v, acc._2, acc._1)}
    val messageIdentMap = negExamples.foldLeft(messageIdentMap1){
      (acc,v) => mapMessageIdentifiers(v, acc._2, acc._1)
    }._1
    val solver = ctx.mkSolver()

    // Identifier for rule 1
    val ruleTemplates = rulesFor.zipWithIndex.map(m => RuleTemplate(messageIdentMap(m._1.ident),m._2 ))
    val matcherTemplates = List(NIMatcherTemplate(1))
    posExamples.map(encode(_, messageIdentMap,ruleTemplates,matcherTemplates))
    negExamples.map(encode(_, messageIdentMap, ruleTemplates, matcherTemplates))
    ???
  }


  /**
   *
   * @param example
   * @return z3 formula representing the reachability of the last point.
   */
  def encode(example:List[TraceMessage], identMap:Map[String,Int],
             rules: List[RuleTemplate], matchers:List[MatcherTemplate]):BoolExpr = {
    val indexedMessages = example.zipWithIndex
    indexedMessages match{
      case (msg, index)::t =>{
//        val mident: IntNum = ctx.mkInt(identMap(msg.ident))
        val value: IntNum = ctx.mkInt(msg.v)
        val positionPreds: Seq[BoolExpr] = rules.flatMap(rule => {
          if(rule.mident == identMap(msg.ident)) {
            val (r_enabled, r_disabled) = iEncodeEnable(t, value, rule.matcher)
            Some(ctx.mkAnd(r_enabled, ctx.mkNot(r_disabled)))
          }else{
            None
          }
        })

        ???
      }
      case Nil => ctx.mkBool(true) // Empty trace is reachable
    }
    ???
  }
  def iEncodeEnable(example:List[(TraceMessage,Int)], targetValue:IntNum, ruleMatcher:IntExpr):(BoolExpr,BoolExpr) = example match{
    case (tm,ind)::t =>{
      ???
    }
    case _ =>
      ???
  }


  case class Automata(transitions: Set[Transition],initialState:Int, finalState:Int)
  case class Transition(sourceState: Int, transitionSymbol:Int, targetState:Int)

}

