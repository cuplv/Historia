package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.ir.{AppMethod, CBEnter, CBExit, CIEnter, CIExit, CNode, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, ConcGraph, FwkMethod, Loc, MessageType, Method, SerializedIRMethodLoc, TMessage}
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState.{AbsMsg, LSSingle, OAbsMsg, Signature, SignatureMatcher}
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, ConcreteAddr, ConcreteVal, IPathNode, MemoryOutputMode, NamedPureVar, NullVal, OrdCount, OutputMode, PathNode, PureExpr, PureVal, PureVar, Qry, State, TopVal, Unknown}

import scala.util.matching.Regex

object SynthTestUtil {

  val hierarchy: Map[String, Set[String]] =
    Map("java.lang.Object" -> Set("String", "Foo", "Bar",
      "com.example.createdestroy.MyFragment",
      "rx.Single",
      "com.example.createdestroy.-$$Lambda$MyFragment$hAOPQ7FFP1lMCJX7gGOvwmZq1uk",
      "java.lang.Object"),
      "String" -> Set("String"), "Foo" -> Set("Bar", "Foo"), "Bar" -> Set("Bar"),
      "com.example.createdestroy.MyFragment" -> Set("com.example.createdestroy.MyFragment"),
      "com.example.createdestroy.-$$Lambda$MyFragment$hAOPQ7FFP1lMCJX7gGOvwmZq1uk" ->
        Set("com.example.createdestroy.-$$Lambda$MyFragment$hAOPQ7FFP1lMCJX7gGOvwmZq1uk"),
      "rx.Single" -> Set("rx.Single"),
      "foo" -> Set("foo"),
      "rx.functions.Action1"->Set("rx.functions.Action1"),
      "bar" -> Set("bar"),
      "foo2" -> Set("foo2")
    )

  implicit val cha = new ClassHierarchyConstraints(hierarchy,Set("java.lang.Runnable"),intToClass)

  val classToInt: Map[String, Int] = hierarchy.keySet.zipWithIndex.toMap
  val intToClass: Map[Int, String] = classToInt.map(k => (k._2, k._1))

  val dummyMethod = SerializedIRMethodLoc("","",Nil)
  val dummyLoc = CallbackMethodInvoke(Signature("", "a()"), dummyMethod)
  val top = State.topState
  def onceToTestLoc(o:LSSingle):Loc = o match {
    case LifeState.CLInit(sig) => ???
    case LifeState.FreshRef(v) => ???
    case OAbsMsg(CBEnter, signatures, lsVars) => //TODO: may want to gen args at some point
      val sig = signatures.example()
      CallbackMethodInvoke( sig, SerializedIRMethodLoc(sig.base,sig.methodSignature,Nil))
    case OAbsMsg(CBExit, signatures, lsVars) =>
      val sig = signatures.example()
      CallinMethodReturn(sig)
    case OAbsMsg(CIEnter, signatures, lsVars) =>
      val sig = signatures.example()
      CallinMethodInvoke(sig)
  }

  /**
   * Create a witness tree with top states from a list of abstract messages
   * @param history list of abstract messages
   * @param ord
   * @param mode
   * @return
   */
  def witTreeFromMsgList(history : List[LSSingle])
                        ( implicit ord: OrdCount, mode: OutputMode = MemoryOutputMode):Set[IPathNode] = history match{
    case at@_::t =>
      val qry = Qry(top.copy(sf=top.sf.copy(traceAbstraction = AbstractTrace(at))), onceToTestLoc(at.head), Unknown)
      //Set(PathNode(qry, witTreeFromMsgList(t).toList, None)) //TODO: test out full enc
      Set(PathNode(qry, Nil, None))
    case Nil => Set.empty
  }
  def methodFromSig(mt:MessageType,sig:SignatureMatcher):Method = {
    val sigex = sig.example()
//    val mLoc = SerializedIRMethodLoc(clazz,methodSig,Nil)
    val fwkMethod = FwkMethod(sigex)
    mt match {
      case CBEnter => AppMethod(sigex, Some(fwkMethod))
      case CBExit => AppMethod(sigex, Some(fwkMethod))
      case CIEnter => fwkMethod
      case CIExit => fwkMethod
    }
  }
  def toConcGraph(history:List[LSSingle]):ConcGraph = {
    if(history.isEmpty)
      throw new IllegalArgumentException("History must not be empty")
    val pvs: Map[PureVar, PureExpr] = history.flatMap{ v => v.lsVar}.zipWithIndex.map{
      case (p@PureVar(id), i) => (p, NamedPureVar(s"${id}_$i"))
    }.toMap
    val tMessages = history.map {
      case LifeState.CLInit(sig) => ???
      case LifeState.FreshRef(v) => ???
      case OAbsMsg(mt, signatures, lsVars) =>
        val m = methodFromSig(mt,signatures)
        new CNode(TMessage(mt,m, lsVars.map{
          case p:PureVar => pvs(p)
          case TopVal => NullVal
        }))
    }
    val start = tMessages.head
    val last = tMessages.last

    def addEdgesToGraph(graph:ConcGraph, tmessages:List[CNode]):ConcGraph = tmessages match {
      case _::Nil => graph
      case Nil => graph
      case tmsg::tmsgTail =>
        val newGraph = graph.add(tmsg,tmsgTail.head)
        addEdgesToGraph(newGraph, tmsgTail)
    }
    addEdgesToGraph(ConcGraph(last, Set(start), Map.empty), tMessages)
  }
  def targetIze(history:List[LSSingle]):List[LSSingle] = {
    def vTargetIze(pureExpr:PureExpr):PureExpr = pureExpr match {
      case NamedPureVar(name) => NamedPureVar(s"${name}_tgt")
      case other => other
    }
    history.map {
      case LifeState.CLInit(sig) => ???
      case LifeState.FreshRef(v) => ???
      case OAbsMsg(mt, signatures, lsVars) => AbsMsg(mt, signatures, lsVars.map(vTargetIze))
    }
  }
}

class DummyOrd extends OrdCount{

  override def delta(current: Qry): Int = current.loc match {
    case _:CallbackMethodInvoke => 1
    case _:CallbackMethodReturn => 1
    case _ => 0
  }

  override def compare(x: IPathNode, y: IPathNode): Int = ???
}
