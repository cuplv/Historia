package edu.colorado.plv.bounder.synthesis

import edu.colorado.plv.bounder.ir.{CallbackMethodInvoke, CallbackMethodReturn, TestIRMethodLoc}
import edu.colorado.plv.bounder.lifestate.LifeState
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSingle, Once}
import edu.colorado.plv.bounder.symbolicexecutor.state.{AbstractTrace, IPathNode, MemoryOutputMode, NamedPureVar, OrdCount, OutputMode, PathNode, PureExpr, Qry, State, Unknown}

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
      "bar" -> Set("bar"),
      "foo2" -> Set("foo2")
    )

  val classToInt: Map[String, Int] = hierarchy.keySet.zipWithIndex.toMap
  val intToClass: Map[Int, String] = classToInt.map(k => (k._2, k._1))

  val dummyMethod = TestIRMethodLoc("","",Nil)
  val dummyLoc = CallbackMethodInvoke("", "", dummyMethod)
  val top = State.topState

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
      val qry = Qry(top.copy(sf=top.sf.copy(traceAbstraction = AbstractTrace(at))), dummyLoc, Unknown)
      //Set(PathNode(qry, witTreeFromMsgList(t).toList, None)) //TODO: test out full enc
      Set(PathNode(qry, Nil, None))
    case Nil => Set.empty
  }
  def targetIze(history:List[LSSingle]):List[LSSingle] = {
    def vTargetIze(pureExpr:PureExpr):PureExpr = pureExpr match {
      case NamedPureVar(name) => NamedPureVar(s"${name}_tgt")
      case other => other
    }
    history.map {
      case LifeState.CLInit(sig) => ???
      case LifeState.FreshRef(v) => ???
      case Once(mt, signatures, lsVars) => Once(mt, signatures, lsVars.map(vTargetIze))
    }
  }
}

class DummyOrd extends OrdCount{

  override def delta(current: Qry): Int = current.loc match {
    case CallbackMethodInvoke(_, _, _) => 1
    case CallbackMethodReturn(_, _, _, _) => 1
    case _ => 0
  }

  override def compare(x: IPathNode, y: IPathNode): Int = ???
}
