package edu.colorado.plv.bounder.ir
import edu.colorado.plv.bounder.ir.Trace.step
import edu.colorado.plv.bounder.lifestate.LifeState.{LSPred, LSTrue, Signature}
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.solver.ClassHierarchyConstraints
import edu.colorado.plv.bounder.symbolicexecutor.state.PureExpr
import upickle.default.{macroRW, ReadWriter => RW}


case class Trace(t:List[TMessage]) extends AnyVal{
  def size:Int = t.size
}
object Trace {
  def empty = Trace(Nil)
  def step(msg:TraceElement, pred:LSPred, space:SpecSpace)(implicit cha:ClassHierarchyConstraints):LSPred = msg match {
    case TCLInit(cl) => ???
    case TNew(v, types) => ???
    case msg:TMessage =>
      val matchedMsgs = space.allI.filter(m => m.contains(msg.mType,msg.fwkSig))
      ???
  }
}

sealed trait ApproxDir
case object OverApprox extends ApproxDir
case object UnderApprox extends ApproxDir
case object Exact extends ApproxDir

/**
 * Under approximate representation of message histories
 * TODO: we may want some way to connect this with the associated nodes in the over-approximation
 * @param tgt reachable or unreachable location
 * @param edges under-approximate steps to the tgt location
 */
case class ConcGraph(tgt:TMessage, edges:Map[TMessage,Set[TMessage]]){

  lazy val reverseEdges:Map[TMessage,TMessage] = edges.flatMap{
    case (k,v) => v.map(_ -> k)
  }

  /**
   * prune all paths not matching spec space
   * @param specSpace
   * @return (initial nodes, nodes that may be extended)
   */
  def filter(specSpace:SpecSpace)(implicit cha:ClassHierarchyConstraints):Set[(TMessage, LSPred)] = {

    def iFilter(workList:List[(TMessage,LSPred)], acc:Set[(TMessage,LSPred)]):Set[(TMessage,LSPred)] = {
      val (cMessage, cPred) = workList.head
      val prev = step(cMessage, cPred, specSpace)
      //TODO========

      ???
    }
    iFilter(List((tgt, LSTrue)), Set())
  }
  def add(src:TMessage,tgt:TMessage):ConcGraph = {
    val newEdges = edges.get(src) match {
      case Some(s) => edges + (src -> (s + tgt))
      case None => edges + (src -> Set(tgt))
    }
    ConcGraph(tgt,newEdges)
  }
}


sealed trait MessageType {
  def toTex:String

}

object MessageType{
  implicit var rw:RW[MessageType] = RW.merge(macroRW[CIEnter.type],  macroRW[CIExit.type],
    macroRW[CBEnter.type], macroRW[CBExit.type])
}
case object CIEnter extends MessageType {
  override def toTex: String = "\\enkwCi"
}
case object CIExit extends MessageType {
  override def toTex: String = "\\enkwCi" // Not distinguishing between entry/exit in paper
}
case object CBEnter extends MessageType {
  override def toTex: String = "\\enkwCb"
}
case object CBExit extends MessageType {
  override def toTex: String = "\\enkwCb\\enkwRet"
}

sealed trait Method {
  def sig:Signature
  def fwkSig:Option[Signature]
}
object Method{
  implicit var rw:RW[Method] = RW.merge(AppMethod.rw, FwkMethod.rw)
}
case class AppMethod(sig:Signature, fwkOverride : Option[FwkMethod]) extends Method{
  override def fwkSig: Option[Signature] = fwkOverride.flatMap(_.fwkSig)
}
object AppMethod{
  implicit var rw:RW[AppMethod] = macroRW
}
case class FwkMethod(sig:Signature) extends Method{
  override def fwkSig: Option[Signature] = Some(sig)
}
object FwkMethod{
  implicit var rw:RW[FwkMethod] = macroRW
}

sealed trait TraceElement
object TraceElement{
  implicit var rw:RW[TraceElement] = RW.merge(TNew.rw, TMessage.rw)//, macroRW[TInitial.type])
}

//case object TInitial extends TraceElement

case class TCLInit(cl:String)extends TraceElement
object TCLInit{
  implicit var rw:RW[TCLInit] = macroRW
}
case class TNew(v:PureExpr, types:TypeSet) extends TraceElement
object TNew{
  implicit var rw:RW[TNew] = macroRW
}
case class TMessage(mType : MessageType, method: Method, args: List[PureExpr],
                    receiverType:String = "java.lang.Object") extends TraceElement {

  def fwkSig: Signature = method.fwkSig.getOrElse{
    throw new IllegalArgumentException(s"Trace message must be a callback or callin, found: $method")
  }

  override def toString: String = s"$mType ${method.sig.methodSignature}( ${args.mkString(",")} )"
}
object TMessage{
  implicit var rw:RW[TMessage] = macroRW
}




case class WitnessExplanation(futureTrace:List[TraceElement]){
  override def toString: String = s"Future trace:\n ${futureTrace.mkString("\n")}\n"
}
object WitnessExplanation{
  implicit var rw:RW[WitnessExplanation] = macroRW
}
