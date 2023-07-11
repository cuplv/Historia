package edu.colorado.plv.bounder.ir
import better.files.File
import better.files.File.CopyOptions
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.lifestate.LifeState.{And, LSPred, LSTrue, OAbsMsg, Signature}
import edu.colorado.plv.bounder.lifestate.SpecSpace
import edu.colorado.plv.bounder.solver.{ClassHierarchyConstraints, EncodingTools}
import edu.colorado.plv.bounder.symbolicexecutor.state.PureExpr
import upickle.default.{macroRW, ReadWriter => RW}

import scala.annotation.tailrec


case class Trace(t:List[TMessage]) extends AnyVal{
  def size:Int = t.size
}
object Trace {
  def empty = Trace(Nil)
}

sealed trait ApproxDir
case object OverApprox extends ApproxDir
case object UnderApprox extends ApproxDir
case object Exact extends ApproxDir

class CNode(msg:TMessage){
  def getMsg = this.msg

  override def toString: String = s"""${System.identityHashCode(this)}_${msg.toString}"""
}

/**
 * Under approximate representation of message histories
 * TODO: we may want some way to connect this with the associated nodes in the over-approximation
 * @param tgt reachable or unreachable location
 * @param edges under-approximate steps to the tgt location
 */
case class ConcGraph(tgt:CNode,init:Set[CNode], edges:Map[CNode,Set[CNode]]){


  def toDotGraph(out:String): Unit = {
    val nodes = edges.keys.map(_.getMsg.toDotNode).mkString("\n")
    val edgesOut = this.edges.map{case (src, tgts) =>
      tgts.map(tgt => s"${src.getMsg.toDotNode} -> ${tgt.getMsg.toDotNode}").mkString("\n")}.mkString("\n")
    val dotFile = s"digraph G {\n$nodes\n$edgesOut\n}"
    for {tempFile <- File.temporaryFile(suffix = ".dot")
         _ = tempFile.write(dotFile)
         _ = BounderUtil.runCmdStdout(s"dot -Tpng $tempFile -o $out")
//         _ = File(out).moveTo(File(out))(CopyOptions(overwrite=true))
    } yield ()
  }

  lazy val reverseEdges = edges.flatMap{
    case (k,v) => v.map(_ -> k)
  }.groupBy(_._1).map{case (k,v) => k -> v.values.toSet}

  /**
   * prune all paths not matching spec space
   * @param specSpace
   * @return (initial nodes, nodes that may be extended)
   */
  def filter(specSpace:SpecSpace)(implicit cha:ClassHierarchyConstraints):Set[(CNode, LSPred)] = {

    //TODO: may be able to memoize this
    def step(msg:TraceElement, pred:LSPred, space:SpecSpace)
            (implicit cha:ClassHierarchyConstraints):LSPred = msg match {
      case TCLInit(cl) => ???
      case TNew(v, types) => ???
      case msg:TMessage =>
        val matchedMsgs = space.allI.filter(m => m.contains(msg.mType,msg.fwkSig)).map{
          case OAbsMsg(mt, signatures, lsVars) =>
            // swap params in abstract messages with values from the under approx
            if(lsVars.size != msg.args.size)
              ??? //TODO: may want to handle this case by masking or something
            OAbsMsg(mt, signatures, msg.args)
        }
        assert(matchedMsgs.size < 2, "At most one message should match")
        matchedMsgs.headOption match {
          case Some(m) =>
            val out = EncodingTools.rhsToPred(m::Nil, space, Set(pred))
            out.reduceOption(And).getOrElse(LSTrue)
          case None => pred
        }
    }
    @tailrec
    def iFilter(workList:List[(CNode,LSPred)], acc:Set[(CNode,LSPred)]):Set[(CNode,LSPred)] = {
      if(workList.isEmpty)
        return acc
      val (cMessage, cPred) = workList.head
      println(cMessage.getMsg)
      val prevPred = step(cMessage.getMsg, cPred, specSpace)
      val prevMsg = reverseEdges.getOrElse(cMessage, Set.empty).map{
        m => m -> prevPred
      }
      val mayBeInit = prevMsg.filter{case (m,_) => init.contains(m)}
      iFilter(workList.tail ++ prevMsg, acc ++ mayBeInit)
    }
    iFilter(List((tgt, LSTrue)), Set())
  }
  def add(src:CNode,tgt:CNode):ConcGraph = {
    val newEdges = edges.get(src) match {
      case Some(s) => edges + (src -> (s + tgt))
      case None => edges + (src -> Set(tgt))
    }
    ConcGraph(tgt,init,newEdges)
  }
  def addInit(msg:CNode):ConcGraph = ConcGraph(tgt,init + msg,edges)
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
  def toDotNode:String = {
    val str = toString.replaceAll("[^a-zA-Z0-9]", "_")
    s"""${System.identityHashCode(this)} [label="${str}"];"""
  }

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
