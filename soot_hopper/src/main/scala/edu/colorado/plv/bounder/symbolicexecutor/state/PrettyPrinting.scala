package edu.colorado.plv.bounder.symbolicexecutor.state
import java.io.{File, PrintWriter}

import scalax.collection.Graph
import scalax.collection.edge.LDiEdge
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.io.dot.Indent._
import scalax.collection.edge.Implicits._
import scalax.collection.io.dot.{DotAttr, DotEdgeStmt, DotGraph, DotRootGraph, Id, NodeId}

import scala.io.Source

object PrettyPrinting {
  val templateFile = getClass.getResource("/pageTemplate.html").getPath
  val template = Source.fromFile(templateFile).getLines().mkString
  def qryString(q : Qry):String = q match{
    case SomeQry(state,loc) =>
      loc.toString +
        "   state: " + state.callStack.headOption.map(_.locals.toString).getOrElse("Empty stack")
    case BottomQry(state,loc) =>
      "REFUTED: " + loc.toString +
        "   state: " + state.callStack.headOption.map(_.locals.toString).getOrElse("Empty stack")
    case WitnessedQry(state,loc) =>
      "WITNESSED: " + loc.toString +
        "   state: " + state.callStack.headOption.map(_.locals.toString).getOrElse("Empty stack")
  }
  def witnessToTrace(pn:PathNode):List[String] = pn match{
    case PathNode(q, Some(pred), _) =>
      qryString(q) :: witnessToTrace(pred)
    case PathNode(q, None, _) =>
      qryString(q) :: Nil
    case v =>
      println(v)
      ???
  }
  def printWitnessTraces(result: Set[PathNode], outFile: String): Unit = {
    val pw = new PrintWriter(new File(outFile ))
    val live = result.flatMap{
      case pn@PathNode(_: SomeQry, _ , None) => Some(("live",pn))
      case pn@PathNode(_ :WitnessedQry, succ, _) => Some(("witnessed", pn))
      case _ => None
    }
    val traces = live.map(a => a._1 + "\n    " + witnessToTrace(a._2).mkString("\n    ")).mkString("\n")
    pw.write(traces)
    pw.close()
  }

  private def sanitizeStringForDot(str:String):String =
    str.replace(">","\\>")
      .replace("<","\\<")
      .replace("-","\\-")
      .replace("\"","\\\"").replace("|","\\|")
  private def iDotNode(qrySet:Set[PathNode],seen:Set[PathNode],
                       procNodes:Set[String],procEdges:Set[String],
                       includeSubsEdges:Boolean):(Set[String],Set[String]) = {
    if(qrySet.isEmpty){
      (procNodes,procEdges)
    }else {
      val cur = qrySet.head
      val rest = cur.succ match{
        case None => qrySet.tail
        case Some(v) => qrySet.tail + v
      }
      val curString = sanitizeStringForDot(cur.qry.toString)

      val init = if(cur.succ.isDefined) "" else "INITIAL: "
      val subs = if(cur.subsumed.isDefined)"SUBSUMED: " else ""
      val nextProcNodes = procNodes + s"""n${System.identityHashCode(cur)} [label="${init}${subs}${curString}"]"""
      // TODO: add subsumption edges
      // TODO: add subsumption labels
      val nextProcEdges = cur.succ match {
        case Some(v) =>
          assert(!v.subsumed.isDefined)
          procEdges + s"""n${System.identityHashCode(cur)} -> n${System.identityHashCode(v)}"""
        case None => procEdges
      }
      val subsumedEdges =
        if (includeSubsEdges)cur.subsumed.map(v =>
          s"\n    n${System.identityHashCode(v)}->n${System.identityHashCode(cur)}").getOrElse("") else ""
      iDotNode(rest, seen + cur, nextProcNodes, nextProcEdges + subsumedEdges, includeSubsEdges)
    }
  }
  def dotWitTree(qrySet : Set[PathNode], outFile:String, includeSubsEdges:Boolean) = {
    val pw = new PrintWriter(new File(outFile ))
    val (nodes,edges) = iDotNode(qrySet,Set(),Set(),Set(), includeSubsEdges)
    pw.write(
      s"""
         |digraph D {
         |    node[shape=record];
         |    ${nodes.mkString("\n    ")}
         |
         |    ${edges.mkString("\n    ")}
         |}
         |""".stripMargin)
    pw.close
  }

  def printWitnessOrProof(qrySet : Set[PathNode], outFile:String, includeSubsEdges:Boolean = false) =
    qrySet.find(_.qry.isInstanceOf[WitnessedQry]) match{
      case Some(v) => dotWitTree(Set(v), outFile, includeSubsEdges)
      case None => dotWitTree(qrySet, outFile, includeSubsEdges)
    }
}
