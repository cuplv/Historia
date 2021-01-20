package edu.colorado.plv.bounder.symbolicexecutor.state
import java.io.{File, PrintWriter}

import com.sun.org.glassfish.gmbal.IncludeSubclass
import scalax.collection.Graph
import scalax.collection.edge.LDiEdge
import scalax.collection.GraphEdge._
import scalax.collection.GraphPredef._
import scalax.collection.io.dot.Indent._
import scalax.collection.edge.Implicits._
import scalax.collection.io.dot.{DotAttr, DotEdgeStmt, DotGraph, DotRootGraph, Id, NodeId}

object PrettyPrinting {
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
