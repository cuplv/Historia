package edu.colorado.plv.bounder.symbolicexecutor.state
import java.io.{File, PrintWriter}

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
                       procNodes:Set[String],procEdges:Set[String]):(Set[String],Set[String]) = {
    if(qrySet.isEmpty){
      (procNodes,procEdges)
    }else {
      val cur = qrySet.head
      val rest = cur.succ match{
        case None => qrySet.tail
        case Some(v) => qrySet.tail + v
      }
      val curString = sanitizeStringForDot(cur.qry.toString)

      val nextProcNodes = procNodes + s"""n${System.identityHashCode(cur)} [label="${curString}"]"""
      // TODO: add subsumption edges
      // TODO: add subsumption labels
      val nextProcEdges = cur.succ match {
        case Some(v) => procEdges + s"""n${System.identityHashCode(cur)} -> n${System.identityHashCode(v)}""" +
          v.subsumed.map(v => s"\n    n${System.identityHashCode(cur)} -> n${System.identityHashCode(v)}").getOrElse("")
        case None => procEdges
      }
      iDotNode(rest, seen + cur, nextProcNodes, nextProcEdges)
    }
  }
  def dotWitTree(qrySet : Set[PathNode], outFile:String) = {
    val pw = new PrintWriter(new File(outFile ))
    val (nodes,edges) = iDotNode(qrySet,Set(),Set(),Set())
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
    //TODO: figure out how to use dot package


}
