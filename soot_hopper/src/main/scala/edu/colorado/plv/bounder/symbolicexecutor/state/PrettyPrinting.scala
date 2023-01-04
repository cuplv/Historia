package edu.colorado.plv.bounder.symbolicexecutor.state

import better.files.Dsl.SymbolicOperations
import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppLoc, CallbackMethodInvoke, CallbackMethodReturn, CallinMethodInvoke, CallinMethodReturn, CmdWrapper, GroupedCallinMethodInvoke, GroupedCallinMethodReturn, IRWrapper, InternalMethodInvoke, InternalMethodReturn, LineLoc, Loc, SkippedInternalMethodInvoke, SkippedInternalMethodReturn}
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, ExecutorConfig}
import org.apache.log4j.{EnhancedPatternLayout, PatternLayout}
import soot.JastAddJ.JastAddJavaParser.Terminals

import scala.annotation.tailrec
import scala.io.Source

object PrettyPrinting {
  def printWitness(terminals: Set[IPathNode]):Unit = {
    var witFound = false
    terminals.foreach(n => n.qry match {
      case Qry(_, _, WitnessedQry(explanation)) =>
        witFound = true
        println("Witness")
        println(explanation)
      case _ => false
    })
    if(!witFound){
      println("No witnesses found")
    }
  }


  //  implicit val thisMode = mode
  val envOutDir = sys.env.get("OUT_DIR")

//  val templateFile = getClass.getResource("/pageTemplate.html").getPath
//  val template = Source.fromFile(templateFile).getLines().mkString
  def qryString(q : Qry):String = q match{
    case Qry(state,loc, Live) =>
      loc.toString +
        "\n       state: " + state.toString.replaceAll("\n"," ")
    case Qry(state,loc, BottomQry) =>
      "REFUTED: " + loc.toString +
        "\n       state: " + state.toString.replaceAll("\n"," ")
    case Qry(state,loc,WitnessedQry(witness)) =>
      "WITNESSED: " + loc.toString +
        "\n       state: " + state.toString.replaceAll("\n"," ")
    case Qry(state, loc, Unknown) =>
      "UNK: " + loc.toString +
      "\n       state: " + state.toString.replaceAll("\n"," ")
}
  @tailrec
  final def witnessToTrace(pn:List[IPathNode],
                           truncate:Boolean,
                           acc:List[String] = List())
                          (implicit mode : OutputMode = MemoryOutputMode):List[String] = pn match{
    case (p@PathNode(q, _))::t =>
      val branch = if(t.nonEmpty) " -- branch" else ""
      lazy val isMethodLoc = q.loc.isEntry.isDefined
      lazy val succSame = p.succ.exists(next => next.qry.state.sf != q.state.sf)
      // Only print path nodes that are method entry/exit or where the state differs
      if (!truncate || isMethodLoc || succSame)
        witnessToTrace(p.succ,truncate, qryString(q) + branch::acc)
      else
        witnessToTrace(p.succ,truncate, acc)
    case Nil => acc.reverse
    case v =>
      println(v)
      ???
  }

  def nodeToWitness(nodes:List[IPathNode], truncate:Boolean)(implicit mode : OutputMode):List[List[String]] = {

    val targetTraces: List[(String, IPathNode)] = nodes.flatMap{
      case pn@PathNode(Qry(_,_,q@Live), false) => Some((q.toString +
        s"${if(pn.getError.isDefined) pn.getError.get.toString else ""}",pn))
      case pn@PathNode(Qry(_,_,Live), true) => Some((s"subsumed by:\n -- ${qryString(pn.subsumed.head.qry)}\n", pn))
      case pn@PathNode(Qry(_,_,q:WitnessedQry), _) => Some((q.toString, pn))
      case pn@PathNode(Qry(_,_,q@BottomQry), false) => Some((q.toString,pn))
      case _ => None
    }

    targetTraces.map{
      case (k,v) => k::witnessToTrace(List(v), truncate = truncate)
    }
  }

  def printTraces(result: Set[IPathNode],
                  outFile: String,
                  truncate:Boolean)(implicit mode : OutputMode = MemoryOutputMode): Unit = {
    val pw = File(outFile)
    val targetTraces: List[(String, IPathNode)] = result.flatMap{
      case pn@PathNode(Qry(_,_,Live), true) => Some((s"subsumed by:\n -- ${qryString(pn.subsumed.head.qry)}\n", pn))
      case pn@PathNode(Qry(_,_,q@Live), false) => Some((q.toString +
        s"${if(pn.getError.isDefined) pn.getError.get.toString else ""}",pn))
      case pn@PathNode(Qry(_,_,q@WitnessedQry(_)), _) => Some((q.toString, pn))
      case pn@PathNode(Qry(_,_,q@BottomQry), false) => Some((q.toString,pn))
      case _ => None
    }.toList

    if(pw.exists()) pw.delete()
    pw.createFile()
    val sortedTraces = targetTraces.sortBy(tr => tr._2.depth)
    sortedTraces.zipWithIndex.foreach{case (a,ind) =>
      println(s"Writing trace $ind / ${targetTraces.size}, length: ${a._2.depth}")
      pw.append(a._1 + "\n    " + witnessToTrace(List(a._2),truncate).mkString("\n    "))
      pw.append("\n")
    }
//      .append(traces)
  }

  private def sanitizeStringForDot(str:String):String =
    str.replace(">","\\>")
      .replace("<","\\<")
      .replace("-","\\-")
      .replace("\"","\\\"").replace("|","\\|")
  private def iDotNode(qrySet:Set[PrintingPathNode],seen:Set[IPathNode],
                       procNodes:Set[String],procEdges:Set[String],
                       includeSubsEdges:Boolean)
                      (implicit mode : OutputMode = MemoryOutputMode):(Set[String],Set[String]) = {
    if(qrySet.isEmpty){
      (procNodes,procEdges)
    }else {
      val cur = qrySet.head
      val rest = cur.succ match{
        case None => qrySet.tail
        case Some(v) => qrySet.tail + v
      }
      val curString = sanitizeStringForDot(cur.str)

      val init = if(cur.succ.isDefined) "" else "INITIAL: "
      val subs = if(cur.pn.subsumed.nonEmpty)"SUBSUMED: " else ""
      val nextProcNodes = procNodes + s"""n${System.identityHashCode(cur.pn)} [label="${init}${subs}${curString}"]"""
      // TODO: add subsumption edges
      // TODO: add subsumption labels
      val nextProcEdges = cur.succ match {
        case Some(v) =>
          assert(v.pn.subsumed.isEmpty)
          procEdges + s"""n${System.identityHashCode(cur.pn)} -> n${System.identityHashCode(v.pn)}"""
        case None => procEdges
      }
      val subsumedEdges =
        if (includeSubsEdges)cur.pn.subsumed.map(v =>
          s"\n    n${System.identityHashCode(v)}->n${System.identityHashCode(cur.pn)}").headOption.getOrElse("") else ""
      iDotNode(rest, seen + cur.pn, nextProcNodes, nextProcEdges + subsumedEdges, includeSubsEdges)
    }
  }
  case class PrintingPathNode(pn:IPathNode,  skip: IPathNode => Boolean,
                              prettyPrint:Qry => String = p => p.toString)
                             (implicit mode : OutputMode = MemoryOutputMode) {
    def succ:Option[PrintingPathNode] = {
      @tailrec
      def nextNode(pn:IPathNode):List[IPathNode] = {
        pn.succ match{
          case List(nextP) if skip(nextP) => nextNode(nextP)
          case v => v
        }
      }
      nextNode(pn).headOption.map(PrintingPathNode(_,skip))
    }
    def str:String = prettyPrint(pn.qry)
  }
  def dotWitTree(qrySet : Set[IPathNode], outFile:String, includeSubsEdges:Boolean, skipCmd:Boolean = false) = {
    val pw = File(s"${envOutDir.get}/$outFile" )
    val skipf: IPathNode => Boolean = p =>
      p.qry.loc match {
        case _:CallbackMethodInvoke => false
        case _:CallbackMethodReturn => false
        case _ => skipCmd
      }
    val printQry = qrySet.map(q => PrintingPathNode(q, skipf, p => p.toString))
    val (nodes,edges) = iDotNode(printQry,Set(),Set(),Set(), includeSubsEdges)
    if(pw.exists()) pw.delete()
    pw.createFile()
    pw.write(
      s"""
         |digraph D {
         |    node[shape=record];
         |    ${nodes.mkString("\n    ")}
         |
         |    ${edges.mkString("\n    ")}
         |}
         |""".stripMargin)
  }

  def dotMethod[M,C](loc : Loc, resolver:ControlFlowResolver[M,C], outFile:String): Unit = {
    val containingMethod = loc.containingMethod
    val w = resolver.getWrapper
    val rets: Set[CmdWrapper] = w.makeMethodRetuns(containingMethod.get).toSet
      .map((v: AppLoc) => BounderUtil.cmdAtLocationNopIfUnknown(v,w).mkPre)
    val outf = File(envOutDir.get) / outFile
    if(outf.exists()) outf.delete()
    case class NodesAndEdges(nodes: Map[CmdWrapper,Int], ind:Int, edges:Set[(Int,Int)] = Set()){
      def addEdge(src:CmdWrapper, tgt:CmdWrapper):NodesAndEdges = {
        assert(nodes.contains(tgt))
        val (newNodes,newInd) = if(nodes.contains(src)) (nodes,ind) else (nodes + (src -> ind), ind+1)
        val newEdges = edges.+((newNodes(src),newNodes(tgt)))
        NodesAndEdges(newNodes, newInd, newEdges)
      }
      def getNodes:Set[String] = {
        nodes.map{
          case (cmd,ind) if w.isMethodEntry(cmd) =>
            val line = cmd.getLoc.line.lineNumber
            s"""n$ind [label="ENTRY: line:$line top:${w.commandTopologicalOrder(cmd)} : ${sanitizeStringForDot(cmd.toString)}"]"""
          case (cmd,ind) =>
            val line = cmd.getLoc.line.lineNumber
            s"""n$ind [label="line:$line top:${w.commandTopologicalOrder(cmd)} : ${sanitizeStringForDot(cmd.toString)}"]"""
        }.toSet
      }
      def getEdges:Set[String] = {
        edges.map{case (src,tgt) => s"""n$src -> n$tgt"""}
      }
    }

    @tailrec
    def iter(acc: NodesAndEdges, worklist:Set[CmdWrapper],
             visited:Set[CmdWrapper] = Set()):NodesAndEdges = worklist match{
      case s if s.nonEmpty =>
        val h = s.head
        val pred = w.commandPredecessors(h).map(loc => w.cmdAtLocation(loc).mkPre).toSet
        val newAcc = pred.foldLeft(acc){case (acc2,v) => acc2.addEdge(v,h)}
        iter(newAcc, s.tail ++ (pred -- visited), visited + h)
      case _ => acc
    }
    val nodesAndEdges = iter(NodesAndEdges(rets.zipWithIndex.toMap, rets.size),rets)


    val nodes:Set[String] = nodesAndEdges.getNodes
    val edges: Set[String] = nodesAndEdges.getEdges
    outf.write(s"""
                  |digraph D {
                  |    node[shape=record];
                  |    ${nodes.mkString("\n    ")}
                  |
                  |    ${edges.mkString("\n    ")}
                  |}
                  |""".stripMargin
    )
  }

  /**
   * Output witness or proof as dot graph
   * @param qrySet
   * @param outFile
   * @param includeSubsEdges
   * @return
   */
  def printWitnessOrProof(qrySet : Set[IPathNode], outFile:String, includeSubsEdges:Boolean = false) =
    qrySet.find(_.qry.isWitnessed ) match{
      case Some(v) => dotWitTree(Set(v), outFile, includeSubsEdges)
      case None => dotWitTree(qrySet, outFile, includeSubsEdges)
    }

  /**
   * Output debug info of proof witness or timeout
   * @param qrySet generated by symbolic executor
   * @param fileName base name of output files
   * @param outDir override env variable out
   */
  def dumpDebugInfo(qrySet:Set[IPathNode],
                    fileName: String,
                    truncate:Boolean = true,
                    outDir : Option[String] = None)(implicit mode : OutputMode = MemoryOutputMode):Unit = {
    val outDir3 = if(outDir.isDefined) outDir else envOutDir
    outDir3 match{
      case Some(baseDir) =>
        val fname = s"$baseDir/$fileName"
        // printWitnessOrProof(qrySet, s"$fname.dot")

        printTraces(qrySet.filter{
          case PathNode(Qry(_,_,WitnessedQry(_)), false) => true
          case _ => false
        }, s"$fname.witnesses", truncate)
        printTraces(qrySet.filter{
          case PathNode(Qry(_,_,BottomQry), false) => true
          case _ => false
        }, s"$fname.refuted", truncate)
        printTraces(qrySet.filter{
          case PathNode(_, true) => true
          case _ => false
        }, s"$fname.subsumed", truncate)
        printTraces(qrySet.filter{
          case PathNode(Qry(_,_,Live), false) => true
          case _ => false
        }, s"$fname.live",truncate)
      case None =>
    }

  }

  def escapeForHtml(s:String):String = {
    s.replace("<","&lt;").replace(">","&gt;")
  }

  def nodeToHtml(node:IPathNode):String = escapeForHtml(node.toString)

  /**
   * Generate a html page to expand and search witness traces.
   * @param qrySet
   * @return
   */
  def treeToExpandableHTML(qrySet:Set[IPathNode]):String = {
    val html = new StringBuilder()
    html.append(
      """
        |<html>
        |<head>
        |<script src="https://ajax.googleapis.com/ajax/libs/jquery/3.3.1/jquery.min.js"></script>
        |<script>
        |$(document).ready(function(){
        |    $("button").click(function(){
        |        $(this).next().toggle();
        |    });
        |});
        |</script>
        |</head>
        |<body>
        |<h1>Witnesses</h1>
        |</body>
        |</html>
        |""".stripMargin)
    //TODO: better way to explore results.
    html.toString
  }


}
