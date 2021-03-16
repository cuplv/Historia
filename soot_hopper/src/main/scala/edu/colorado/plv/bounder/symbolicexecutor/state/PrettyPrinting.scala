package edu.colorado.plv.bounder.symbolicexecutor.state

import better.files.Dsl.SymbolicOperations
import better.files.File
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.ir.{AppLoc, CmdWrapper, IRWrapper, Loc}
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, SymbolicExecutorConfig}

import scala.io.Source

class PrettyPrinting(mode : OutputMode = MemoryOutputMode$) {
  implicit val thisMode = mode
  val outDir = sys.env.get("OUT_DIR")

  val templateFile = getClass.getResource("/pageTemplate.html").getPath
  val template = Source.fromFile(templateFile).getLines().mkString
  def qryString(q : Qry):String = q match{
    case SomeQry(state,loc) =>
      loc.toString +
        "\n       state: " + state.toString.replaceAll("\n"," ")
    case BottomQry(state,loc) =>
      "REFUTED: " + loc.toString +
        "\n       state: " + state.toString.replaceAll("\n"," ")
    case WitnessedQry(state,loc) =>
      "WITNESSED: " + loc.toString +
        "\n       state: " + state.toString.replaceAll("\n"," ")
  }
  def witnessToTrace(pn:Option[IPathNode]):List[String] = pn match{
    case Some(p@PathNode(q, _)) =>
      qryString(q) :: witnessToTrace(p.succ)
    case None => Nil
    case v =>
      println(v)
      ???
  }
  def printTraces(result: Set[IPathNode], outFile: String): Unit = {
    val pw = File(outFile)
    val live = result.flatMap{
      case pn@PathNode(_: SomeQry, false) => Some(("live",pn))
      case pn@PathNode(_ :WitnessedQry, _) => Some(("witnessed", pn))
      case pn@PathNode(_:BottomQry, false) => Some(("refuted",pn))
      case pn@PathNode(_:SomeQry, true) => Some((s"subsumed by:\n -- ${qryString(pn.qry)}\n", pn))
      case _ => None
    }
    val traces = live.map(a => a._1 + "\n    " + witnessToTrace(Some(a._2)).mkString("\n    ")).mkString("\n")
    if(pw.exists()) pw.delete()
    pw.createFile()
      .append(traces)
  }

  private def sanitizeStringForDot(str:String):String =
    str.replace(">","\\>")
      .replace("<","\\<")
      .replace("-","\\-")
      .replace("\"","\\\"").replace("|","\\|")
  private def iDotNode(qrySet:Set[IPathNode],seen:Set[IPathNode],
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
  def dotWitTree(qrySet : Set[IPathNode], outFile:String, includeSubsEdges:Boolean) = {
    val pw = File(s"${outDir.get}/$outFile" )
    val (nodes,edges) = iDotNode(qrySet,Set(),Set(),Set(), includeSubsEdges)
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
      .map((v: AppLoc) => resolver.cmdAtLocationNopIfUnknown(v).mkPre)
    val outf = File(outDir.get) / outFile
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
            s"""n$ind [label="ENTRY: ${sanitizeStringForDot(cmd.toString)}"]"""
          case (cmd,ind) => s"""n$ind [label="${sanitizeStringForDot(cmd.toString)}"]"""
        }.toSet
      }
      def getEdges:Set[String] = {
        edges.map{case (src,tgt) => s"""n$src -> n$tgt"""}
      }
    }

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

  def printWitnessOrProof(qrySet : Set[IPathNode], outFile:String, includeSubsEdges:Boolean = false) =
    qrySet.find(_.qry.isInstanceOf[WitnessedQry]) match{
      case Some(v) => dotWitTree(Set(v), outFile, includeSubsEdges)
      case None => dotWitTree(qrySet, outFile, includeSubsEdges)
    }

  /**
   * Output debug info of proof witness or timeout
   * @param qrySet generated by symbolic executor
   * @param fileName base name of output files
   * @param outDir2 override env variable out
   */
  def dumpDebugInfo(qrySet:Set[IPathNode],fileName: String, outDir2 : Option[String] = None):Unit = {
    val outDir3 = if(outDir2.isDefined) outDir2 else outDir
    outDir3 match{
      case Some(baseDir) =>
        val fname = s"$baseDir/$fileName"
        // printWitnessOrProof(qrySet, s"$fname.dot")

        printTraces(qrySet.filter{
          case PathNode(_:WitnessedQry, false) => true
          case _ => false
        }, s"$fname.witnesses")
        printTraces(qrySet.filter{
          case PathNode(_:BottomQry, false) => true
          case _ => false
        }, s"$fname.refuted")
        printTraces(qrySet.filter{
          case PathNode(_, true) => true
          case _ => false
        }, s"$fname.subsumed")
        printTraces(qrySet.filter{
          case PathNode(_:SomeQry, false) => true
          case _ => false
        }, s"$fname.live")
      case None =>
    }

  }
}
