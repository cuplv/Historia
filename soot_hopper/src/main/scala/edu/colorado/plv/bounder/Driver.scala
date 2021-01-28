package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, NI}
import edu.colorado.plv.bounder.lifestate.{SpecSignatures, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, FlowdroidCallGraph, SymbolicExecutor, SymbolicExecutorConfig, TransferFunctions}
import edu.colorado.plv.bounder.symbolicexecutor.state.{PathNode, PrettyPrinting, Qry}
import scopt.OParser
import soot.SootMethod

object Driver {
  sealed trait RunMode
  case object DotWitnessTree extends RunMode
  case object Default extends RunMode

  case class Config(mode:RunMode = Default,
                   apkPath:String = "",
                   outFolder:Option[String] = None
                   )

  def main(args: Array[String]): Unit = {
    val builder = OParser.builder[Config]
    val parser = {
      import builder._
      OParser.sequence(
        programName("Bounder"),
        opt[String]('m',"mode").required().text("run mode [dottree, ...]").action{
          case ("dottree",c) => c.copy(mode = DotWitnessTree)
        },
        opt[String]('a', "apkFile").required().text("Compiled Android application").action{
          case (v,c) => c.copy(apkPath = v)
        },
        opt[String]('o', "outFolder").text("folder to output analysis artifacts").action{
          case (v,c) => c.copy(outFolder = Some(v))
        }

      )
    }
    OParser.parse(parser, args, Config()) match {
      case Some(Config(DotWitnessTree, apkPath, Some(outFolder))) => dotWitnessTree(apkPath, outFolder)
      case _ => throw new IllegalArgumentException("Argument parsing failed")
    }
  }

  def dotWitnessTree(apkPath: String, outFolder: String): Unit = {
    val callGraph = FlowdroidCallGraph
    val w = new JimpleFlowdroidWrapper(apkPath, callGraph)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
//    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val testSpec = LSSpec(NI(SpecSignatures.Activity_onResume_entry, SpecSignatures.Activity_onPause_exit),
      SpecSignatures.Activity_onPause_entry) // TODO: fill in spec details for test
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set(testSpec)))
    val config = SymbolicExecutorConfig(
      stepLimit = Some(30), w,transfer, component = None)
    val symbolicExecutor = config.getSymbolicExecutor
    val query = Qry.makeReceiverNonNull(symbolicExecutor, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    val outname = apkPath.split("/").last
    PrettyPrinting.dotWitTree(result, s"${outFolder}/${outname}.dot",false)
  }
}
