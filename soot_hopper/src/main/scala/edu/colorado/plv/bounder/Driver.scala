package edu.colorado.plv.bounder

import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.LifeState.{LSSpec, NI}
import edu.colorado.plv.bounder.lifestate.{SpecSpace, TestSignatures}
import edu.colorado.plv.bounder.symbolicexecutor.{ControlFlowResolver, DefaultAppCodeResolver, SymbolicExecutor, SymbolicExecutorConfig, TransferFunctions}
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
      case Config(DotWitnessTree, apkPath, Some(outFolder)) => dotWitnessTree(apkPath, outFolder)
      case _ => throw new IllegalArgumentException("Argument parsing failed")
    }
  }

  def dotWitnessTree(apkPath: String, outFolder: String): Unit = {

    val w = new JimpleFlowdroidWrapper(apkPath)
    val a = new DefaultAppCodeResolver[SootMethod, soot.Unit](w)
    val resolver = new ControlFlowResolver[SootMethod, soot.Unit](w, a)
    val testSpec = LSSpec(NI(TestSignatures.Activity_onResume_entry, TestSignatures.Activity_onPause_exit),
      TestSignatures.Activity_onPause_entry) // TODO: fill in spec details for test
    val transfer = new TransferFunctions[SootMethod,soot.Unit](w, new SpecSpace(Set(testSpec)))
    val config = SymbolicExecutorConfig(
      stepLimit = Some(30), w,resolver,transfer)
    val query = Qry.makeReceiverNonNull(config, w,
      "com.example.test_interproc_2.MainActivity",
      "void onPause()",27)
    val symbolicExecutor = new SymbolicExecutor[SootMethod, soot.Unit](config)
    val result: Set[PathNode] = symbolicExecutor.executeBackward(query)
    //TODO: deref not proven, figure out what is going on
    PrettyPrinting.dotWitTree(result, outFolder)
  }
}
