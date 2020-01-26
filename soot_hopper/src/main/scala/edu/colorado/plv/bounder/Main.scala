package edu.colorado.plv.bounder

import soot.{G, Scene}
import soot.options.Options

import scala.jdk.CollectionConverters._

object Main {

  val androidHome = sys.env("ANDROID_HOME")
  def loadApk(path : String): Unit = {
    G.reset()

    Options.v().set_src_prec(Options.src_prec_apk_class_jimple)
    Options.v().set_whole_program(true)
    Options.v.set_allow_phantom_refs(true)
//    Options.v().setPhaseOption("cg.spark", "on")
    val platformsDir = androidHome + "/platforms"
    Options.v().set_android_jars(platformsDir)
    Options.v().set_process_dir(List(path).asJava)
    Options.v.set_keep_line_number(true)
    Options.v.set_throw_analysis(Options.throw_analysis_dalvik)
    Options.v.set_process_multiple_dex(true)
    // Ignore resolutionn errors, does not appear to work?
//    Options.v.set_ignore_resolution_errors(true)

    Scene.v().loadNecessaryClasses()
//    val cg = Scene.v().getCallGraph
//    val classes = Scene.v().getClasses

  }

}
