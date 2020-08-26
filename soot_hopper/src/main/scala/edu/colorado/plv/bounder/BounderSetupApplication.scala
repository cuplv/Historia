package edu.colorado.plv.bounder

import soot.jimple.infoflow.android.{InfoflowAndroidConfiguration, SetupApplication}
import soot.jimple.infoflow.android.callbacks.{AndroidCallbackDefinition, DefaultCallbackAnalyzer}
import soot.jimple.infoflow.android.callbacks.filters.{AlienHostComponentFilter, ApplicationCallbackFilter, UnreachableConstructorFilter}
import soot.jimple.infoflow.android.entryPointCreators.AndroidEntryPointCreator
import soot.jimple.infoflow.android.manifest.ProcessManifest
import soot.jimple.infoflow.android.resources.{ARSCFileParser, LayoutFileParser}
import soot.{G, PackManager, Scene, SootClass}
import soot.options.Options

import scala.jdk.CollectionConverters._

object BounderSetupApplication {

  val androidHome = sys.env("ANDROID_HOME")

  def loadApk(path:String) : Unit = {
    // Create call graph and pointer analysis with flowdroid main method
    val config = new InfoflowAndroidConfiguration
    val platformsDir = androidHome + "/platforms"
    config.getAnalysisFileConfig.setTargetAPKFile(path)
    config.getAnalysisFileConfig.setAndroidPlatformDir(platformsDir)
    val setup = new SetupApplication(config)
    G.reset()
//    setup.initializeSoot()

    // Hacky way of setting up call graph without running flowdroid
    val setupApplicationClass =
      Class.forName("soot.jimple.infoflow.android.SetupApplication")
    List("initializeSoot","parseAppResources").foreach(methodname => {
      val method = setupApplicationClass.getDeclaredMethod(methodname)
      method.setAccessible(true)
      method.invoke(setup)
    })
    Options.v.set_keep_line_number(true)
    val ssp = Class.forName("soot.jimple.infoflow.sourcesSinks.definitions.ISourceSinkDefinitionProvider")
    val calculateCallbacks =
      setupApplicationClass.getDeclaredMethod("calculateCallbacks",ssp)
    calculateCallbacks.setAccessible(true)
    calculateCallbacks.invoke(setup,null)
    val scc = Class.forName("soot.SootClass")
    val createMainMethod =
      setupApplicationClass.getDeclaredMethod("createMainMethod", scc)
    createMainMethod.setAccessible(true)
    createMainMethod.invoke(setup,null)

    val constructCg =
      setupApplicationClass.getDeclaredMethod("constructCallgraphInternal")
    constructCg.setAccessible(true)
    constructCg.invoke(setup)
  }
  def loadApkOld(path : String): Unit = {
    G.reset()
    Scene.v.releaseCallGraph()
    Scene.v.releasePointsToAnalysis()
    Scene.v.releaseReachableMethods()
    G.v.resetSpark()

    Options.v().set_src_prec(Options.src_prec_apk_class_jimple)
    Options.v().set_whole_program(true)
    Options.v.set_allow_phantom_refs(true)
    Options.v().setPhaseOption("cg.spark", "on")
    val platformsDir = androidHome + "/platforms"
    Options.v().set_android_jars(platformsDir)
    Options.v().set_process_dir(List(path).asJava)
    Options.v.set_keep_line_number(true)
    Options.v.set_throw_analysis(Options.throw_analysis_dalvik)
    Options.v.set_process_multiple_dex(true)
    // Ignore resolutionn errors, does not appear to work?
//    Options.v.set_ignore_resolution_errors(true)
    Scene.v().loadNecessaryClasses()
    val manifest = new ProcessManifest(path)
    val entryPoints = manifest.getEntryPointClasses.asScala.flatMap(epName => {
      val sootClass = Scene.v().getSootClassUnsafe(epName)
      if (sootClass == null) None else Some(sootClass)
    })
    val resources = new ARSCFileParser();
    resources.parse(path)

    val layoutFileParser = new LayoutFileParser(manifest.getPackageName, resources)
    val config = new InfoflowAndroidConfiguration
    config.getAnalysisFileConfig.setTargetAPKFile(path)
    config.getAnalysisFileConfig.setAndroidPlatformDir(platformsDir)
    val callbackAnalyzer = new DefaultCallbackAnalyzer(config, entryPoints.asJava,"AndroidCallbacks.txt")

    // Prevent inner classes of components from being callbacks associated with other components
    callbackAnalyzer.addCallbackFilter(new AlienHostComponentFilter(entryPoints.asJava))

    // Restrict to application callbacks
    callbackAnalyzer.addCallbackFilter(new ApplicationCallbackFilter(entryPoints.asJava))

    // Filter out objects with no factory method or allocation site
    callbackAnalyzer.addCallbackFilter(new UnreachableConstructorFilter)

    callbackAnalyzer.collectCallbackMethods()

    layoutFileParser.parseLayoutFile(path)

    //Note: This function works but does not find the entry points, use the loadApk to call
    // flowdroid's main method creation

    //Below is a hacky way I was trying to do the same thing, but it got too tedious
//    var callbackMethods = collection.mutable.Map[SootClass, AndroidCallbackDefinition]()
//    var entrypointsMut = collection.mutable.Set[SootClass]()
//    var done = false
//    while(done){
//      val entryPointCreator = new AndroidEntryPointCreator(manifest, entryPoints.asJava)
//      callbackAnalyzer.getCallbackMethods.asScala.foreach(a => callbackMethods.put(a.getO1,a.getO2))
//      callbackAnalyzer.getDynamicManifestComponents
//      println(callbackMethods)
//      done = true
//    }

    PackManager.v.getPack("cg").apply()
    Scene.v.getOrMakeFastHierarchy
//    val cg = Scene.v().getCallGraph
//    val classes = Scene.v().getClasses

  }

}
