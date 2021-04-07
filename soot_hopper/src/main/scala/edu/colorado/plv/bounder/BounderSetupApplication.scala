package edu.colorado.plv.bounder

import java.io.{File, FileOutputStream}

import edu.colorado.plv.bounder.symbolicexecutor.{CallGraphSource, FlowdroidCallGraph, FrameworkExtensions, PatchedFlowdroidCallGraph}
import javax.tools.{JavaCompiler, ToolProvider}
import soot.jimple.infoflow.InfoflowConfiguration.{AliasingAlgorithm, CallgraphAlgorithm, CodeEliminationMode}
import soot.jimple.infoflow.android.{InfoflowAndroidConfiguration, SetupApplication}
import soot.jimple.infoflow.android.callbacks.{AndroidCallbackDefinition, DefaultCallbackAnalyzer}
import soot.jimple.infoflow.android.callbacks.filters.{AlienHostComponentFilter, ApplicationCallbackFilter, UnreachableConstructorFilter}
import soot.jimple.infoflow.android.entryPointCreators.AndroidEntryPointCreator
import soot.jimple.infoflow.android.manifest.ProcessManifest
import soot.jimple.infoflow.android.resources.{ARSCFileParser, LayoutFileParser}
import soot.jimple.toolkits.callgraph.CHATransformer
import soot.{G, Main, PackManager, Scene, SootClass, SootMethod}
import soot.options.Options

import scala.jdk.CollectionConverters._

object BounderSetupApplication {
  def reset():Unit = {
    G.reset()
  }

  val androidHome = sys.env("ANDROID_HOME")

  /**
   * TODO: implement this
   * A method to compile and load a class into the soot scene so unit
   * tests can be written without the full android compile process.
   * @param path path to .java file
   */
  def loadClass(path:String): Unit ={

    val comp: JavaCompiler = ToolProvider.getSystemJavaCompiler
    val tmpfile = new FileOutputStream("/Users/shawnmeier/Desktop/Test.class")
    val res = comp.run(null, tmpfile, null, path)

    // load class
    import java.net.MalformedURLException
    import java.net.URLClassLoader
    // Create a File object on the root of the directory containing the class file// Create a File object on the root of the directory containing the class file

    val file = new File("c:\\myclasses\\")

    try { // Convert File to a URL
      val url = file.toURI.toURL // file:/c:/myclasses/
      val urls = Array(url)
      // Create a new class loader with the directory
      val cl = new URLClassLoader(urls)
      // Load in the class; MyClass.class should be located in
      // the directory file:/c:/myclasses/com/mycompany
      val cls = cl.loadClass("com.mycompany.MyClass")
    } catch {
      case e: MalformedURLException =>

      case e: ClassNotFoundException =>

    }

//    Scene.v().loadClass("Test",1)
    Scene.v().addBasicClass("Test")
    val testclass =
      Scene.v().getClasses().asScala.filter(a => a.getName == "Test")
    println(testclass)

    println()
    ???
  }

  def loadApk(path:String, callGraph:CallGraphSource) : Unit = callGraph match{
    case PatchedFlowdroidCallGraph => loadApkFlowdroid(path)
    case FlowdroidCallGraph => loadApkFlowdroid(path)
    case _ => loadApkNonFlowdroid(path)
  }
  def loadApkFlowdroid(path:String) : Unit = {
    // Create call graph and pointer analysis with flowdroid main method
    val config = new InfoflowAndroidConfiguration
    val platformsDir = androidHome + "/platforms"
    config.getAnalysisFileConfig.setAndroidPlatformDir(platformsDir)
    config.getAnalysisFileConfig.setTargetAPKFile(path)
    // TODO: figure out how to load apk without generating flowdroid callgraph
    config.setCallgraphAlgorithm(CallgraphAlgorithm.VTA)
    config.setMergeDexFiles(true)
//    config.setAliasingAlgorithm(AliasingAlgorithm.PtsBased)
    config.setEnableLineNumbers(true)
    config.setExcludeSootLibraryClasses(false)
    config.setCodeEliminationMode(CodeEliminationMode.NoCodeElimination)
    config.setOneComponentAtATime(false)
    config.getSourceSinkConfig.setEnableLifecycleSources(true)
    val setup = new SetupApplication(config)
    G.reset()
    setup.constructCallgraph()
  }
  def loadApkNonFlowdroid(path : String):Unit ={
    G.reset()
    val platformsDir = androidHome + "/platforms"
    Options.v.set_allow_phantom_refs(true)
    //Options.v.set_output_format(1) //TODO: dbg output?
    Options.v.set_output_format(Options.output_format_none)

    //TODO: added from jpf example
    import soot.Scene
    import soot.SootClass
    Scene.v.addBasicClass("java.lang.System", SootClass.SIGNATURES)
    Scene.v.addBasicClass("java.lang.Thread", SootClass.SIGNATURES)
    Scene.v.addBasicClass("java.lang.ThreadGroup", SootClass.SIGNATURES)

    Scene.v.addBasicClass("java.lang.ClassLoader", SootClass.SIGNATURES)
    Scene.v.addBasicClass("java.security.PrivilegedActionException", SootClass.SIGNATURES)
    Scene.v.addBasicClass("java.lang.ref.Finalizer", SootClass.SIGNATURES)
//    val excludedList = FrameworkExtensions.extensionStrings
//    Options.v().set_exclude(excludedList.asJava)
    Options.v().set_no_bodies_for_excluded(true)
    Options.v.set_whole_program(true)
    Options.v.set_process_dir(List(path).asJava)
    Options.v.set_android_jars(platformsDir)
    Options.v.set_src_prec(Options.src_prec_apk_class_jimple)
    Options.v.set_keep_offset(false) //don't create tag that holds bytecode offset
    Options.v.set_keep_line_number(true)
    Options.v.set_throw_analysis(Options.throw_analysis_dalvik)
    Options.v.set_process_multiple_dex(true)
    Options.v.set_ignore_resolution_errors(true) //TODO: what does this do?
//    Options.v.setPhaseOption("jb", "use-original-names:true")
    val classpath = s"${platformsDir}/android-26/android.jar"
    //TODO: construct classpath
    Options.v.set_soot_classpath(classpath)
    Main.v.autoSetOptions()
//    Options.v.setPhaseOption("cg.cha", "on")
    Scene.v.loadBasicClasses()
    Scene.v.loadNecessaryClasses()
    PackManager.v.getPack("wjpp").apply()
    PackManager.v.runPacks()
//    CHATransformer.v().transform()
//    Packmanager.v().runPacks()

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
    Scene.v().loadBasicClasses()
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
