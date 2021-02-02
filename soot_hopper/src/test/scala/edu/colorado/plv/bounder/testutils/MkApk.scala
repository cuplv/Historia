package edu.colorado.plv.bounder.testutils

import edu.colorado.plv.bounder.testutils.MkApk.makeApkWithSources
import org.scalatest.funsuite.AnyFunSuite
import better.files._
import edu.colorado.plv.bounder.BounderUtil
import edu.colorado.plv.bounder.BounderUtil.Proven
import edu.colorado.plv.bounder.ir.JimpleFlowdroidWrapper
import edu.colorado.plv.bounder.lifestate.{ActivityLifecycle, FragmentGetActivityNullSpec, RxJavaSpec, SpecSpace}
import edu.colorado.plv.bounder.symbolicexecutor.state.{PrettyPrinting, Qry}
import edu.colorado.plv.bounder.symbolicexecutor.{CHACallGraph, SymbolicExecutorConfig, TransferFunctions}
import soot.{Scene, SootMethod}

import scala.jdk.CollectionConverters.CollectionHasAsScala
import sys.process._
//import scala.language.postfixOps
object MkApk {
  val RXBase = getClass.getResource("/CreateDestroySubscribe.zip").getPath

  /**
   *
   * @param sources map from file name to source contents
   * @param targetProject tar.gz of project to add test file
   * @param applyWithApk operation to perform on apk
   * @return result of applyWithApk
   */
  def makeApkWithSources[U](sources: Map[String,String], targetProject: String, applyWithApk: String => U):Option[U] ={
    var res:Option[U] = None
    File.usingTemporaryDirectory(){(dir:File) =>
      val baseFile = File(targetProject)
//      val copiedBase = baseFile.copyToDirectory(dir)
      val unZip = Dsl.unzip(baseFile)(dir)
      val appDir: File = dir / "CreateDestroySubscribe"
      val srcDir =
        appDir / "app" / "src" / "main" / "java" / "com" / "example" / "createdestroy"

      sources.map{
        case (filename,v) =>
          (srcDir / filename).appendLines(v)
      }

      val gw = appDir / "gradlew"
      val res1 = Process("chmod +x gradlew",appDir.toJava).!!
      val res2 = Process("./gradlew assembleDebug",appDir.toJava).!!
      val apkFile = appDir / "app" / "build" / "outputs/apk/debug/app-debug.apk"
      res = Some(applyWithApk(apkFile.toString))
    }
    res
  }
}