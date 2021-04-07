package edu.colorado.plv.bounder.testutils

import better.files._
import edu.colorado.plv.bounder.solver.StateSolver
import org.slf4j.LoggerFactory

import sys.process._

object MkApk {

  private val logger = LoggerFactory.getLogger("MkApk.scala")
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

      try {
        val res1 = Process("chmod +x gradlew", appDir.toJava).!!
        logger.info(s"Chmod output: $res1")
        import sys.process._

        val stdout = new StringBuilder
        val stderr = new StringBuilder
//        val status = "ls -al FRED" ! ProcessLogger(stdout append _, stderr append _)
        Process("./gradlew assembleDebug", appDir.toJava) ! ProcessLogger(v => stdout.append(v + "\n"),
          v => stderr.append(v + "\n"))
        logger.info(s"Gradle stdout: $stdout")
        logger.info(s"Gradle stderr: $stderr")
        val apkFile = appDir / "app" / "build" / "outputs/apk/debug/app-debug.apk"
        res = Some(applyWithApk(apkFile.toString))
      }catch{
        case e:RuntimeException =>
          logger.error("FAILED BUILDING TEST APK")
          logger.error(e.toString)
          logger.error(e.getStackTrace.mkString("\n    "))
          throw e
      }
    }
    res
  }
}