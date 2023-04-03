
name := "soot_hopper"
organization := "edu.colorado.plv.bounder"
version := "0.1"
mainClass in (Compile, run) := Some("edu.colorado.plv.bounder.Driver")
scalaVersion := "2.13.8"


resolvers += "Maven Central Server" at "https://repo1.maven.org/maven2"

resolvers += "Typesafe Server" at "https://repo.typesafe.com/typesafe/releases"

//unmanagedJars in Compile += baseDirectory.value / "lib/soot-infoflow-cmd-jar-with-dependencies.jar"
unmanagedJars in Compile += baseDirectory.value / "lib/com.microsoft.z3.jar"
libraryDependencies += "ca.mcgill.sable" % "soot" % "4.1.0"

//libraryDependencies += "com.fasterxml.jackson.core" % "jackson-core" % "2.7.9" % "compile"
//libraryDependencies += "org.scala-graph" %% "graph-core" % "1.13.2" % "compile"
//libraryDependencies += "org.scala-graph" %% "graph-dot" % "1.13.0" % "compile"
//libraryDependencies += "org.postgresql" % "postgresql" % "9.3-1100-jdbc4"
libraryDependencies += "com.github.scopt" % "scopt_2.13" % "4.0.0-RC2" % "compile"
libraryDependencies += "org.postgresql" % "postgresql" % "42.2.19"
libraryDependencies += "org.scala-lang.modules" % "scala-parallel-collections_2.13" % "1.0.0" % "compile"
libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.2"
libraryDependencies += "org.scalatest" %% "scalatest-funsuite" % "3.2.2" % Test
libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.3.3" %"compile"
//libraryDependencies += "com.lihaoyi" %% "upickle" % "0.9.5"
libraryDependencies += "com.lihaoyi" % "upickle_2.13" % "1.3.0"
libraryDependencies += "com.github.pathikrit" % "better-files_2.13" % "3.9.1"
// note: another lib that does file i/o but also does processes: https://github.com/com-lihaoyi/os-lib
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.1.2"
libraryDependencies += "com.typesafe.slick" % "slick_2.13" % "3.3.3"
libraryDependencies += "org.xerial" % "sqlite-jdbc" % "3.34.0"
libraryDependencies += "com.h2database" % "h2" % "1.4.187"
libraryDependencies += "de.learnlib.distribution" % "learnlib-distribution" % "0.16.0"
libraryDependencies += "net.automatalib.distribution" % "automata-distribution" % "0.10.0"
libraryDependencies += "com.regblanc" %% "scala-smtlib" % "0.2.1-42-gc68dbaa"
libraryDependencies += "io.github.andrebeat" %% "scala-pool" % "0.4.3"
// libraryDependencies += "org.apache.spark" % "spark-core_2.13" % "3.3.1"


libraryDependencies ++= {
  Seq("org.slf4j" % "slf4j-log4j12" % "1.7.30")
}.map(_.force())

//// Clear out Flowdroid logger so that ours actually logs things
mappings in (Compile,packageBin) ~= { (ms: Seq[(File, String)]) =>
  ms filter { case (file, toPath) =>
    println(file)
    toPath != "org/slf4j/impl/StaticLoggerBinder.class"
  }
}

mappings in (Test,packageBin) ~= { (ms: Seq[(File, String)]) =>
  ms filter { case (file, toPath) =>
    toPath != "org/slf4j/impl/StaticLoggerBinder.class"
  }
}

Compile / resourceDirectory := baseDirectory.value / "src" / "main" / "resources"

//Compile / unmanagedResourceDirectories += baseDirectory.value / "src/main/resources"
//Test / unmanagedResourceDirectories += baseDirectory.value / "src/main/resources"
// uncomment below if parallel tests become a problem
parallelExecution in Test := false
javaOptions += "-Xmx15G"

//lazy val configTest = settingKey[String]("example")

//configTest := baseDirectory.value.toString()
import sbt.Package.ManifestAttributes
import com.typesafe.sbt.SbtGit.git
packageOptions := Seq(ManifestAttributes(("Repository-Commit", git.gitHeadCommit.value.get)))
// ignore unit tests when assembling fat jar
test in assembly := {}

// ignore duplicate slf4j during assembly of fat jar
assemblyMergeStrategy in assembly := {
  case PathList("META-INF", xs @ _*) => MergeStrategy.discard
  case x => MergeStrategy.first
}

mainClass in assembly := Some("edu.colorado.plv.bounder.Driver")
//unmanagedResources in Compile := Seq() //we don't want to add resources from "src/main/resources" to inner jar

//mappings in assembly += (file("src/main/resources/filename.json"),"path/to/resource/in/onejar")

//notes: use "sbt assembly" to create fat jar