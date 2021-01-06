import scala._

name := "soot_hopper"
organization := "edu.colorado.plv.bounder"
version := "0.1"
mainClass in (Compile, run) := Some("edu.colorado.plv.bounder.Driver")
scalaVersion := "2.13.1"
unmanagedJars in Compile += baseDirectory.value / "lib/soot-infoflow-cmd-jar-with-dependencies.jar"
unmanagedJars in Compile += baseDirectory.value / "lib/com.microsoft.z3.jar"
libraryDependencies += "ca.mcgill.sable" % "soot" % "3.3.0"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.1.0" % "test"
libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.5"
libraryDependencies += "com.fasterxml.jackson.core" % "jackson-core" % "2.7.9"
libraryDependencies += "org.scala-graph" %% "graph-core" % "1.13.2"
// https://mvnrepository.com/artifact/org.scala-graph/graph-dot
libraryDependencies += "org.scala-graph" %% "graph-dot" % "1.13.0"
libraryDependencies += "com.github.scopt" % "scopt_2.13" % "4.0.0-RC2"

//libraryDependencies += "com.regblanc" %% "scala-smtlib" % "0.2.2"

envVars in run := Map("DYLD_LIBRARY_PATH" -> System.getenv("Z3_LIB"))
//unmanagedBase := Seq(
//  baseDirectory.value / "lib/com.microsoft.z3.jar",
//  baseDirectory.value / "lib/soot-infoflow-cmd-jar-with-dependencies.jar")

