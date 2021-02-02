
name := "soot_hopper"
organization := "edu.colorado.plv.bounder"
version := "0.1"
mainClass in (Compile, run) := Some("edu.colorado.plv.bounder.Driver")
scalaVersion := "2.13.1"
unmanagedJars in Compile += baseDirectory.value / "lib/soot-infoflow-cmd-jar-with-dependencies.jar"
unmanagedJars in Compile += baseDirectory.value / "lib/com.microsoft.z3.jar"
//libraryDependencies += "ca.mcgill.sable" % "soot" % "4.1.0"

libraryDependencies += "org.slf4j" % "slf4j-simple" % "1.7.5" % "compile"
libraryDependencies += "com.fasterxml.jackson.core" % "jackson-core" % "2.7.9" % "compile"
libraryDependencies += "org.scala-graph" %% "graph-core" % "1.13.2" % "compile"
libraryDependencies += "org.scala-graph" %% "graph-dot" % "1.13.0" % "compile"
libraryDependencies += "com.github.scopt" % "scopt_2.13" % "4.0.0-RC2" % "compile"
libraryDependencies += "org.scala-lang.modules" % "scala-parallel-collections_2.13" % "1.0.0" % "compile"
libraryDependencies += "org.scalatest" %% "scalatest-funsuite" % "3.2.2" % "test"
libraryDependencies += "org.scalaz" %% "scalaz-core" % "7.3.3" %"compile"
libraryDependencies += "com.lihaoyi" %% "upickle" % "0.9.5"
libraryDependencies += "com.github.pathikrit" % "better-files_2.13" % "3.9.1"


Compile / unmanagedResourceDirectories += baseDirectory.value / "src/main/resources"
Test / unmanagedResourceDirectories += baseDirectory.value / "src/main/resources"


//libraryDependencies += "com.regblanc" %% "scala-smtlib" % "0.2.2"

//envVars in run := Map("DYLD_LIBRARY_PATH" -> System.getenv("Z3_LIB"))
//unmanagedBase := Seq(
//  baseDirectory.value / "lib/com.microsoft.z3.jar",
//  baseDirectory.value / "lib/soot-infoflow-cmd-jar-with-dependencies.jar")

