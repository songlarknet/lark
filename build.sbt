scalaVersion := "3.1.2"
libraryDependencies += "org.scalactic" %% "scalactic" % "3.2.12"
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.12" % "test"

// No Scala 3 release; use 2.13 version
libraryDependencies += "com.regblanc" % "scala-smtlib_2.13" % "0.2.1-42-gc68dbaa"
