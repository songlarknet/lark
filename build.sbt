scalaVersion := "3.2.2"

/////////////////// Fundamental dependencies
// SMTlib: used for interfacing with SMT solvers
// No Scala 3 release; use 2.13 version
libraryDependencies += "com.regblanc" % "scala-smtlib_2.13" % "0.2.1-42-gc68dbaa"

// Kiama: used for pretty-printing
libraryDependencies += "org.bitbucket.inkytonik.kiama" %% "kiama" % "2.5.0"

/////////////////// Test dependencies
// Hedgehog: used for property tests
val hedgehogVersion = "0.9.0"

libraryDependencies ++= Seq(
  "qa.hedgehog" %% "hedgehog-core" % hedgehogVersion,
  "qa.hedgehog" %% "hedgehog-runner" % hedgehogVersion,
  "qa.hedgehog" %% "hedgehog-munit" % hedgehogVersion,
).map(_ % Test)

// MUnit: test integration
val munitVersion = "0.7.27"
libraryDependencies += "org.scalameta" %% "munit" % munitVersion % Test

testFrameworks += TestFramework("munit.runner.Framework")
