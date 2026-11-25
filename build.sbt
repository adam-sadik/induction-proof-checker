ThisBuild / scalaVersion := "3.3.6"
ThisBuild / version      := "0.1.0"

lazy val root = project
  .in(file("."))
  .settings(
    name := "induction-proof-checker",
    scalacOptions ++= Seq("-deprecation", "-feature", "-unchecked"),
    libraryDependencies += "org.scalameta" %% "munit" % "1.0.4" % Test,
    // fork so that sys.exit in the CLI does not kill sbt
    run / fork := true
  )
