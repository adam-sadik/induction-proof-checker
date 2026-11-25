package proofchecker.cli

import java.nio.file.{Files, Path}
import scala.util.Try
import proofchecker.core.Checker
import proofchecker.parse.Parser

/** Reads a proof file and runs the pipeline: parse, then check definitions and proofs. */
object Cli:

  val ExitOk       = 0
  val ExitProof    = 1 // the file has a syntax or proof error
  val ExitUsage    = 2 // bad arguments or unreadable file

  /** Returns the exit code and the line to print (stdout when 0, stderr otherwise). */
  def run(args: List[String]): (Int, String) =
    args match
      case List(path) => checkFile(path)
      case _          => (ExitUsage, "usage: run <file.proof>")

  private def checkFile(path: String): (Int, String) =
    Try(Files.readString(Path.of(path))).toEither match
      case Left(e) => (ExitUsage, s"$path: cannot read file: ${e.getMessage}")
      case Right(src) =>
        val result = Parser.parse(src).flatMap(Checker.check)
        result match
          case Right(_) => (ExitOk, "OK")
          case Left(e)  => (ExitProof, s"$path:${e.pos.line}:${e.pos.col}: ${e.msg}")
