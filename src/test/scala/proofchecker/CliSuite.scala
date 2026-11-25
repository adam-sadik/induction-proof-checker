package proofchecker

import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import proofchecker.cli.Cli

class CliSuite extends munit.FunSuite:

  private def proofFiles(dir: String): List[Path] =
    Files.list(Path.of(dir)).iterator.asScala.toList
      .filter(_.toString.endsWith(".proof"))
      .sortBy(_.getFileName.toString)

  private def rel(p: Path): String = p.toString.replace('\\', '/')

  test("all valid examples are accepted"):
    val files = proofFiles("examples")
    assert(files.length >= 8, s"expected at least 8 examples, found ${files.length}")
    for f <- files do
      assertEquals(Cli.run(List(rel(f))), (Cli.ExitOk, "OK"), rel(f))

  test("invalid examples give the expected error and a non-zero exit code"):
    val files = proofFiles("examples/invalid")
    assert(files.nonEmpty)
    for f <- files do
      val expectedFile = Path.of(rel(f).stripSuffix(".proof") + ".expected")
      val expected     = Files.readString(expectedFile).trim
      assertEquals(Cli.run(List(rel(f))), (Cli.ExitProof, expected), rel(f))

  test("usage error without a file argument"):
    assertEquals(Cli.run(Nil)._1, Cli.ExitUsage)
    assertEquals(Cli.run(List("a", "b"))._1, Cli.ExitUsage)

  test("unreadable file"):
    val (code, msg) = Cli.run(List("examples/does_not_exist.proof"))
    assertEquals(code, Cli.ExitUsage)
    assert(msg.contains("cannot read file"), msg)
