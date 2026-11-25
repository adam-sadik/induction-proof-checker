package proofchecker

import proofchecker.ast.*
import proofchecker.ast.Term.*
import proofchecker.ast.Pattern.*
import proofchecker.parse.{Lexer, Parser}

class ParserSuite extends munit.FunSuite:

  private val nat = "data Nat = Zero | Succ(Nat)\n"

  private def parseOk(src: String): Program =
    Parser.parse(src) match
      case Right(p)  => p
      case Left(err) => fail(s"unexpected parse error at ${err.pos}: ${err.msg}")

  private def parseErr(src: String): ProofError =
    Parser.parse(src) match
      case Left(err) => err
      case Right(_)  => fail("expected a parse error")

  test("lexer tracks lines and columns"):
    val toks = Lexer.tokenize("data N\n  = A -- comment\n").toOption.get
    assertEquals(toks.map(_.pos).take(4), Vector(Pos(1, 1), Pos(1, 6), Pos(2, 3), Pos(2, 5)))

  test("lexer rejects unknown characters"):
    assertEquals(Lexer.tokenize("data @").left.map(_.pos), Left(Pos(1, 6)))

  test("data declaration"):
    val p = parseOk("data List = Nil | Cons(Nat, List)")
    assertEquals(
      p.datas.head.cons,
      List(Constructor("Nil", Nil), Constructor("Cons", List("Nat", "List")))
    )

  test("function definition with patterns"):
    val p = parseOk(nat + "def add : (Nat, Nat) -> Nat\ndef add(Zero, m) = m\ndef add(Succ(n), m) = Succ(add(n, m))")
    val f = p.defs.head
    assertEquals(f.paramTypes, List("Nat", "Nat"))
    assertEquals(f.eqs.length, 2)
    assertEquals(f.eqs(0).pats, List(PCon("Zero", Nil), PVar("m")))
    assertEquals(f.eqs(1).rhs, App("Succ", List(App("add", List(Var("n"), Var("m"))))))

  test("function without equations is rejected"):
    assertEquals(parseErr(nat + "def f : (Nat) -> Nat\n").pos, Pos(2, 1))

  test("full theorem parses with positions"):
    val src = scala.io.Source.fromFile("examples/add_zero_right.proof").mkString
    val t   = parseOk(src).theorems.head
    assertEquals(t.name, "add_zero_right")
    assertEquals(t.indVar, "n")
    assertEquals(t.cases.map(_.con), List("Zero", "Succ"))
    val succ = t.cases(1)
    assertEquals(succ.binders, List("k"))
    assertEquals(succ.ihs.length, 1)
    assertEquals(succ.chain.steps.map(_.just), List(Just.Def("add", false), Just.IH(false)))
    assertEquals(succ.chain.steps.head.pos, Pos(14, 5))

  test("reversed justifications and lemmas"):
    val src = nat +
      "theorem t: forall n: Nat. n = n\nproof by induction on n:\n" +
      "case Zero:\n Zero = Zero by <- def f\n= Zero by lemma foo\n" +
      "case Succ(k) [IH: k = k]:\n Succ(k) = Succ(k) by <- IH\nqed"
    val cs = parseOk(src).theorems.head.cases
    assertEquals(cs(0).chain.steps.map(_.just), List(Just.Def("f", true), Just.Lemma("foo", false)))
    assertEquals(cs(1).chain.steps.map(_.just), List(Just.IH(true)))

  test("missing justification is reported at the offending token"):
    val src = nat + "theorem t: forall n: Nat. n = n\nproof by induction on n:\ncase Zero:\n Zero = Zero\nqed"
    val err = parseErr(src)
    assertEquals(err.pos, Pos(6, 1))
    assert(err.msg.contains("expected 'by'"), err.msg)

  test("a chain needs at least one step"):
    val src = nat + "theorem t: forall n: Nat. n = n\nproof by induction on n:\ncase Zero:\n Zero\nqed"
    assert(parseErr(src).msg.contains("expected '='"))

  test("stray top-level token"):
    assertEquals(parseErr("qed").pos, Pos(1, 1))
