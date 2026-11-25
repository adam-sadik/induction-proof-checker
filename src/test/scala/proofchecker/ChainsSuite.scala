package proofchecker

import proofchecker.ast.*
import proofchecker.ast.Term.*
import proofchecker.core.*
import proofchecker.parse.Parser

class ChainsSuite extends munit.FunSuite:

  private val header =
    "data Nat = Zero | Succ(Nat)\n" +
      "def add : (Nat, Nat) -> Nat\n" +
      "def add(Zero, m) = m\n" +
      "def add(Succ(n), m) = Succ(add(n, m))\n"

  private val zero = App("Zero", Nil)
  private def succ(t: Term) = App("Succ", List(t))
  private def add(a: Term, b: Term) = App("add", List(a, b))

  /** Checks the chain of the first case of a dummy theorem written after `header`. */
  private def checkChain(
      body: String,
      goal: (Term, Term),
      ihs: List[(Term, Term)] = Nil,
      lemmas: Map[String, Theorem] = Map.empty
  ): Either[ProofError, Unit] =
    val src = header + "theorem t: forall k: Nat. k = k\nproof by induction on k:\ncase Zero:\n" + body + "\nqed"
    val Right(p)   = Parser.parse(src): @unchecked
    val Right(env) = Defs.checkAll(p): @unchecked
    val ctx = Chains.Ctx(env, lemmas, ihs, Map("k" -> "Nat", "x" -> "Nat"))
    Chains.check(ctx, p.theorems.head.cases.head.chain, goal._1, goal._2)

  private def assertError(r: Either[ProofError, Unit], line: Int, fragment: String)(using munit.Location): Unit =
    r match
      case Right(_) => fail("expected an error")
      case Left(e) =>
        assertEquals(e.pos.line, line)
        assert(e.msg.contains(fragment), s"message was: ${e.msg}")

  // header is 4 lines, then theorem / proof / case, so the chain starts on line 8
  private val bodyLine = 8

  test("a correct chain is accepted"):
    val r = checkChain("add(Zero, Zero)\n= Zero by def add", (add(zero, zero), zero))
    assertEquals(r, Right(()))

  test("a step inside a subterm"):
    val r = checkChain(
      "Succ(add(Zero, x))\n= Succ(x) by def add",
      (succ(add(zero, Var("x"))), succ(Var("x")))
    )
    assertEquals(r, Right(()))

  test("wrong right-hand side reports what the rule gives"):
    val r = checkChain("add(Zero, Zero)\n= Succ(Zero) by def add", (add(zero, zero), succ(zero)))
    assertError(r, bodyLine + 1, "rule gives 'Zero', expected 'Succ(Zero)'")

  test("rule that does not apply"):
    val r = checkChain("add(Zero, Zero)\n= Zero by def foo", (add(zero, zero), zero))
    assertError(r, bodyLine + 1, "unknown function 'foo'")

  test("definition equation does not match a constant"):
    // k is a fixed constant, so add(k, Zero) matches no equation
    val r = checkChain("add(k, Zero)\n= k by def add", (add(Var("k"), zero), Var("k")))
    assertError(r, bodyLine + 1, "does not apply to any subterm")

  test("chain must start at the goal's left-hand side"):
    val r = checkChain("add(Zero, Zero)\n= Zero by def add", (add(zero, succ(zero)), zero))
    assertError(r, bodyLine, "chain starts with")

  test("chain must end at the goal's right-hand side"):
    val r = checkChain("add(Zero, Zero)\n= Zero by def add", (add(zero, zero), succ(zero)))
    assertError(r, bodyLine + 1, "chain ends with")

  test("IH is used as a fixed rule"):
    val ih = (add(Var("k"), zero), Var("k"))
    val r  = checkChain("Succ(add(k, Zero))\n= Succ(k) by IH", (succ(add(Var("k"), zero)), succ(Var("k"))), List(ih))
    assertEquals(r, Right(()))

  test("IH does not generalize to other arguments"):
    val ih = (add(Var("k"), zero), Var("k"))
    val r  = checkChain("add(x, Zero)\n= x by IH", (add(Var("x"), zero), Var("x")), List(ih))
    assertError(r, bodyLine + 1, "does not apply")

  test("IH without hypotheses"):
    val r = checkChain("add(Zero, Zero)\n= Zero by IH", (add(zero, zero), zero))
    assertError(r, bodyLine + 1, "no induction hypothesis")

  test("reversed definition"):
    val r = checkChain("Zero\n= add(Zero, Zero) by <- def add", (zero, add(zero, zero)))
    assertEquals(r, Right(()))

  test("reversed step is checked in the right direction"):
    val r = checkChain("Zero\n= add(Zero, Zero) by def add", (zero, add(zero, zero)))
    assertError(r, bodyLine + 1, "cannot justify step")

  test("lemma with quantified variables is instantiated by matching"):
    val lemma = Theorem("add_zero", List("n" -> "Nat"), add(Var("n"), zero), Var("n"), "n", Pos(1, 1), Nil, Pos(1, 1))
    val r = checkChain(
      "add(Succ(Zero), Zero)\n= Succ(Zero) by lemma add_zero",
      (add(succ(zero), zero), succ(zero)),
      lemmas = Map("add_zero" -> lemma)
    )
    assertEquals(r, Right(()))

  test("lemma that is not yet proven is unknown"):
    val r = checkChain("add(Zero, Zero)\n= Zero by lemma later", (add(zero, zero), zero))
    assertError(r, bodyLine + 1, "unknown lemma 'later'")

  test("unbound variable in a step"):
    val r = checkChain("add(Zero, Zero)\n= Zero by def add\n= y by def add", (add(zero, zero), Var("y")))
    assertError(r, bodyLine + 2, "unbound variable 'y'")
