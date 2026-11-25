package proofchecker

import proofchecker.ast.*
import proofchecker.core.Defs
import proofchecker.parse.Parser

class DefsSuite extends munit.FunSuite:

  private val nat  = "data Nat = Zero | Succ(Nat)\n"
  private val list = "data List = Nil | Cons(Nat, List)\n"

  private def check(src: String): Either[ProofError, Unit] =
    Parser.parse(src) match
      case Left(e)  => fail(s"parse error at ${e.pos}: ${e.msg}")
      case Right(p) => Defs.checkAll(p).map(_ => ())

  private def assertRejected(src: String, line: Int, fragment: String)(using munit.Location): Unit =
    check(src) match
      case Right(_) => fail("expected a definition error")
      case Left(e) =>
        assertEquals(e.pos.line, line)
        assert(e.msg.contains(fragment), s"message was: ${e.msg}")

  private val add =
    "def add : (Nat, Nat) -> Nat\n" +
      "def add(Zero, m) = m\n" +
      "def add(Succ(n), m) = Succ(add(n, m))\n"

  test("valid definitions are accepted"):
    val append =
      "def append : (List, List) -> List\n" +
        "def append(Nil, ys) = ys\n" +
        "def append(Cons(x, xs), ys) = Cons(x, append(xs, ys))\n"
    assertEquals(check(nat + list + add + append), Right(()))

  test("nested patterns and deep recursion are accepted"):
    val src = nat + "def half : (Nat) -> Nat\n" +
      "def half(Zero) = Zero\ndef half(Succ(Zero)) = Zero\ndef half(Succ(Succ(n))) = Succ(half(n))\n"
    assertEquals(check(src), Right(()))

  test("missing constructor case"):
    assertRejected(nat + "def f : (Nat) -> Nat\ndef f(Zero) = Zero\n", 2, "not total")

  test("missing nested case reports a witness"):
    val src = nat + "def f : (Nat) -> Nat\ndef f(Zero) = Zero\ndef f(Succ(Zero)) = Zero\n"
    assertRejected(src, 2, "f(Succ(Succ(_)))")

  test("missing combination of arguments"):
    val src = nat + "def f : (Nat, Nat) -> Nat\ndef f(Zero, m) = m\ndef f(Succ(n), Zero) = n\n"
    assertRejected(src, 2, "f(Succ(_), Succ(_))")

  test("overlapping equations"):
    val src = nat + "def f : (Nat) -> Nat\ndef f(Zero) = Zero\ndef f(n) = n\n"
    assertRejected(src, 4, "overlaps")

  test("duplicate equation"):
    val src = nat + "def f : (Nat) -> Nat\ndef f(Zero) = Zero\ndef f(Zero) = Zero\ndef f(Succ(n)) = n\n"
    assertRejected(src, 4, "overlaps")

  test("recursive call on the same argument"):
    val src = nat + "def f : (Nat) -> Nat\ndef f(Zero) = Zero\ndef f(Succ(n)) = f(Succ(n))\n"
    assertRejected(src, 4, "not structural")

  test("recursion on a variable pattern"):
    val src = nat + "def f : (Nat) -> Nat\ndef f(n) = f(n)\n"
    assertRejected(src, 3, "not structural")

  test("arguments that swap forever are rejected"):
    val src = nat + "def f : (Nat, Nat) -> Nat\n" +
      "def f(Succ(a), b) = f(a, Succ(b))\n" +
      "def f(Zero, Succ(b)) = f(Succ(Zero), b)\n" +
      "def f(Zero, Zero) = Zero\n"
    assertRejected(src, 2, "same argument")

  test("ackermann is not structural"):
    val src = nat + "def ack : (Nat, Nat) -> Nat\n" +
      "def ack(Zero, n) = Succ(n)\n" +
      "def ack(Succ(m), Zero) = ack(m, Succ(Zero))\n" +
      "def ack(Succ(m), Succ(n)) = ack(m, ack(Succ(m), n))\n"
    assertRejected(src, 2, "same argument")

  test("a function may only call itself or earlier functions"):
    val src = nat + "def f : (Nat) -> Nat\ndef f(Zero) = g(Zero)\ndef f(Succ(n)) = n\n"
    assertRejected(src, 3, "unknown function")

  test("type errors"):
    val src = nat + list + "def f : (List) -> Nat\ndef f(Nil) = Nil\ndef f(Cons(x, xs)) = x\n"
    assertRejected(src, 4, "has type List, expected Nat")

  test("wrong constructor type in a pattern"):
    assertRejected(nat + list + "def f : (Nat) -> Nat\ndef f(Nil) = Zero\n", 4, "builds a List")

  test("wrong arity in a pattern"):
    assertRejected(nat + "def f : (Nat) -> Nat\ndef f(Succ(a, b)) = a\n", 3, "takes 1 argument")

  test("non-linear pattern"):
    val src = nat + "def f : (Nat, Nat) -> Nat\ndef f(a, a) = a\n"
    assertRejected(src, 3, "occurs twice")

  test("unbound variable on the right-hand side"):
    assertRejected(nat + "def f : (Nat) -> Nat\ndef f(n) = m\n", 3, "unbound variable 'm'")

  test("unknown type and duplicate declarations"):
    assertRejected("data T = A(U)\n", 1, "unknown type 'U'")
    assertRejected(nat + nat, 2, "declared twice")
    assertRejected(nat + add + add, 5, "already declared")
