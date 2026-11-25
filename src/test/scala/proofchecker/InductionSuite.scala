package proofchecker

import proofchecker.ast.*
import proofchecker.core.Checker
import proofchecker.parse.Parser

class InductionSuite extends munit.FunSuite:

  private val defs =
    """data Nat = Zero | Succ(Nat)
      |data List = Nil | Cons(Nat, List)
      |def add : (Nat, Nat) -> Nat
      |def add(Zero, m) = m
      |def add(Succ(n), m) = Succ(add(n, m))
      |def append : (List, List) -> List
      |def append(Nil, ys) = ys
      |def append(Cons(x, xs), ys) = Cons(x, append(xs, ys))
      |""".stripMargin

  private val addZeroRight =
    """theorem add_zero_right: forall n: Nat. add(n, Zero) = n
      |proof by induction on n:
      |  case Zero:
      |    add(Zero, Zero)
      |    = Zero by def add
      |  case Succ(k) [IH: add(k, Zero) = k]:
      |    add(Succ(k), Zero)
      |    = Succ(add(k, Zero)) by def add
      |    = Succ(k) by IH
      |qed
      |""".stripMargin

  private def run(src: String): Either[ProofError, Unit] =
    Parser.parse(src) match
      case Left(e)  => fail(s"parse error at ${e.pos}: ${e.msg}")
      case Right(p) => Checker.check(p)

  private def lineOf(src: String, marker: String): Int =
    src.linesIterator.indexWhere(_.contains(marker)) + 1

  private def assertError(src: String, marker: String, fragment: String)(using munit.Location): Unit =
    run(src) match
      case Right(_) => fail("expected an error")
      case Left(e) =>
        assert(e.msg.contains(fragment), s"message was: ${e.msg}")
        assertEquals(e.pos.line, lineOf(src, marker), s"message was: ${e.msg}")

  test("ordinary induction on the naturals"):
    assertEquals(run(defs + addZeroRight), Right(()))

  test("several variables, induction on one of them"):
    val src = defs +
      """theorem add_succ_right: forall n: Nat, m: Nat. add(n, Succ(m)) = Succ(add(n, m))
        |proof by induction on n:
        |  case Zero:
        |    add(Zero, Succ(m))
        |    = Succ(m) by def add
        |    = Succ(add(Zero, m)) by <- def add
        |  case Succ(k) [IH: add(k, Succ(m)) = Succ(add(k, m))]:
        |    add(Succ(k), Succ(m))
        |    = Succ(add(k, Succ(m))) by def add
        |    = Succ(Succ(add(k, m))) by IH
        |    = Succ(add(Succ(k), m)) by <- def add
        |qed
        |""".stripMargin
    assertEquals(run(src), Right(()))

  test("non-recursive constructor arguments get no hypothesis"):
    val src = defs +
      """theorem append_nil: forall xs: List. append(xs, Nil) = xs
        |proof by induction on xs:
        |  case Nil:
        |    append(Nil, Nil)
        |    = Nil by def append
        |  case Cons(h, t) [IH: append(t, Nil) = t]:
        |    append(Cons(h, t), Nil)
        |    = Cons(h, append(t, Nil)) by def append
        |    = Cons(h, t) by IH
        |qed
        |""".stripMargin
    assertEquals(run(src), Right(()))

  test("a proven lemma can be used, instantiated by matching"):
    val src = defs + addZeroRight +
      """theorem again: forall n: Nat. add(n, Zero) = n
        |proof by induction on n:
        |  case Zero:
        |    add(Zero, Zero)
        |    = Zero by lemma add_zero_right
        |  case Succ(k) [IH: add(k, Zero) = k]:
        |    add(Succ(k), Zero)
        |    = Succ(k) by lemma add_zero_right
        |qed
        |""".stripMargin
    assertEquals(run(src), Right(()))

  test("a theorem cannot use itself"):
    val src = defs + addZeroRight.replace("= Succ(k) by IH", "= Succ(k) by lemma add_zero_right")
    assertError(src, "by lemma add_zero_right", "unknown lemma 'add_zero_right'")

  test("a lemma cannot be used before it is proven"):
    val src = defs + addZeroRight.replace("= Zero by def add", "= Zero by lemma later") +
      addZeroRight.replace("add_zero_right", "later")
    assertError(src, "by lemma later", "unknown lemma 'later'")

  test("missing case"):
    val src = defs + addZeroRight.replace(
      "  case Zero:\n    add(Zero, Zero)\n    = Zero by def add\n", "")
    assertError(src, "induction on n", "missing case 'Zero'")

  test("duplicate case"):
    val dup = "  case Zero:\n    add(Zero, Zero)\n    = Zero by def add\n"
    val src = defs + addZeroRight.replace(dup, dup + dup)
    // reported on the second occurrence, which starts 3 lines after the first
    val e = run(src).left.getOrElse(fail("expected an error"))
    assertEquals(e.pos.line, lineOf(src, "case Zero") + 3)
    assert(e.msg.contains("duplicate case 'Zero'"), e.msg)

  test("unknown constructor"):
    val src = defs + addZeroRight.replace("case Zero:", "case Nil:")
    assertError(src, "case Nil", "not a constructor of type Nat")

  test("wrong number of binders"):
    val src = defs + addZeroRight.replace("case Succ(k) [IH: add(k, Zero) = k]", "case Succ(k, j)")
    assertError(src, "case Succ", "takes 1 argument(s), but the case binds 2")

  test("missing induction hypothesis annotation"):
    val src = defs + addZeroRight.replace(" [IH: add(k, Zero) = k]", "")
    assertError(src, "case Succ", "missing induction hypothesis: expected [IH: add(k, Zero) = k]")

  test("wrong induction hypothesis annotation"):
    val src = defs + addZeroRight.replace("[IH: add(k, Zero) = k]", "[IH: add(k, Zero) = Zero]")
    assertError(src, "case Succ", "wrong induction hypothesis")

  test("hypothesis written where there is none"):
    val src = defs + addZeroRight.replace("case Zero:", "case Zero [IH: Zero = Zero]:")
    assertError(src, "case Zero", "no induction hypothesis")

  test("the induction hypothesis is a constant, it does not match other terms"):
    val src = defs + addZeroRight.replace(
      "= Succ(k) by IH", "= Succ(add(k, Zero)) by IH")
    assertError(src, "= Succ(add(k, Zero)) by IH", "cannot justify step")

  test("induction on an unknown variable"):
    val src = defs + addZeroRight.replace("induction on n:", "induction on z:")
    assertError(src, "induction on z", "not a variable of the theorem")

  test("ill-typed statement"):
    val src = defs + addZeroRight.replace("= n\nproof", "= Nil\nproof")
    assertError(src, "theorem add_zero_right", "different types")

  test("binder may not capture another theorem variable"):
    val src = defs +
      """theorem t: forall n: Nat, m: Nat. add(n, m) = add(n, m)
        |proof by induction on n:
        |  case Zero:
        |    add(Zero, m)
        |    = m by def add
        |    = add(Zero, m) by <- def add
        |  case Succ(m) [IH: add(m, m) = add(m, m)]:
        |    add(Succ(m), m)
        |    = add(Succ(m), m) by def add
        |qed
        |""".stripMargin
    assertError(src, "case Succ", "choose a fresh name")

  test("duplicate theorem names"):
    val src = defs + addZeroRight + addZeroRight
    val e   = run(src).left.getOrElse(fail("expected an error"))
    assertEquals(e.pos.line, lineOf(src, "theorem add_zero_right") + addZeroRight.linesIterator.size)
    assert(e.msg.contains("declared twice"), e.msg)
