package proofchecker

import proofchecker.ast.*
import proofchecker.ast.Term.*
import proofchecker.core.*
import proofchecker.parse.Parser

class TermsSuite extends munit.FunSuite:

  private def v(x: String)                  = Var(x)
  private def app(f: String, a: Term*)      = App(f, a.toList)
  private def succ(t: Term)                 = app("Succ", t)
  private val zero                          = app("Zero")

  test("substitution replaces variables"):
    val t = app("add", v("n"), succ(v("m")))
    assertEquals(Terms.subst(Map("n" -> zero), t), app("add", zero, succ(v("m"))))

  test("matching binds variables"):
    val pat = app("add", succ(v("n")), v("m"))
    val t   = app("add", succ(succ(zero)), zero)
    assertEquals(
      Terms.matchTerm(Set("n", "m"), pat, t),
      Some(Map("n" -> succ(zero), "m" -> zero))
    )

  test("matching a repeated variable needs equal subterms"):
    val pat = app("eq", v("x"), v("x"))
    assertEquals(Terms.matchTerm(Set("x"), pat, app("eq", zero, zero)), Some(Map("x" -> zero)))
    assertEquals(Terms.matchTerm(Set("x"), pat, app("eq", zero, succ(zero))), None)

  test("constructor or function mismatch does not match"):
    assertEquals(Terms.matchTerm(Set("n"), succ(v("n")), zero), None)
    assertEquals(Terms.matchTerm(Set("n"), app("f", v("n")), app("g", zero)), None)

  test("variables outside the rule's variable set are constants"):
    // `k` is fixed, so it matches only itself, not an arbitrary term
    assertEquals(Terms.matchTerm(Set.empty, v("k"), v("k")), Some(Map.empty))
    assertEquals(Terms.matchTerm(Set.empty, v("k"), zero), None)
    assertEquals(Terms.matchTerm(Set.empty, v("k"), v("j")), None)

  private val addRules =
    val Right(p) = Parser.parse(
      "data Nat = Zero | Succ(Nat)\n" +
        "def add : (Nat, Nat) -> Nat\n" +
        "def add(Zero, m) = m\n" +
        "def add(Succ(n), m) = Succ(add(n, m))\n"
    ): @unchecked
    Terms.rulesOf(p.defs.head)

  private def rewriteDef(t: Term): List[Term] = addRules.flatMap(Terms.rewriteOnce(_, t))

  test("rewriting at the root"):
    assertEquals(rewriteDef(app("add", succ(v("k")), zero)), List(succ(app("add", v("k"), zero))))

  test("rewriting inside a term, one occurrence at a time"):
    val t = app("add", succ(zero), app("add", zero, v("x")))
    assertEquals(
      rewriteDef(t),
      List(
        app("add", succ(zero), v("x")),                    // first equation, on the inner call
        succ(app("add", zero, app("add", zero, v("x"))))   // second equation, on the outer call
      )
    )

  test("a constant is not matched by a definition pattern"):
    // add(k, Zero) with k a fixed constant: neither equation applies
    assertEquals(rewriteDef(app("add", v("k"), zero)), Nil)

  test("reversed rules rewrite right to left"):
    val rule = addRules(0).reverse // m -> add(Zero, m)
    assertEquals(Terms.rewriteOnce(rule, zero).head, app("add", zero, zero))

  test("a rule may not introduce unbound quantified variables"):
    // forall x y. f(x) = g(x, y), used left to right, would have to invent y
    val rule = Rule(Set("x", "y"), app("f", v("x")), app("g", v("x"), v("y")))
    assertEquals(Terms.rewriteOnce(rule, app("f", zero)), Nil)
    assertEquals(Terms.rewriteOnce(rule.reverse, app("g", zero, zero)), List(app("f", zero)))
