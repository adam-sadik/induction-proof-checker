package proofchecker.parse

import scala.util.boundary
import proofchecker.ast.*
import proofchecker.ast.Term.*
import proofchecker.ast.Pattern.*

/** Recursive-descent parser. The first syntax error aborts the parse through `boundary`. */
object Parser:

  def parse(src: String): Either[ProofError, Program] =
    Lexer.tokenize(src).flatMap(toks => boundary(Right(new Impl(toks).program())))

  private type Parse[A] = boundary.Label[Either[ProofError, Program]] ?=> A

  private final class Impl(tokens: Vector[Token]):
    private var i = 0
    // constructor names declared so far: a bare identifier among them is a constant
    private var constructors = Set.empty[String]

    private def peek: Token           = tokens(i)
    private def peekAt(k: Int): Token = tokens(math.min(i + k, tokens.length - 1))

    private def advance(): Token =
      val t = tokens(i)
      if t.kind != Tok.Eof then i += 1
      t

    private def fail(pos: Pos, msg: String): Parse[Nothing] =
      boundary.break(Left(ProofError(pos, msg)))

    private def unexpected(what: String): Parse[Nothing] =
      fail(peek.pos, s"expected $what, found ${peek.kind.show}")

    private def isSym(s: String) = peek.kind == Tok.Sym(s)
    private def isKw(s: String)  = peek.kind == Tok.Kw(s)

    private def expectSym(s: String): Parse[Token] =
      if isSym(s) then advance() else unexpected(s"'$s'")

    private def expectKw(s: String): Parse[Token] =
      if isKw(s) then advance() else unexpected(s"'$s'")

    private def ident(what: String): Parse[String] =
      peek.kind match
        case Tok.Id(n) =>
          advance()
          n
        case _ => unexpected(what)

    /** `item (',' item)*` */
    private def commaSep[A](item: () => Parse[A]): Parse[List[A]] =
      val first = item()
      if isSym(",") then
        advance()
        first :: commaSep(item)
      else List(first)

    private def parenList[A](item: () => Parse[A]): Parse[List[A]] =
      expectSym("(")
      val xs = commaSep(item)
      expectSym(")")
      xs

    // ---- program ----

    def program(): Parse[Program] =
      def loop(ds: List[DataDecl], fs: List[FunDef], ts: List[Theorem]): Parse[Program] =
        peek.kind match
          case Tok.Eof           => Program(ds.reverse, fs.reverse, ts.reverse)
          case Tok.Kw("data")    => loop(dataDecl() :: ds, fs, ts)
          case Tok.Kw("def")     => loop(ds, funDef() :: fs, ts)
          case Tok.Kw("theorem") => loop(ds, fs, theorem() :: ts)
          case _                 => unexpected("'data', 'def' or 'theorem'")
      loop(Nil, Nil, Nil)

    // ---- data ----

    private def dataDecl(): Parse[DataDecl] =
      val pos  = expectKw("data").pos
      val name = ident("a type name")
      expectSym("=")
      def cons(): Parse[List[Constructor]] =
        val c = constructor()
        if isSym("|") then
          advance()
          c :: cons()
        else List(c)
      val cs = cons()
      constructors ++= cs.map(_.name)
      DataDecl(name, cs, pos)

    private def constructor(): Parse[Constructor] =
      val name = ident("a constructor name")
      val args = if isSym("(") then parenList(() => ident("a type name")) else Nil
      Constructor(name, args)

    // ---- functions ----

    private def funDef(): Parse[FunDef] =
      val pos  = expectKw("def").pos
      val name = ident("a function name")
      expectSym(":")
      val params = parenList(() => ident("a type name"))
      expectSym("->")
      val ret = ident("a type name")
      def equations(): Parse[List[Equation]] =
        if isKw("def") && peekAt(1).kind == Tok.Id(name) && peekAt(2).kind == Tok.Sym("(") then
          val e = equation()
          e :: equations()
        else Nil
      val eqs = equations()
      if eqs.isEmpty then fail(pos, s"function '$name' has no equations")
      FunDef(name, params, ret, eqs, pos)

    private def equation(): Parse[Equation] =
      val pos = expectKw("def").pos
      ident("a function name")
      val pats = parenList(() => pattern())
      expectSym("=")
      Equation(pats, term(), pos)

    private def pattern(): Parse[Pattern] =
      val name = ident("a pattern")
      if isSym("(") then PCon(name, parenList(() => pattern()))
      else if constructors(name) then PCon(name, Nil)
      else PVar(name)

    // ---- terms ----

    private def term(): Parse[Term] =
      val name = ident("a term")
      if isSym("(") then App(name, parenList(() => term()))
      else if constructors(name) then App(name, Nil)
      else Var(name)

    private def equality(): Parse[(Term, Term)] =
      val l = term()
      expectSym("=")
      (l, term())

    // ---- theorems and proofs ----

    private def theorem(): Parse[Theorem] =
      val pos  = expectKw("theorem").pos
      val name = ident("a theorem name")
      expectSym(":")
      expectKw("forall")
      val vars = commaSep(() => binder())
      expectSym(".")
      val (lhs, rhs) = equality()
      expectKw("proof")
      expectKw("by")
      expectKw("induction")
      expectKw("on")
      val indPos = peek.pos
      val indVar = ident("a variable name")
      expectSym(":")
      def cases(): Parse[List[ProofCase]] =
        val c = proofCase()
        if isKw("case") then c :: cases() else List(c)
      if !isKw("case") then unexpected("'case'")
      val cs = cases()
      expectKw("qed")
      Theorem(name, vars, lhs, rhs, indVar, indPos, cs, pos)

    private def binder(): Parse[(String, String)] =
      val x = ident("a variable name")
      expectSym(":")
      (x, ident("a type name"))

    private def proofCase(): Parse[ProofCase] =
      val pos     = expectKw("case").pos
      val con     = ident("a constructor name")
      val binders = if isSym("(") then parenList(() => ident("a variable name")) else Nil
      val ihs =
        if isSym("[") then
          advance()
          val xs = commaSep { () =>
            expectKw("IH")
            expectSym(":")
            equality()
          }
          expectSym("]")
          xs
        else Nil
      expectSym(":")
      ProofCase(con, binders, ihs, chain(), pos)

    private def chain(): Parse[Chain] =
      val pos   = peek.pos
      val start = term()
      def steps(): Parse[List[Step]] =
        if isSym("=") then
          val s = step()
          s :: steps()
        else Nil
      val ss = steps()
      if ss.isEmpty then unexpected("'='")
      Chain(start, ss, pos)

    private def step(): Parse[Step] =
      val pos = expectSym("=").pos
      val rhs = term()
      expectKw("by")
      Step(rhs, just(), pos)

    private def just(): Parse[Just] =
      val reversed = isSym("<-")
      if reversed then advance()
      peek.kind match
        case Tok.Kw("def") =>
          advance()
          Just.Def(ident("a function name"), reversed)
        case Tok.Kw("IH") =>
          advance()
          Just.IH(reversed)
        case Tok.Kw("lemma") =>
          advance()
          Just.Lemma(ident("a theorem name"), reversed)
        case _ => unexpected("'def', 'IH' or 'lemma'")
