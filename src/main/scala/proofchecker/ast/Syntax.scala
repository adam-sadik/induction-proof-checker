package proofchecker.ast

/** 1-based source position. */
final case class Pos(line: Int, col: Int)

/** An error (from parsing or checking) at a source position. */
final case class ProofError(pos: Pos, msg: String)

/** Terms. Constants and nullary constructors are `App(name, Nil)`. */
enum Term:
  case Var(name: String)
  case App(fn: String, args: List[Term])

  def show: String = this match
    case Var(x)       => x
    case App(f, Nil)  => f
    case App(f, args) => args.map(_.show).mkString(f + "(", ", ", ")")

enum Pattern:
  case PVar(name: String)
  case PCon(con: String, args: List[Pattern])

  def show: String = this match
    case PVar(x)       => x
    case PCon(c, Nil)  => c
    case PCon(c, args) => args.map(_.show).mkString(c + "(", ", ", ")")

final case class Constructor(name: String, argTypes: List[String])
final case class DataDecl(name: String, cons: List[Constructor], pos: Pos)

final case class Equation(pats: List[Pattern], rhs: Term, pos: Pos)
final case class FunDef(
    name: String,
    paramTypes: List[String],
    retType: String,
    eqs: List[Equation],
    pos: Pos
)

/** How a proof step is justified. `reversed` means the rule is used right to left. */
enum Just:
  case Def(fn: String, reversed: Boolean)
  case IH(reversed: Boolean)
  case Lemma(name: String, reversed: Boolean)

/** One step `= rhs by just`; `pos` is the position of the `=`. */
final case class Step(rhs: Term, just: Just, pos: Pos)
final case class Chain(start: Term, steps: List[Step], pos: Pos)

/** An induction case as written; `ihs` is the written `[IH: ...]` annotation. */
final case class ProofCase(
    con: String,
    binders: List[String],
    ihs: List[(Term, Term)],
    chain: Chain,
    pos: Pos
)

final case class Theorem(
    name: String,
    vars: List[(String, String)],
    lhs: Term,
    rhs: Term,
    indVar: String,
    indPos: Pos,
    cases: List[ProofCase],
    pos: Pos
)

final case class Program(
    datas: List[DataDecl],
    defs: List[FunDef],
    theorems: List[Theorem]
)
