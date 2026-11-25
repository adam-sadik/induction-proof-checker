package proofchecker.core

import proofchecker.ast.*
import proofchecker.ast.Term.*
import proofchecker.ast.Pattern.*

type Subst = Map[String, Term]

/**
 * A rewrite rule `lhs -> rhs`. Only the variables in `vars` are universally quantified and can be
 * matched. Any other `Var` in the rule is a fixed constant (e.g. an induction hypothesis variable)
 * and matches only itself.
 */
final case class Rule(vars: Set[String], lhs: Term, rhs: Term):
  def reverse: Rule = Rule(vars, rhs, lhs)

object Terms:

  def freeVars(t: Term): Set[String] = t match
    case Var(x)       => Set(x)
    case App(_, args) => args.flatMap(freeVars).toSet

  def subst(s: Subst, t: Term): Term = t match
    case Var(x)       => s.getOrElse(x, t)
    case App(f, args) => App(f, args.map(subst(s, _)))

  def patternToTerm(p: Pattern): Term = p match
    case PVar(x)       => Var(x)
    case PCon(c, args) => App(c, args.map(patternToTerm))

  /** One-way matching: finds `s` with `subst(s, pat) == t`, binding only variables in `vars`. */
  def matchTerm(vars: Set[String], pat: Term, t: Term, s: Subst = Map.empty): Option[Subst] =
    (pat, t) match
      case (Var(x), _) if vars(x) =>
        s.get(x) match
          case Some(bound) => if bound == t then Some(s) else None
          case None        => Some(s + (x -> t))
      case (Var(x), Var(y)) => if x == y then Some(s) else None
      case (App(f, ps), App(g, ts)) if f == g && ps.length == ts.length =>
        ps.zip(ts).foldLeft[Option[Subst]](Some(s)) { case (acc, (p, u)) =>
          acc.flatMap(matchTerm(vars, p, u, _))
        }
      case _ => None

  /** All terms obtained from `t` by applying `rule` once, at any one subterm. */
  def rewriteOnce(rule: Rule, t: Term): List[Term] =
    val atRoot = matchTerm(rule.vars, rule.lhs, t) match
      // a rule must not invent values: every quantified variable of the result must be bound
      case Some(s) if (freeVars(rule.rhs) & rule.vars).subsetOf(s.keySet) => List(subst(s, rule.rhs))
      case _                                                              => Nil
    val inside = t match
      case Var(_) => Nil
      case App(f, args) =>
        for
          (arg, i) <- args.zipWithIndex
          r        <- rewriteOnce(rule, arg)
        yield App(f, args.updated(i, r))
    atRoot ++ inside

  /** The equations of a definition, read left to right as rewrite rules. */
  def rulesOf(f: FunDef): List[Rule] =
    f.eqs.map { eq =>
      val vars = eq.pats.flatMap(patVars).toSet
      Rule(vars, App(f.name, eq.pats.map(patternToTerm)), eq.rhs)
    }

  private def patVars(p: Pattern): List[String] = p match
    case PVar(x)       => List(x)
    case PCon(_, args) => args.flatMap(patVars)
