package proofchecker.core

import proofchecker.ast.*

/** Checks equational chains `t0 = t1 by J1 = t2 by J2 ...` against a goal `lhs = rhs`. */
object Chains:

  /** What a chain may use: declared functions, proven lemmas and the case's IH as fixed rules. */
  final case class Ctx(
      env: Env,
      lemmas: Map[String, Theorem],
      ihs: List[(Term, Term)],
      vars: Map[String, String] // types of the theorem variables and of the case constants
  )

  def showJust(j: Just): String =
    val (rev, rule) = j match
      case Just.Def(f, r)   => (r, s"def $f")
      case Just.IH(r)       => (r, "IH")
      case Just.Lemma(n, r) => (r, s"lemma $n")
    if rev then s"<- $rule" else rule

  def check(ctx: Ctx, chain: Chain, goalLhs: Term, goalRhs: Term): Either[ProofError, Unit] =
    for
      _ <- if chain.start == goalLhs then Right(())
           else Left(ProofError(chain.pos,
             s"the chain starts with '${chain.start.show}', but the goal's left-hand side is '${goalLhs.show}'"))
      _ <- chain.steps.foldLeft[Either[ProofError, Term]](Right(chain.start)) { (acc, step) =>
        acc.flatMap(prev => checkStep(ctx, prev, step).map(_ => step.rhs))
      }
      last = chain.steps.last
      _ <- if last.rhs == goalRhs then Right(())
           else Left(ProofError(last.pos,
             s"the chain ends with '${last.rhs.show}', but the goal's right-hand side is '${goalRhs.show}'"))
    yield ()

  private def checkStep(ctx: Ctx, prev: Term, step: Step): Either[ProofError, Unit] =
    def err(msg: String) = Left(ProofError(step.pos, msg))
    for
      _ <- ctx.env.typeOf(ctx.vars, step.rhs).left.map(ProofError(step.pos, _))
      rules <- rulesFor(ctx, step.just).left.map(ProofError(step.pos, _))
      results = rules.flatMap(Terms.rewriteOnce(_, prev)).distinct
      _ <-
        if results.contains(step.rhs) then Right(())
        else
          val where = s"cannot justify step '${prev.show} = ${step.rhs.show}' by ${showJust(step.just)}"
          if results.isEmpty then err(s"$where: the rule does not apply to any subterm of '${prev.show}'")
          else err(s"$where: rule gives ${results.map(r => s"'${r.show}'").mkString(" or ")}, expected '${step.rhs.show}'")
    yield ()

  private def rulesFor(ctx: Ctx, j: Just): Either[String, List[Rule]] =
    val (rules, reversed) = j match
      case Just.Def(f, rev) =>
        ctx.env.funs.get(f) match
          case Some(fd) => (Right(Terms.rulesOf(fd)), rev)
          case None     => (Left(s"unknown function '$f'"), rev)
      case Just.IH(rev) =>
        if ctx.ihs.isEmpty then (Left("there is no induction hypothesis in this case"), rev)
        else (Right(ctx.ihs.map((l, r) => Rule(Set.empty, l, r))), rev)
      case Just.Lemma(name, rev) =>
        ctx.lemmas.get(name) match
          case Some(t) => (Right(List(Rule(t.vars.map(_._1).toSet, t.lhs, t.rhs))), rev)
          case None =>
            (Left(s"unknown lemma '$name' (a lemma can only be used after its proof)"), rev)
    rules.map(rs => if reversed then rs.map(_.reverse) else rs)
