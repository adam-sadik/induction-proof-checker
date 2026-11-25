package proofchecker.core

import proofchecker.ast.*
import proofchecker.ast.Term.*

/**
 * Checks a theorem proven by structural induction. The checker generates the required cases
 * from the `data` declaration; the user's cases must match them exactly.
 */
object Induction:

  private type Result[A] = Either[ProofError, A]

  private def guard(ok: Boolean, pos: Pos, msg: => String): Result[Unit] =
    if ok then Right(()) else Left(ProofError(pos, msg))

  private def forEachOk[A](xs: List[A])(f: A => Result[Unit]): Result[Unit] =
    xs.foldLeft[Result[Unit]](Right(()))((acc, x) => acc.flatMap(_ => f(x)))

  def checkTheorem(env: Env, lemmas: Map[String, Theorem], thm: Theorem): Result[Unit] =
    for
      varTypes <- checkStatement(env, thm)
      data = env.datas(varTypes(thm.indVar))
      _ <- checkCoverage(data, thm)
      _ <- forEachOk(thm.cases)(checkCase(env, lemmas, thm, varTypes, data, _))
    yield ()

  /** The statement must be well-typed and the induction variable must be one of its variables. */
  private def checkStatement(env: Env, thm: Theorem): Result[Map[String, String]] =
    val names = thm.vars.map(_._1)
    for
      _ <- guard(names.distinct.length == names.length, thm.pos, "a variable is bound twice in the theorem")
      // variable names must not be confused with constructors or functions
      _ <- forEachOk(thm.vars)((x, t) =>
        for
          _ <- guard(!env.cons.contains(x) && !env.funs.contains(x), thm.pos, s"'$x' is already a constructor or function")
          _ <- guard(env.datas.contains(t), thm.pos, s"unknown type '$t'")
        yield ()
      )
      vars = thm.vars.toMap
      _ <- guard(vars.contains(thm.indVar), thm.indPos, s"'${thm.indVar}' is not a variable of the theorem")
      lt <- env.typeOf(vars, thm.lhs).left.map(ProofError(thm.pos, _))
      rt <- env.typeOf(vars, thm.rhs).left.map(ProofError(thm.pos, _))
      _ <- guard(lt == rt, thm.pos, s"the two sides of the theorem have different types ($lt and $rt)")
    yield vars

  /** One case per constructor: none unknown, none duplicated, none missing. */
  private def checkCoverage(data: DataDecl, thm: Theorem): Result[Unit] =
    val known = data.cons.map(_.name).toSet
    val seen = thm.cases.foldLeft[Result[Set[String]]](Right(Set.empty)) { (acc, c) =>
      acc.flatMap { s =>
        for
          _ <- guard(known(c.con), c.pos, s"'${c.con}' is not a constructor of type ${data.name}")
          _ <- guard(!s(c.con), c.pos, s"duplicate case '${c.con}'")
        yield s + c.con
      }
    }
    seen.flatMap(s =>
      data.cons.map(_.name).find(!s(_)) match
        case Some(c) => Left(ProofError(thm.indPos, s"missing case '$c'"))
        case None    => Right(())
    )

  private def showIHs(ihs: List[(Term, Term)]): String =
    ihs.map((l, r) => s"IH: ${l.show} = ${r.show}").mkString("[", ", ", "]")

  private def checkCase(
      env: Env,
      lemmas: Map[String, Theorem],
      thm: Theorem,
      varTypes: Map[String, String],
      data: DataDecl,
      pc: ProofCase
  ): Result[Unit] =
    val con = data.cons.find(_.name == pc.con).get // existence checked by checkCoverage
    val x   = thm.indVar
    val others = varTypes - x
    for
      _ <- guard(
        pc.binders.length == con.argTypes.length,
        pc.pos,
        s"constructor '${con.name}' takes ${con.argTypes.length} argument(s), but the case binds ${pc.binders.length}"
      )
      _ <- guard(pc.binders.distinct.length == pc.binders.length, pc.pos, "a variable is bound twice in the case")
      _ <- forEachOk(pc.binders)(b =>
        guard(
          !others.contains(b) && !env.cons.contains(b) && !env.funs.contains(b),
          pc.pos,
          s"'$b' is already used (as a theorem variable, constructor or function); choose a fresh name"
        )
      )
      consts = pc.binders.zip(con.argTypes).toMap
      // the goal for this case, and the hypotheses: one per argument of the induction type
      goalOf = (t: Term) => (sub: Term) => Terms.subst(Map(x -> sub), t)
      caseTerm = App(con.name, pc.binders.map(Var(_)))
      goal = (goalOf(thm.lhs)(caseTerm), goalOf(thm.rhs)(caseTerm))
      ihs = pc.binders.zip(con.argTypes).collect { case (b, t) if t == data.name =>
        (goalOf(thm.lhs)(Var(b)), goalOf(thm.rhs)(Var(b)))
      }
      _ <- guard(
        pc.ihs == ihs,
        pc.pos,
        if ihs.isEmpty then "this case has no induction hypothesis, but one is written"
        else if pc.ihs.isEmpty then s"missing induction hypothesis: expected ${showIHs(ihs)}"
        else s"wrong induction hypothesis: expected ${showIHs(ihs)}, found ${showIHs(pc.ihs)}"
      )
      // the IH is a fixed fact: Chains turns it into a rule without quantified variables
      ctx = Chains.Ctx(env, lemmas, ihs, others ++ consts)
      _ <- Chains.check(ctx, pc.chain, goal._1, goal._2)
    yield ()
