package proofchecker.core

import proofchecker.ast.*
import proofchecker.ast.Term.*
import proofchecker.ast.Pattern.*

/**
 * Checks of data and function declarations. Together they guarantee that every function is
 * total, deterministic (no overlapping equations) and terminating (structural recursion),
 * which is what makes using a definition as a rewrite rule sound.
 */
object Defs:

  private type Result[A] = Either[ProofError, A]

  private def guard(ok: Boolean, pos: Pos, msg: => String): Result[Unit] =
    if ok then Right(()) else Left(ProofError(pos, msg))

  private def at[A](pos: Pos, r: Either[String, A]): Result[A] =
    r.left.map(ProofError(pos, _))

  /** Runs `f` on each element in order, stopping at the first error. */
  private def forEachOk[A](xs: List[A])(f: A => Result[Unit]): Result[Unit] =
    xs.foldLeft[Result[Unit]](Right(()))((acc, x) => acc.flatMap(_ => f(x)))

  def checkAll(p: Program): Result[Env] =
    checkData(p.datas).flatMap(env0 =>
      p.defs.foldLeft[Result[Env]](Right(env0))((acc, f) => acc.flatMap(checkDef(_, f)))
    )

  // ---- data ----

  def checkData(datas: List[DataDecl]): Result[Env] =
    val typeNames = datas.map(_.name).toSet
    val env0 = Env.empty
    datas.foldLeft[Result[Env]](Right(env0)) { (acc, d) =>
      acc.flatMap { env =>
        for
          _ <- guard(!env.datas.contains(d.name), d.pos, s"type '${d.name}' is declared twice")
          _ <- forEachOk(d.cons) { c =>
            for
              _ <- guard(!env.cons.contains(c.name), d.pos, s"constructor '${c.name}' is declared twice")
              _ <- forEachOk(c.argTypes)(t => guard(typeNames(t), d.pos, s"unknown type '$t'"))
            yield ()
          }
          _ <- guard(
            d.cons.map(_.name).distinct.length == d.cons.length,
            d.pos,
            s"type '${d.name}' has two constructors with the same name"
          )
        yield env.copy(
          datas = env.datas + (d.name -> d),
          cons = env.cons ++ d.cons.map(c => c.name -> (c, d.name))
        )
      }
    }

  // ---- functions ----

  /** Checks `f` against the functions declared before it (and itself); returns the extended env. */
  def checkDef(env: Env, f: FunDef): Result[Env] =
    val withF = env.copy(funs = env.funs + (f.name -> f))
    for
      _ <- guard(
        !env.funs.contains(f.name) && !env.cons.contains(f.name),
        f.pos,
        s"'${f.name}' is already declared"
      )
      _ <- forEachOk(f.retType :: f.paramTypes)(t =>
        guard(env.datas.contains(t), f.pos, s"unknown type '$t'")
      )
      _ <- forEachOk(f.eqs)(checkEquation(withF, f, _))
      _ <- checkOverlap(f)
      _ <- checkCoverage(env, f)
      _ <- checkRecursion(f)
    yield withF

  private def checkEquation(env: Env, f: FunDef, eq: Equation): Result[Unit] =
    for
      _ <- guard(
        eq.pats.length == f.paramTypes.length,
        eq.pos,
        s"'${f.name}' takes ${f.paramTypes.length} argument(s), but the equation has ${eq.pats.length}"
      )
      vars <- at(eq.pos, bindAll(env, eq.pats.zip(f.paramTypes), Map.empty))
      ty   <- at(eq.pos, env.typeOf(vars, eq.rhs))
      _ <- guard(ty == f.retType, eq.pos, s"right-hand side has type $ty, expected ${f.retType}")
    yield ()

  /** Types the patterns against the parameter types, collecting the variable types. */
  private def bindAll(
      env: Env,
      pats: List[(Pattern, String)],
      acc: Map[String, String]
  ): Either[String, Map[String, String]] =
    pats.foldLeft[Either[String, Map[String, String]]](Right(acc)) { case (a, (p, ty)) =>
      a.flatMap(bind(env, p, ty, _))
    }

  private def bind(
      env: Env,
      pat: Pattern,
      ty: String,
      acc: Map[String, String]
  ): Either[String, Map[String, String]] = pat match
    case PVar(x) =>
      if env.cons.contains(x) then Left(s"'$x' is a constructor; declare data types before using them")
      else if acc.contains(x) then Left(s"variable '$x' occurs twice in the patterns")
      else Right(acc + (x -> ty))
    case PCon(c, args) =>
      env.cons.get(c) match
        case None => Left(s"unknown constructor '$c'")
        case Some((_, owner)) if owner != ty =>
          Left(s"constructor '$c' builds a $owner, but a $ty is expected here")
        case Some((con, _)) if con.argTypes.length != args.length =>
          Left(s"constructor '$c' takes ${con.argTypes.length} argument(s), got ${args.length}")
        case Some((con, _)) => bindAll(env, args.zip(con.argTypes), acc)

  // ---- overlap ----

  /** Two patterns overlap if some value matches both. Patterns are linear, so this is structural. */
  private def overlaps(p: Pattern, q: Pattern): Boolean = (p, q) match
    case (PVar(_), _) | (_, PVar(_)) => true
    case (PCon(c, as), PCon(d, bs))  => c == d && as.zip(bs).forall(overlaps)

  private def checkOverlap(f: FunDef): Result[Unit] =
    val pairs = for
      (e1, i) <- f.eqs.zipWithIndex
      e2      <- f.eqs.drop(i + 1)
      if e1.pats.zip(e2.pats).forall(overlaps)
    yield (e1, e2)
    pairs.headOption match
      case None => Right(())
      case Some((e1, e2)) =>
        Left(ProofError(e2.pos, s"equation overlaps with the one at line ${e1.pos.line}: " +
          s"'${f.name}(${e1.pats.map(_.show).mkString(", ")})' and " +
          s"'${f.name}(${e2.pats.map(_.show).mkString(", ")})' can match the same arguments"))

  // ---- totality ----

  private def checkCoverage(env: Env, f: FunDef): Result[Unit] =
    missing(env, f.eqs.map(_.pats), f.paramTypes) match
      case None => Right(())
      case Some(w) =>
        Left(ProofError(f.pos, s"'${f.name}' is not total: no equation for " +
          s"'${f.name}(${w.map(_.show).mkString(", ")})'"))

  /** A vector of patterns (with `_` wildcards) matched by no row, if there is one. */
  private def missing(env: Env, rows: List[List[Pattern]], types: List[String]): Option[List[Pattern]] =
    types match
      case Nil => if rows.isEmpty then Some(Nil) else None
      case ty :: rest =>
        val allVars = rows.forall(_.head.isInstanceOf[PVar])
        if allVars then missing(env, rows.map(_.tail), rest).map(PVar("_") :: _)
        else
          env.datas(ty).cons.iterator.flatMap { c =>
            val n = c.argTypes.length
            val specialized = rows.collect {
              case PCon(d, args) :: tl if d == c.name => args ++ tl
              case PVar(_) :: tl                      => List.fill(n)(PVar("_")) ++ tl
            }
            missing(env, specialized, c.argTypes ++ rest).map(w => PCon(c.name, w.take(n)) :: w.drop(n))
          }.nextOption()

  // ---- structural recursion ----

  private def patVars(p: Pattern): List[String] = p match
    case PVar(x)       => List(x)
    case PCon(_, args) => args.flatMap(patVars)

  /** Variables bound strictly inside a constructor pattern, i.e. strict subterms of the argument. */
  private def strictVars(p: Pattern): Set[String] = p match
    case PVar(_)       => Set.empty
    case PCon(_, args) => args.flatMap(patVars).toSet

  private def callsTo(name: String, t: Term): List[List[Term]] = t match
    case Var(_) => Nil
    case App(g, args) =>
      (if g == name then List(args) else Nil) ++ args.flatMap(callsTo(name, _))

  private def decreases(eq: Equation, call: List[Term], j: Int): Boolean =
    call(j) match
      case Var(x) => strictVars(eq.pats(j)).contains(x)
      case _      => false

  /**
   * All recursive calls must decrease the same argument position `j`: the argument must be a
   * variable bound strictly inside the pattern at `j`. Letting each call pick its own position
   * is unsound (the arguments could swap forever).
   */
  private def checkRecursion(f: FunDef): Result[Unit] =
    val calls = f.eqs.flatMap(eq => callsTo(f.name, eq.rhs).map(eq -> _))
    val common = f.paramTypes.indices.exists(j => calls.forall((eq, c) => decreases(eq, c, j)))
    if common then Right(())
    else
      val alone = calls.find((eq, c) => !f.paramTypes.indices.exists(decreases(eq, c, _)))
      alone match
        case Some((eq, c)) =>
          Left(ProofError(eq.pos, s"recursion is not structural: in the call " +
            s"'${App(f.name, c).show}', no argument is a strict subterm of the matching pattern"))
        case None =>
          Left(ProofError(f.pos, s"recursion is not structural: the recursive calls of " +
            s"'${f.name}' do not all decrease the same argument"))
