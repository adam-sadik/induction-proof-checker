package proofchecker.core

import proofchecker.ast.*
import proofchecker.ast.Term.*

/** Everything declared so far: data types, constructors and (already checked) functions. */
final case class Env(
    datas: Map[String, DataDecl],
    cons: Map[String, (Constructor, String)], // constructor name -> (constructor, owning type)
    funs: Map[String, FunDef]
):
  /** Parameter types and result type of a constructor or function. */
  def signature(name: String): Option[(List[String], String)] =
    cons.get(name).map((c, owner) => (c.argTypes, owner))
      .orElse(funs.get(name).map(f => (f.paramTypes, f.retType)))

  /** The type of `t`, given the types of its variables. */
  def typeOf(vars: Map[String, String], t: Term): Either[String, String] = t match
    case Var(x) => vars.get(x).toRight(s"unbound variable '$x'")
    case App(f, args) =>
      signature(f) match
        case None => Left(s"unknown function or constructor '$f'")
        case Some((params, ret)) =>
          if params.length != args.length then
            Left(s"'$f' expects ${params.length} argument(s), got ${args.length}")
          else
            args.zip(params).foldLeft[Either[String, Unit]](Right(())) { case (acc, (arg, expected)) =>
              acc.flatMap(_ =>
                typeOf(vars, arg).flatMap(actual =>
                  if actual == expected then Right(())
                  else Left(s"'${arg.show}' has type $actual, expected $expected")
                )
              )
            }.map(_ => ret)

object Env:
  val empty: Env = Env(Map.empty, Map.empty, Map.empty)
