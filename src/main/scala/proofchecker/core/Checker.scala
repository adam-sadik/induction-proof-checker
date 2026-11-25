package proofchecker.core

import proofchecker.ast.*

/** Entry point of the trusted core: checks definitions, then each theorem in file order. */
object Checker:

  def check(p: Program): Either[ProofError, Unit] =
    Defs.checkAll(p).flatMap { env =>
      // a theorem becomes a usable lemma only after its own proof has been checked
      p.theorems
        .foldLeft[Either[ProofError, Map[String, Theorem]]](Right(Map.empty)) { (lemmas, thm) =>
          lemmas.flatMap { ls =>
            if ls.contains(thm.name) then Left(ProofError(thm.pos, s"theorem '${thm.name}' is declared twice"))
            else Induction.checkTheorem(env, ls, thm).map(_ => ls + (thm.name -> thm))
          }
        }
        .map(_ => ())
    }
