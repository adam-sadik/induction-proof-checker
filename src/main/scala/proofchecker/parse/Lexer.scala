package proofchecker.parse

import scala.annotation.tailrec
import proofchecker.ast.{Pos, ProofError}

enum Tok:
  case Id(name: String)
  case Kw(name: String)
  case Sym(text: String)
  case Eof

  def show: String = this match
    case Id(n)  => s"'$n'"
    case Kw(n)  => s"'$n'"
    case Sym(s) => s"'$s'"
    case Eof    => "end of file"

final case class Token(kind: Tok, pos: Pos)

object Lexer:
  val keywords: Set[String] = Set(
    "data", "def", "theorem", "forall", "proof", "by", "induction", "on",
    "case", "qed", "lemma", "IH"
  )

  // two-character symbols first, so "->" is not read as '-' then '>'
  private val symbols = List("->", "<-", "=", "|", "(", ")", ",", ":", ".", "[", "]")

  private def isIdStart(c: Char) = c.isLetter || c == '_'
  private def isIdPart(c: Char)  = c.isLetterOrDigit || c == '_' || c == '\''

  def tokenize(src: String): Either[ProofError, Vector[Token]] =
    @tailrec
    def go(i: Int, line: Int, col: Int, acc: Vector[Token]): Either[ProofError, Vector[Token]] =
      val here = Pos(line, col)
      if i >= src.length then Right(acc :+ Token(Tok.Eof, here))
      else
        val c = src(i)
        if c == '\n' then go(i + 1, line + 1, 1, acc)
        else if c.isWhitespace then go(i + 1, line, col + 1, acc)
        else if src.startsWith("--", i) then
          val end = src.indexOf('\n', i) match
            case -1 => src.length
            case j  => j
          go(end, line, col + (end - i), acc)
        else if isIdStart(c) then
          val end = src.indexWhere(ch => !isIdPart(ch), i) match
            case -1 => src.length
            case j  => j
          val word = src.substring(i, end)
          val kind = if keywords(word) then Tok.Kw(word) else Tok.Id(word)
          go(end, line, col + word.length, acc :+ Token(kind, here))
        else
          symbols.find(s => src.startsWith(s, i)) match
            case Some(s) => go(i + s.length, line, col + s.length, acc :+ Token(Tok.Sym(s), here))
            case None    => Left(ProofError(here, s"unexpected character '$c'"))
    go(0, 1, 1, Vector.empty)
