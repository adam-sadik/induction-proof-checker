# Architecture

```
src/main/scala/proofchecker
  ast/     Syntax.scala    Pos, ProofError, Term, Pattern, DataDecl, FunDef, Theorem, Program
  parse/   Lexer.scala     source text -> tokens with line/column
           Parser.scala    tokens -> Program (recursive descent)
  core/    Env.scala       declared types, constructors, functions; typing of terms
           Terms.scala     substitution, one-way matching, one-step rewriting, Rule
           Defs.scala      checks on data and function declarations
           Chains.scala    checks an equational chain against a goal
           Induction.scala generates induction cases and checks a theorem
           Checker.scala   runs everything in file order
  cli/     Cli.scala       file reading, error formatting, exit codes
           Main.scala      entry point
```

`core/` is the trusted part. It depends only on `ast/`. The parser and the CLI cannot make an invalid proof pass: the checker works on the AST and re-derives everything it relies on (types, induction cases, hypotheses) from the declarations.

## Errors

All errors are `ProofError(pos, msg)`. The parser and the checker return `Either[ProofError, _]` and stop at the first error. Positions are attached to declarations, equations, cases and proof steps (the position of the `=` that starts the step). Terms carry no positions.

## Parsing

The lexer produces `Id`, `Kw`, `Sym` and `Eof` tokens. The parser is a set of mutually recursive functions over a token cursor; a syntax error aborts the parse with `scala.util.boundary`. A bare identifier is read as a constant if it is a constructor declared earlier, so data types must be declared before use.

## Checking definitions (`Defs`)

For each function, in file order:

1. **Types.** Patterns and right-hand sides are type-checked against the signature.
2. **Overlap.** Two equations overlap if their pattern vectors can match the same arguments.
3. **Totality.** A pattern-matrix check finds an argument vector matched by no equation and prints it.
4. **Recursion.** One argument position `j` must work for all recursive calls: the argument at `j` is a variable bound strictly inside the pattern at `j`. Functions can only call themselves or functions defined earlier.

## Checking proofs

- `Terms.matchTerm(vars, pattern, term)` binds only the variables in `vars`. Any other variable is a constant and matches only itself.
- `Terms.rewriteOnce(rule, t)` lists every result of applying a `Rule(vars, lhs, rhs)` at one subterm. A result may not contain a quantified variable that matching left unbound.
- `Chains.check` verifies the start, each step and the end of a chain. A step is valid if the claimed term is in `rewriteOnce` of the previous one for some rule of the justification. Reversed justifications use `Rule.reverse`.
- `Induction.checkTheorem` checks the statement, then the coverage of constructors, then each case: binder count and freshness, the generated goal and induction hypotheses, the written `[IH: ...]` annotation, and finally the chain, with the hypotheses as rules without quantified variables.
- `Checker.check` adds a theorem to the lemma map only after it has been checked.

## Tests

One munit suite per module in `src/test/scala/proofchecker`. `CliSuite` runs every file in `examples/` (expecting `OK`) and every file in `examples/invalid/` (comparing with its `.expected` file).
