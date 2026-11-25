# Conventions

- Scala 3 (3.3.x LTS), sbt, munit. No other dependencies.
- Enums and case classes for data, pattern matching, immutable values, small pure functions,
  `Option` / `Either` for errors. No exceptions for control flow.
- Hand-written tokenizer and recursive-descent parser.
- Comments are short and explain why, not what.

## Layout (`src/main/scala/proofchecker`)
- `ast/`   data types only.
- `parse/` lexer and parser, producing the AST with positions.
- `core/`  the trusted checking core. Depends only on `ast`.
- `cli/`   file reading, error formatting, exit codes.

## Soundness rules
- Functions must be total, non-overlapping and structurally recursive.
- In an induction case, IH variables and case constants are fixed, never match variables.
- A lemma can be used only after its own proof has been checked.
