# induction-proof-checker

A small Scala 3 command-line tool that checks proofs by structural induction (including ordinary induction on the natural numbers) written in a simple text format.

[![CI](https://github.com/adam-sadik/induction-proof-checker/actions/workflows/ci.yml/badge.svg)](https://github.com/adam-sadik/induction-proof-checker/actions/workflows/ci.yml)

```
$ sbt "run examples/add_comm.proof"
OK
```

## Why induction works

### Induction on the natural numbers

Let $\mathbb{N} = \{0, 1, 2, \dots\}$ be the set of natural numbers, ordered by $<$.

**Well-ordering principle.** Every non-empty subset of $\mathbb{N}$ has a least element:

$$\forall S \subseteq \mathbb{N} \quad \Big( S \neq \varnothing \implies \exists m \in S \quad \forall s \in S \quad m \leq s \Big)$$

**Theorem (induction).** Let $P$ be a predicate on $\mathbb{N}$. Then

$$\Big( P(0) \wedge \forall n \in \mathbb{N} \big( P(n) \Rightarrow P(n+1) \big) \Big) \implies \forall n \in \mathbb{N} \quad P(n)$$

*Proof (least counterexample).* Assume the hypothesis

$$\text{(B)} \quad P(0) \qquad \text{and} \qquad \text{(S)} \quad \forall n \in \mathbb{N} \big( P(n) \Rightarrow P(n+1) \big),$$

and suppose, for a contradiction, that $\neg \forall n \in \mathbb{N}\ P(n)$, that is, $\exists n \in \mathbb{N}\ \neg P(n)$. Then the set of counterexamples

$$S = \{ n \in \mathbb{N} \mid \neg P(n) \}$$

is non-empty. By well-ordering, there is $m \in S$ with $m \leq s$ for all $s \in S$. Now:

1. $m \neq 0$, because $P(0)$ holds by (B) while $\neg P(m)$ holds since $m \in S$.
2. Hence $m \geq 1$, so $m = k + 1$ for some $k \in \mathbb{N}$, and $k < m$.
3. By minimality of $m$, $k \notin S$ (otherwise $m \leq k$). So $P(k)$ holds.
4. By (S) applied to $n = k$, we get $P(k+1)$, that is, $P(m)$.

This contradicts $m \in S$, i.e. $\neg P(m)$. Therefore $S = \varnothing$, which means $\forall n \in \mathbb{N}\ P(n)$. $\blacksquare$

### Structural induction on inductive data types

An inductive data type such as

```
data List = Nil | Cons(Nat, List)
```

consists of all **finite** trees built by applying constructors. Every value $v$ has a finite *height*:

$$h(C(a_1, \dots, a_k)) = \begin{cases} 0 & \text{if no } a_i \text{ has type } T \\ 1 + \max \{ h(a_i) \mid a_i \text{ has type } T \} & \text{otherwise} \end{cases}$$

Each argument $a_i$ of the same type $T$ is a *strict subterm* of $C(a_1,\dots,a_k)$, and its height is strictly smaller.

**Theorem (structural induction).** Let $T$ be an inductive type with constructors $C_1, \dots, C_r$, where $C_j$ takes arguments of types $\tau_{j,1}, \dots, \tau_{j,k_j}$, and let $P$ be a predicate on $T$. Write $I_j = \{ i \mid \tau_{j,i} = T \}$ for the positions of the recursive arguments of $C_j$. Then

$$\Big( \forall j \in \{1,\dots,r\} \ \ \forall a_1 \in \tau_{j,1}, \dots, a_{k_j} \in \tau_{j,k_j} \ \ \Big( \bigwedge_{i \in I_j} P(a_i) \Rightarrow P\big(C_j(a_1,\dots,a_{k_j})\big) \Big) \Big) \implies \forall v \in T \quad P(v)$$

The conjunction $\bigwedge_{i \in I_j} P(a_i)$ is the *induction hypothesis*. It is empty (hence true) when $I_j = \varnothing$, and the premise then says $P(C_j(a_1,\dots,a_{k_j}))$ outright: this is a base case.

*Proof.* Assume the premise, and suppose $\exists v \in T\ \neg P(v)$. The set of heights of counterexamples

$$H = \{ h(v) \mid v \in T \text{ and } \neg P(v) \} \subseteq \mathbb{N}$$

is non-empty, so by well-ordering it has a least element $h_0$. Pick a counterexample $v = C_j(a_1,\dots,a_{k_j})$ with $h(v) = h_0$. For every $i \in I_j$ we have $h(a_i) < h(v) = h_0$, so $h(a_i) \notin H$ by minimality, i.e. $P(a_i)$ holds. Thus $\bigwedge_{i \in I_j} P(a_i)$ holds, and the premise for $C_j$ gives $P(v)$. This contradicts $\neg P(v)$. Hence $\forall v \in T\ P(v)$. $\blacksquare$

**Special case.** For $T = \mathsf{Nat}$ with constructors `Zero` ($I_1 = \varnothing$) and `Succ` ($I_2 = \{1\}$), the premise reads $P(\mathsf{Zero}) \wedge \forall a \big( P(a) \Rightarrow P(\mathsf{Succ}(a)) \big)$. Since $h(\mathsf{Succ}^n(\mathsf{Zero})) = n$, this is exactly the ordinary induction principle above.

### What the checker relies on

The checker relies on exactly this principle: **structural induction over the declared `data` types, whose values are finite constructor trees, i.e. the strict subterm order is well-founded.** For a theorem proven by induction on a variable $x : T$ it checks the hypothesis of the theorem above for *every* constructor of $T$, with the induction hypothesis stated for *every* argument of type $T$. It also relies on ordinary equational reasoning (reflexivity, symmetry, transitivity, congruence, instantiation of universally quantified equations), where each use of a definition or lemma is a rewrite step.

## What the tool does and does not do

**Does**

- Parse a proof file and check every definition and every proof in it.
- Print `OK`, or the **first** error with file, line and column and an explanation. The exit code is non-zero on error.

**Does not**

- Search for proofs, suggest steps or automate anything. Every step must be written out and justified.
- Have a GUI, a standard library, polymorphism or arithmetic. Everything is defined in the file.

## The proof format

A file contains `data` declarations, function definitions and theorems. Comments start with `--`.

```
data Nat = Zero | Succ(Nat)

def add : (Nat, Nat) -> Nat
def add(Zero, m)    = m
def add(Succ(n), m) = Succ(add(n, m))

theorem add_zero_right: forall n: Nat. add(n, Zero) = n
proof by induction on n:
  case Zero:
    add(Zero, Zero)
    = Zero                    by def add
  case Succ(k) [IH: add(k, Zero) = k]:
    add(Succ(k), Zero)
    = Succ(add(k, Zero))      by def add
    = Succ(k)                 by IH
qed
```

- `data T = C1(T1, ..., Tn) | C2 | ...` declares a type and its constructors. A constructor name used without arguments is a constant.
- `def f : (T1, ..., Tn) -> R` is followed by one equation `def f(pattern, ...) = term` per case. Patterns are variables or constructors applied to patterns.
- `theorem name: forall x: T, y: U. lhs = rhs` is followed by `proof by induction on x:` and one `case` per constructor of the type of `x`, then `qed`.
- A case is `case C(a1, ..., an) [IH: ...]:` followed by a chain. The names `a1 ... an` are fresh constants standing for the constructor's arguments. The `[IH: ...]` annotation lists the induction hypotheses, one for each argument of the induction type. It is written out for readability, and the checker verifies that it is the right one.
- A chain is a term followed by steps `= term by justification`. It must start at the left-hand side of the goal for that case and end at its right-hand side.

| Justification | Meaning |
|---|---|
| `by def f` | rewrite once with an equation of `f`, left to right |
| `by IH` | rewrite once with an induction hypothesis of this case |
| `by lemma name` | rewrite once with a theorem proven **earlier** in the file |
| `by <- ...` | the same, but right to left |

A step `t1 = t2 by J` is valid exactly when `t2` is obtained from `t1` by applying the rule `J` **once**, at one subterm.

## Quick start

Requirements: JDK 17 or newer and [sbt](https://www.scala-sbt.org/). Dependencies (Scala 3, munit) are downloaded by sbt.

```
sbt compile                                # build
sbt "run examples/add_zero_right.proof"    # check a proof
sbt test                                   # run the tests
```

The exit code is `0` for a valid proof, `1` for a syntax or proof error and `2` for a usage error or an unreadable file.

## How it works

```mermaid
flowchart LR
    src[".proof file"] --> lex["Lexer"]
    lex --> parse["Parser"]
    parse --> ast["AST with positions"]
    ast --> defs["Check definitions<br/>types, overlap, totality,<br/>structural recursion"]
    defs --> thm["For each theorem, in order"]
    thm --> ind["Induction<br/>generate cases, IH"]
    ind --> chain["Chains<br/>check each step"]
    chain --> rw["Terms<br/>matching, one-step rewriting"]
    chain --> ok["OK, or first error<br/>file:line:col"]
```

Pipeline: **parse → check definitions → check proofs**. Only `core/` is trusted, and it depends on nothing but the AST.

Key ideas:

- **Matching.** A rule such as `add(Succ(n), m) = Succ(add(n, m))` has universally quantified variables `n` and `m`. One-way matching finds the substitution that makes the left-hand side equal to a subterm of the current term.
- **One-step rewriting.** `rewriteOnce(rule, t)` returns all terms obtained by applying the rule at exactly one position. A step is valid if the claimed term is among them. When it is not, the error shows what the rule *would* have produced.
- **Case generation.** The checker builds the cases itself from the `data` declaration: one per constructor, none missing, none duplicated. For `Cons(h, t)` the goal is the theorem with `xs := Cons(h, t)`, and the induction hypothesis is the theorem with `xs := t`.
- **IH as constants.** In a case, `k`, `h`, `t` and the other theorem variables are *fixed constants*, not pattern variables. Only definitions and lemmas have quantified variables. So `add(k, Zero) = k` can be used on `add(k, Zero)` but not on `add(j, Zero)` or `add(Succ(k), Zero)`. This reflects the fact that the induction hypothesis is a statement about one specific `k`.

## Soundness

A definition is used as a rewrite rule, so it must be a true statement about the intended meaning of the function. The checker enforces this:

| Check | Why it matters |
|---|---|
| **Non-overlapping equations** | If two equations match the same arguments they can disagree. With `def f(Zero) = Zero` and `def f(n) = Succ(Zero)`, one gets `Zero = f(Zero) = Succ(Zero)`. |
| **Structural recursion** | Recursive calls must be on a strict subterm of a pattern argument, always at the same argument position. Otherwise `def f(n) = Succ(f(n))` would give `f(Zero) = Succ(f(Zero))`, which is false for any natural number. Allowing a different position per equation is unsound too: arguments can swap forever. |
| **Totality** | Every function has a value on every input, so a theorem about `f` says what it appears to say (the intended model is total functions on finite constructor trees). |
| **Types** | Terms are well-typed, so rules are only applied to values of the right type. |
| **Lemmas only after their proof** | A theorem is added to the lemma environment after its own proof has been checked, which rules out circular reasoning. |
| **IH as constants** | Treating IH variables as pattern variables would let the induction hypothesis be applied to *any* term, which proves the theorem without induction. |

With these checks every definition has a unique solution on finite constructor trees, and each step of a proof is an instance of equational reasoning from true equations.

## Examples

Valid proofs are in [`examples/`](examples): `add_zero_right`, `add_succ_right`, `add_comm`, `add_assoc`, `append_nil`, `append_assoc`, `rev_append`, `rev_rev`.

Wrong proofs are in [`examples/invalid/`](examples/invalid), each with the expected message in a `.expected` file. For instance, `wrong_step.proof` justifies `add(Succ(k), Zero) = Succ(k)` by `def add`:

```
examples/invalid/wrong_step.proof:15:5: cannot justify step 'add(Succ(k), Zero) = Succ(k)' by def add: rule gives 'Succ(add(k, Zero))', expected 'Succ(k)'
```

Other cases: a missing induction case, a wrong induction hypothesis, a circular lemma, a chain that stops early, a non-total, non-structural or overlapping definition, and a syntax error.

## Limitations and possible future work

- The induction hypothesis is for the same values of the other variables; it cannot be generalized over them. Theorems that need a generalized hypothesis (for example with an accumulator) cannot be proven directly.
- Induction on one variable per theorem, with no nested induction and no case analysis without induction.
- Recursion is checked with a single decreasing argument. Mutual recursion, lexicographic orders and well-founded recursion are rejected.
- No polymorphic types, conditional equations, or built-in numbers.
- Only the first error is reported.
- Possible future work: lexicographic termination, generalizing variables in the hypothesis, nested induction, polymorphic types, several errors per run.

## Acknowledgements

Inspired by concepts from the CS214 Software Construction course at EPFL (algebraic data types, pattern matching, interpreters) and by the author's interest in mathematics and logical reasoning.

License: [MIT](LICENSE).
