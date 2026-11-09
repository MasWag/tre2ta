# Lean proof of TRE-to-TA translation

This directory contains a Lean 4 formalization of the mathematical construction
of timed automata (TAs) from timed regular expressions (TREs). It proves that
the compiler preserves the language of a TRE and that trimming locations
that cannot reach an accepting location preserves that language.

The development verifies the abstract Lean construction, not the Rust
implementation.

## Build

From the repository root:

```sh
cd proof
lake build
```

The Lean toolchain is pinned in [`lean-toolchain`](lean-toolchain), and the
mathlib dependency is specified in [`lakefile.lean`](lakefile.lean).
The [Lean Proof workflow](../.github/workflows/lean.yml) builds the project
and checks that the proofs contain no `sorry` or `admit` placeholders.

## Main correctness theorems

The compiler returns a `SomeAutomaton`, which packages the automaton together
with its location type. The central results in
[`TRE/Compile.lean`](LeanTre2Ta/TRE/Compile.lean) are:

```lean
theorem compile_correct [DecidableEq α] (r : TRE α) :
    (compile r).lang = TRE.lang r

theorem compile_trim_correct [DecidableEq α] (r : TRE α) :
    (trimToAccepting (compile r).aut).lang = TRE.lang r
```

`TRE.lang` defines the language of a TRE recursively, while `Automaton.lang`
is defined through operational acceptance (`AcceptsRun`). Timed words are
represented as sequences of nonnegative delays. The compiler theorem covers
all TRE constructors: `empty`, `epsilon`, `atom`, `union`, `inter`, `concat`,
`star`, `plus`, and `within`.

## Source layout

- [`LeanTre2Ta/Basic/`](LeanTre2Ta/Basic/): intervals, delay-based timed words,
  and language operations.
- [`LeanTre2Ta/TimedAutomata/`](LeanTre2Ta/TimedAutomata/): timed-automata
  syntax and run semantics, label algebra, and automaton combinators.
- [`LeanTre2Ta/TimedAutomata/Constructions/`](LeanTre2Ta/TimedAutomata/Constructions/):
  trimming, time restriction, concatenation, Kleene closure, and intersection,
  with their correctness proofs.
- [`LeanTre2Ta/TRE/`](LeanTre2Ta/TRE/): TRE syntax, language semantics,
  the recursive compiler, and its correctness proofs.

## Construction notes

- **Union** uses tagged locations to keep the two components disjoint.
- **Concatenation** also uses tagged locations, but *shares* the clock
  namespace. A switching transition consumes the final event of the left
  operand and resets the right operand's clocks. The correctness proof uses
  `guardsClosed` to ensure the right operand only tests its declared clocks.
- **Kleene plus** duplicates transitions into accepting locations to restart
  at an initial location. Its Lean reset set is `Set.univ` because clock
  valuations are total functions; Kleene star adds acceptance of the empty
  word to this construction.
- **Time restriction** shifts the operand's clocks by one, reserves clock `0`
  for elapsed duration, and guards transitions into a new accepting sink.
  Empty-word acceptance is preserved exactly when the operand accepts the
  empty word and the interval contains zero.
- **Intersection** synchronizes transitions in a product automaton, renaming
  clocks into disjoint even/odd namespaces. `product_correct` proves the
  construction for a `LabelAlgebra`; `product_correct_eq` specializes it to
  equality-based labels, as used by `compile`.
- **Trimming** removes locations from which no accepting location is
  reachable; `trim_correct` proves language preservation.

## Scope

The compiler currently uses equality-based label synchronization. Although
the generic product theorem handles a label algebra, the compiler theorem
does not formalize application-specific spatial-label semantics or a separate
terminal-`$` normalization step.

The Lean proof does not verify the Rust implementation, parser, DOT or JANI
export, or WASM wrapper.
