# Lean TRE-to-TA proof

This directory contains a Lean 4 port of the self-contained Isabelle/HOL proof
under `proof/` on the `isabelle` branch of `MasWag/tre2ta`.  The development
proves the mathematical TRE-to-TA construction; it does not verify the Rust
implementation itself.

## Build

```sh
cd proof-lean
lake build
```

The project uses Lean 4.29.1 and mathlib.  A local unfinished-proof check is:

```sh
grep -R "sorry\\|admit" LeanTre2Ta || true
```

In sandboxed environments where `elan` cannot write to its default settings
file, it may be necessary to invoke the Lake binary from the installed Lean
toolchain directly.

## Main Theorems

The public compiler packages automata with their location type:

```lean
structure SomeAutomaton (α : Type u) where
  Loc : Type
  aut : Automaton Loc α
```

The main correctness theorems are:

```lean
theorem compile_correct [DecidableEq α] (r : TRE α) :
    (compile r).lang = TRE.lang r

theorem compile_trim_correct [DecidableEq α] (r : TRE α) :
    (trimToAccepting (compile r).aut).lang = TRE.lang r
```

`Automaton.lang` is defined from the operational acceptance relation
`AcceptsRun`; automata do not contain a stored extensional language field.

## What Is Proved

The Lean development defines:

- intervals over real-valued durations;
- delay-based timed words and their duration;
- timed regular expression syntax and denotational semantics;
- timed-automaton syntax, clock valuations, guards, transitions, and runs;
- the TRE-to-TA constructions for all TRE constructors;
- co-reachability trimming by `trimToAccepting`.

The compiler theorem covers:

- `Empty`
- `Epsilon`
- `Atom`
- `Union`
- `Intersection`
- `Concat`
- `KleeneStar`
- `KleenePlus`
- `Within`

The main construction theorems are:

- `emptyTA_lang`
- `epsilonTA_lang`
- `atomTA_lang`
- `union_correct`
- `trim_correct`
- `timeRestrict_correct`
- `concat_correct`
- `plus_correct`
- `star_correct`
- `product_correct`
- `product_correct_eq`

## Construction Notes

Union uses tagged locations internally, so the two component automata cannot
collide at shared location names.

Time restriction shifts the input automaton's clocks by one and reserves clock
`0` as the fresh duration clock.  Guarded duplicate transitions enter a fresh
accepting sink when the total elapsed duration is in the interval.  Empty-word
acceptance is handled by making that sink initial exactly when the original
automaton accepts `[]` and `0` belongs to the interval.

Concatenation uses tagged locations.  A switching transition consumes the event
that completes the left component, enters an initial right state, and resets the
renamed right-clock namespace.  This matches the Rust construction's handoff
discipline while keeping the Lean clock namespaces separated for the proof.

Kleene plus uses a primitive restart-loop construction.  `plusTA` keeps the
original automaton and adds duplicate transitions from transitions entering
accepting states back to initial states.  These duplicate transitions consume
the same event and reset the semantic clock valuation before the next
iteration.  In Lean the restart reset set is `Set.univ`, because valuations are
total functions `Clock → ℝ`; this is the assumption-free analogue of resetting
all allocated clocks.  Kleene star is defined as epsilon-or-plus.

Intersection is proved using a label-algebraic run semantics.  The generic
product theorem is `product_correct`; `product_correct_eq` specializes it to
ordinary equality labels used by the public compiler.  The product construction
places component clocks into disjoint even/odd namespaces before synchronizing
transitions.

## Relation to Isabelle

The Lean port follows these Isabelle theories:

- `Interval.thy`
- `Timed_Word.thy`
- `TRE_Syntax.thy`
- `TRE_Semantics.thy`
- `TA_Syntax.thy`
- `TA_Semantics.thy`
- `TA_Combinators.thy`
- `Trim.thy`
- `Time_Restriction.thy`
- `Concat.thy`
- `Kleene.thy`
- `Label_Algebra.thy`
- `Intersection.thy`

## Out of Scope

This proof does not verify:

- the Rust implementation;
- the parser;
- DOT export;
- JANI export;
- the WASM wrapper;
- the CLI.
