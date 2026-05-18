# Lean TRE-to-TA proof

This directory contains a Lean 4 port of the Isabelle/HOL proof under
`proof/` on the `isabelle` branch of `MasWag/tre2ta`.

## Build

```sh
cd proof-lean
lake build
```

Local unfinished-proof check:

```sh
grep -R "sorry\\|admit" LeanTre2Ta || true
```

The project uses Lean 4.29.1 and mathlib. In sandboxed environments where
`elan` cannot write to its default settings file, invoking the Lake binary from
the installed Lean toolchain directly may be necessary.

## Source Isabelle Theories

The port follows these Isabelle files:

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

## Current Build Milestone

The checked Lean root currently covers the base automata, union, trimming, time
restriction, concatenation, Kleene plus/star, and equality-label
intersection/product milestones:

- `emptyTA_lang`
- `epsilonTA_lang`
- `atomTA_lang`
- `unionTagged_correct`
- `trim_correct`
- `timeRestrict_correct`
- `concat_correct`
- `plus_correct`
- `star_correct`
- `LabelAlgebra.runFromL_eq_iff`
- `LabelAlgebra.runLang_eq_lang`
- `product_correct`
- `product_correct_eq`
- `compile_correct`
- `compile_trim_correct`

## Main theorem

```lean
theorem compile_correct [DecidableEq α] (r : TRE α) :
    (compile r).lang = TRE.lang r

theorem compile_trim_correct [DecidableEq α] (r : TRE α) :
    (trimToAccepting (compile r).aut).lang = TRE.lang r
```

## What Is Proved

The Lean development defines intervals, delay-based timed words, TRE syntax,
denotational TRE semantics, timed-automaton syntax, and an operational run
relation. `Automaton.lang` is defined from `AcceptsRun`; automata do not carry
an extensional language field. The checked compiler theorem covers
`Empty`, `Epsilon`, `Atom`, `Union`, recursive `Concat`, `KleenePlus`,
`KleeneStar`, `Within`, and `Intersection`.

The product proof is operational through `RunFromL` and `Automaton.langL`, then
specialized back to the ordinary equality-label `Automaton.lang` semantics. The
public compiler uses `productTA`, which places the two component
automata into disjoint even/odd clock namespaces before synchronizing them.
The trimming proof is operational through `RunFrom` and `AcceptsRun`.

## Construction Notes

The concatenation proof uses tagged `Sum` locations. Its switching transition
consumes the event that completes the left component, maps the right component
into a separated clock namespace, and resets that right-clock namespace before
entering an initial right state. This matches the Rust construction's handoff
discipline more closely than the earlier all-clock reset model.

The Kleene proof is also proof-oriented: `plusTA` is the disjoint union of all
positive powers built from the proved concatenation construction, and `starTA`
is epsilon-or-plus. The Rust construction instead uses a primitive restart-loop
automaton for plus.

The time-restriction proof shifts every input clock by one and reserves clock
`0` as the fresh duration clock. Original transitions remain available for
continuing runs, while guarded duplicate transitions enter a fresh accepting
sink when the total elapsed duration is in the interval. Empty-word acceptance
is handled by making the sink initial exactly when the original automaton
accepts `[]` and `0` satisfies the interval.

The product theorem used by the public compiler is `product_correct`,
which renames clocks before taking the product.

## Scope

The checked Lean proof currently covers:

- Empty
- Epsilon
- Atom
- Union
- Within
- Concat
- KleenePlus
- KleeneStar
- Intersection, for equality labels in the compiler
- `trimToAccepting`

The Isabelle source proof under `proof/` covers the broader mathematical
construction.

## Out of scope

This Lean proof is about the mathematical TRE-to-TA construction. It does not
verify the Rust implementation, parser, DOT export, JANI export, WASM wrapper,
or CLI.
