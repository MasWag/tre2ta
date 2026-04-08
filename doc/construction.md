# Note on the construction of timed automata from TREs

This document describes the TRE-to-TA construction currently implemented by `tre2ta`.

It is intentionally scoped to the crate's present Rust data structures:

- locations with numeric ids,
- multiple initial locations,
- accepting flags on locations,
- labeled transitions,
- clock guards over indexed clocks,
- and clock resets.

## 1. Translation overview

For a timed regular expression `r`, let `TA(r)` be its translated timed
automaton.
The recursive translation is:

- `TA(Empty)` = empty automaton,
- `TA(Epsilon)` = automaton accepting only the empty timed word,
- `TA(Atom(a))` = automaton accepting the one-event timed word labeled `a`,
- `TA(r1 | r2)` = `disjunction(TA(r1), TA(r2))`,
- `TA(r1 & r2)` = `conjunction(TA(r1), TA(r2))`,
- `TA(r1 ; r2)` = `concatenate(TA(r1), TA(r2))`,
- `TA(r+)` = `plus(TA(r))`,
- `TA(r*)` = `star(TA(r))`,
- `TA(r % I)` = `time_restriction(TA(r), I)`.

This document focuses on those base automata and combinators.

The public `translate` function adds two boundary steps around that
construction:

1. it validates the input TRE, and
2. it applies `trim_to_accepting()` to the final translated automaton before
   returning it.

So the public API behaves as:

```text
translate(r) = trim_to_accepting(TA(r)).
```

This cleanup step matters because some constructors intentionally create
presentation-only dead structure, especially in `time_restriction`, and that
structure is removed before the public result is returned.

## 2. Automaton model

The current crate uses a timed automaton

```text
A = (Q, Q0, F, C, E)
```

with:

- `Q` a finite set of locations,
- `Q0 ⊆ Q` the initial locations,
- `F ⊆ Q` the accepting locations,
- `C = {0, 1, ..., k-1}` the clocks,
- `E` the transitions.

A transition has the form

```text
q --(l, g, R)--> q'
```

where:

- `l` is a label,
- `g` is a conjunction of clock constraints,
- `R ⊆ C` is the set of clocks reset by the transition.

In Rust this corresponds to `TimedAutomaton<L>`, `Location`, `Transition<L>`, and `ClockConstraint`.



## 3. Empty-word acceptance

An automaton accepts the empty timed word exactly when one of its initial locations is accepting:

```text
accepts_empty_word(A) iff Q0 ∩ F ≠ ∅.
```

Implementation-wise, this is a scan over `initial_locations`.
This predicate is used in concatenation and time restriction.



## 4. Base automata

The implementation fixes the base cases as follows.

### Empty

`empty_automaton()` has one initial non-accepting location and no transitions.

### Epsilon

`epsilon_automaton()` has one initial accepting location and no transitions.

### Atom

`atom_automaton(a)` has two locations:

- an initial non-accepting source,
- an accepting target,
- one transition labeled `a` from the source to the target.



## 5. Disjunction

`disjunction(A1, A2)` is the disjoint union of the two automata.

- The right operand's location ids are shifted by `|Q1|`.
- Initial locations are the union of both shifted initial sets.
- Accepting locations are preserved from both sides.
- Transitions are copied unchanged except for the right-side location shift.
- The resulting clock dimension is `max(k1, k2)`.

No synchronization is performed.

### Language intuition

A run starts in either operand and then follows that operand alone.



## 6. Conjunction

`conjunction(A1, A2)` is a reachable synchronous product.

- States are reachable pairs `(q1, q2)`.
- Initial states are all pairs in `Q0^1 × Q0^2`.
- A pair is accepting iff both components are accepting.
- The resulting clock dimension is `k1 + k2`.
- Left clocks keep their indices.
- Right clocks are shifted by `k1`.

### Label synchronization

The current implementation does not synchronize on label equality directly.
Instead it uses the `LabelIntersect` trait:

```rust
pub trait LabelIntersect: Clone {
    fn intersect(&self, other: &Self) -> Option<Self>;
}
```

For a pair of transitions

```text
q1 --(l1, g1, R1)--> q1'
q2 --(l2, g2, R2)--> q2'
```

the product contains a synchronized transition only when `l1.intersect(l2)` is non-empty.
If that intersection returns `Some(l)`, the product transition is:

```text
(q1, q2) --(l, g1 ∧ shift(g2), R1 ∪ shift(R2))--> (q1', q2')
```

Singleton-style labels recover equality as a special case.
For example, the built-in `String` implementation returns `Some(label)` only when the two strings are equal.

### Implementation note

The conceptual product is the Cartesian product, but the code constructs only reachable pairs using a worklist and a memo table from state pairs to product ids.



## 7. Concatenation

`concatenate(A1, A2)` starts in the left operand and may hand off to the right operand whenever a left transition enters a left accepting location.

- The right operand is copied with location ids shifted by `|Q1|`.
- The right clocks are shifted by `k1`.
- The resulting clock dimension is `k1 + k2`.
- Every original transition of both operands is kept.

For each left transition

```text
p --(l, g, R)--> f
```

with `f` accepting in `A1`, and for each initial state `q0 ∈ Q0^2`, the construction adds

```text
p --(l, g, R ∪ shift(C2))--> q0.
```

Thus entering the right factor resets all right-side clocks.

All former accepting locations of the left factor are then made non-accepting.
If `A1` accepts the empty timed word, the shifted initial locations of `A2` are also initial in the result.

### Design note

The handoff is expressed by duplicating and redirecting transitions rather than by adding explicit epsilon edges.
That choice is semantic, not merely notational, and the implementation preserves it.



## 8. Empty-Or

`empty_or(A)` adds a fresh initial accepting location with no outgoing transitions.

This adds acceptance of the empty timed word without changing the rest of the automaton.



## 9. Kleene Plus

`plus(A)` duplicates transitions that enter accepting locations back to every initial location.

For each transition

```text
p --(l, g, R)--> f
```

with `f` accepting, and for each initial location `q0`, it adds

```text
p --(l, g, R ∪ C)--> q0.
```

All clocks are reset on the restart transition.
Original accepting locations remain accepting.

### Design note

As in concatenation, repetition is encoded by redirecting observed transitions, not by adding epsilon moves.



## 10. Kleene Star

`star(A)` is implemented as

```text
empty_or(plus(A)).
```

This matches the identity `r* = ε | r+`.



## 11. Time Restriction

`time_restriction(A, I)` constrains the total duration of an accepting run using a fresh clock.

- If `A` has `k` clocks, the result has `k + 1`.
- The fresh clock has index `k`.
- The fresh clock is never reset by this construction.
- A fresh accepting sink location is added.

For every transition

```text
p --(l, g, R)--> f
```

whose target `f` is accepting in `A`, a second transition is added:

```text
p --(l, g ∧ G_I, R)--> f_new
```

where `G_I` is the guard induced by the interval `I` on the fresh clock.
All old accepting locations are made non-accepting.

In `TA(r % I)`, the original transition into `f` is still present and the
redirected transition to `f_new` is added alongside it. A later cleanup pass
may trim away dead non-accepting remnants of that construction before the
automaton is returned by the public API.

### Interval guards

For an interval with lower bound `lo` and optional upper bound `hi`:

- the lower part becomes `clock >= lo` or `clock > lo`,
- the upper part becomes `clock <= hi` or `clock < hi` when present.

### Empty-word case

If the source automaton accepts the empty word, then the restricted automaton accepts the empty word exactly when `0` satisfies the interval.
When that holds, empty-word acceptance is reintroduced via `empty_or`.



## 12. Rust API shape

The public entry point is:

```rust
pub fn translate<L: LabelIntersect>(
    expr: &TimedRegex<L>,
) -> Result<TimedAutomaton<L>, Error>;
```

Operationally, the public boundary is:

```text
translate(expr):
  1. validate expr
  2. build TA(expr) with the internal combinators
  3. return trim_to_accepting(TA(expr))
```

The combinators themselves remain internal helpers in `src/translate.rs`, and
Sections 4-11 describe the translated automaton `TA(expr)` before that final
cleanup postprocessing step.
