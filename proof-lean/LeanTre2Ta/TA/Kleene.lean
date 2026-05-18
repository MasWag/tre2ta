import LeanTre2Ta.TA.Concat

namespace LeanTre2Ta

def PowLoc (Loc : Type u) : Nat → Type u
  | 0 => PUnit
  | n + 1 => Sum Loc (PowLoc Loc n)

def epsilonUnitTA (α : Type u) : Automaton PUnit α :=
  { locations := {PUnit.unit}
    initial := {PUnit.unit}
    accepting := {PUnit.unit}
    clocks := ∅
    transitions := ∅ }

@[simp] theorem epsilonUnitTA_lang :
    (epsilonUnitTA α).lang = ({[]} : Set (TimedWord α)) := by
  ext w
  constructor
  · intro h
    rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
    have hw := runFrom_noTransitions (A := epsilonUnitTA α) (by simp [epsilonUnitTA]) hrun
    exact hw.1
  · intro h
    rcases h with rfl
    exact ⟨PUnit.unit, by simp [epsilonUnitTA], PUnit.unit,
      by simp [epsilonUnitTA], zeroVal,
      RunFrom.nil (epsilonUnitTA α) PUnit.unit zeroVal⟩

def powTA (A : Automaton Loc α) : (n : Nat) → Automaton (PowLoc Loc n) α
  | 0 => epsilonUnitTA α
  | n + 1 => concatTA A (powTA A n)

theorem powTA_correct (A : Automaton Loc α) (n : Nat) :
    (powTA A n).lang = langPow A.lang n := by
  induction n with
  | zero =>
      exact epsilonUnitTA_lang
  | succ n ih =>
      change (concatTA A (powTA A n)).lang = concatLang A.lang (langPow A.lang n)
      rw [concat_correct, ih]

abbrev PlusLoc (Loc : Type u) : Type u :=
  Sigma (fun n : Nat => PowLoc Loc (n + 1))

def tagPowTransition (n : Nat)
    (t : Transition (PowLoc Loc (n + 1)) α) :
    Transition (PlusLoc Loc) α :=
  { source := ⟨n, t.source⟩
    label := t.label
    guards := t.guards
    resets := t.resets
    target := ⟨n, t.target⟩ }

/- This is a proof-oriented positive-closure construction: it is the disjoint
   union of all positive powers of `A`.  It is operational, but not the Rust
   restart-loop construction. -/
def plusTA (A : Automaton Loc α) : Automaton (PlusLoc Loc) α :=
  { locations := {q | q.2 ∈ (powTA A (q.1 + 1)).locations}
    initial := {q | q.2 ∈ (powTA A (q.1 + 1)).initial}
    accepting := {q | q.2 ∈ (powTA A (q.1 + 1)).accepting}
    clocks := A.clocks
    transitions :=
      {u | ∃ n, ∃ t ∈ (powTA A (n + 1)).transitions,
        u = tagPowTransition n t} }

theorem runFrom_lift_plus_pow
    {A : Automaton Loc α} {n : Nat}
    {p q : PowLoc Loc (n + 1)} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (powTA A (n + 1)) p v w q vf) :
    RunFrom (plusTA A) ⟨n, p⟩ v w ⟨n, q⟩ vf := by
  induction h with
  | nil q v =>
      exact RunFrom.nil (plusTA A) ⟨n, q⟩ v
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      exact RunFrom.cons (tagPowTransition n t)
        (by exact ⟨n, t, ht, rfl⟩)
        (by simp [tagPowTransition, hsource])
        (by simp [tagPowTransition, hlabel])
        hnonneg
        (by simpa [tagPowTransition] using hguards)
        (by simpa [tagPowTransition] using ih)

theorem runFrom_project_plus_pow_aux
    {A : Automaton Loc α} {n : Nat}
    {qstart qend : PlusLoc Loc} {p : PowLoc Loc (n + 1)}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (plusTA A) qstart v w qend vf)
    (hstart : qstart = ⟨n, p⟩) :
    ∃ q : PowLoc Loc (n + 1),
      qend = ⟨n, q⟩ ∧ RunFrom (powTA A (n + 1)) p v w q vf := by
  induction h generalizing n p with
  | nil q v =>
      cases hstart
      exact ⟨p, rfl, RunFrom.nil (powTA A (n + 1)) p v⟩
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      rcases ht with ⟨m, tPow, htPow, htEq⟩
      subst htEq
      have hsrc : (⟨m, tPow.source⟩ : PlusLoc Loc) = ⟨n, p⟩ := by
        simpa [tagPowTransition, hstart] using hsource
      cases hsrc
      rcases ih rfl with ⟨q, hqend, htailPow⟩
      exact ⟨q, hqend,
        RunFrom.cons tPow htPow rfl
          (by simpa [tagPowTransition] using hlabel)
          hnonneg
          (by simpa [tagPowTransition] using hguards)
          htailPow⟩

theorem runFrom_project_plus_pow
    {A : Automaton Loc α} {n : Nat}
    {p : PowLoc Loc (n + 1)} {qend : PlusLoc Loc}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (plusTA A) ⟨n, p⟩ v w qend vf) :
    ∃ q : PowLoc Loc (n + 1),
      qend = ⟨n, q⟩ ∧ RunFrom (powTA A (n + 1)) p v w q vf :=
  runFrom_project_plus_pow_aux h rfl

theorem run_lift_plus
    {A : Automaton Loc α}
    {q₀ qf : Loc} {vf : Valuation} {w : TimedWord α}
    (hq₀ : q₀ ∈ A.initial)
    (hqf : qf ∈ A.accepting)
    (hrun : RunFrom A q₀ zeroVal w qf vf) :
    w ∈ (plusTA A).lang := by
  have hw : w ∈ (powTA A 1).lang := by
    simpa [powTA, concatLang] using
      (concat_complete A (epsilonUnitTA α)
        ⟨w, ⟨q₀, hq₀, qf, hqf, vf, hrun⟩,
          [], by simp, by simp⟩)
  rcases hw with ⟨p₀, hp₀, pf, hpf, vfPow, hrunPow⟩
  exact ⟨⟨0, p₀⟩, hp₀, ⟨0, pf⟩, hpf, vfPow,
    runFrom_lift_plus_pow hrunPow⟩

theorem plus_complete (A : Automaton Loc α) :
    plusLang A.lang ⊆ (plusTA A).lang := by
  intro w h
  rcases h with ⟨n, hn⟩
  have hp : w ∈ (powTA A (n + 1)).lang := by
    simpa [powTA_correct A (n + 1)] using hn
  rcases hp with ⟨p₀, hp₀, pf, hpf, vf, hrun⟩
  exact ⟨⟨n, p₀⟩, hp₀, ⟨n, pf⟩, hpf, vf,
    runFrom_lift_plus_pow hrun⟩

theorem plus_sound (A : Automaton Loc α) :
    (plusTA A).lang ⊆ plusLang A.lang := by
  intro w h
  rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
  rcases q₀ with ⟨n, p₀⟩
  rcases runFrom_project_plus_pow hrun with ⟨pf, hqfEq, hrunPow⟩
  subst qf
  have hp : w ∈ (powTA A (n + 1)).lang :=
    ⟨p₀, hq₀, pf, hqf, vf, hrunPow⟩
  exact ⟨n, by simpa [powTA_correct A (n + 1)] using hp⟩

theorem plus_correct (A : Automaton Loc α) :
    (plusTA A).lang = plusLang A.lang :=
  Set.Subset.antisymm (plus_sound A) (plus_complete A)

def starTA (A : Automaton Loc α) : Automaton (Sum Nat (PlusLoc Loc)) α :=
  unionTaggedTA (epsilonTA α) (plusTA A)

theorem star_correct (A : Automaton Loc α) :
    (starTA A).lang = starLang A.lang := by
  rw [starTA, unionTagged_correct, epsilonTA_lang, plus_correct,
    starLang_empty_union_plus]

end LeanTre2Ta
