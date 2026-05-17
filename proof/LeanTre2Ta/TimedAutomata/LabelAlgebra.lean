import LeanTre2Ta.TimedAutomata.Semantics

namespace LeanTre2Ta

structure LabelAlgebra (Label Event : Type u) where
  labSem : Label → Set Event
  labelIntersect : Label → Label → Option Label
  intersect_some :
    ∀ {l₁ l₂ l}, labelIntersect l₁ l₂ = some l →
      labSem l = labSem l₁ ∩ labSem l₂
  intersect_none :
    ∀ {l₁ l₂}, labelIntersect l₁ l₂ = none →
      labSem l₁ ∩ labSem l₂ = ∅

namespace LabelAlgebra

def eventMatches (alg : LabelAlgebra Label Event) (l : Label) (e : Event) : Prop :=
  e ∈ alg.labSem l

theorem labelIntersect_complete (alg : LabelAlgebra Label Event)
    {l₁ l₂ : Label} {e : Event}
    (h₁ : alg.eventMatches l₁ e) (h₂ : alg.eventMatches l₂ e) :
    ∃ l, alg.labelIntersect l₁ l₂ = some l ∧ alg.eventMatches l e := by
  unfold eventMatches at h₁ h₂ ⊢
  cases h : alg.labelIntersect l₁ l₂ with
  | none =>
      have hempty := alg.intersect_none h
      have hmem : e ∈ alg.labSem l₁ ∩ alg.labSem l₂ := ⟨h₁, h₂⟩
      have : e ∈ (∅ : Set Event) := by
        rw [← hempty]
        exact hmem
      exact False.elim this
  | some l =>
      have hsem := alg.intersect_some h
      exact ⟨l, rfl, by simpa [hsem] using And.intro h₁ h₂⟩

inductive RunFromL (alg : LabelAlgebra Label Event) :
    Automaton Loc Label → Loc → Valuation → TimedWord Event → Loc → Valuation → Prop
  | nil (A : Automaton Loc Label) (q : Loc) (v : Valuation) :
      RunFromL alg A q v [] q v
  | cons {A : Automaton Loc Label} {p qf : Loc} {v vf : Valuation}
      {d : ℝ} {a : Event} {w : TimedWord Event} (t : Transition Loc Label) :
      t ∈ A.transitions →
      t.source = p →
      alg.eventMatches t.label a →
      0 ≤ d →
      guardsSat (delayVal d v) t.guards →
      RunFromL alg A t.target (resetVal t.resets (delayVal d v)) w qf vf →
      RunFromL alg A p v ((d, a) :: w) qf vf

def runLang (alg : LabelAlgebra Label Event) (A : Automaton Loc Label) :
    Set (TimedWord Event) :=
  {w | ∃ q₀ ∈ A.initial, ∃ qf ∈ A.accepting, ∃ vf,
    RunFromL alg A q₀ zeroVal w qf vf}

def eqLabelIntersect [DecidableEq α] (l₁ l₂ : α) : Option α :=
  if l₁ = l₂ then some l₁ else none

def equality [DecidableEq α] : LabelAlgebra α α where
  labSem l := {l}
  labelIntersect := eqLabelIntersect
  intersect_some := by
    intro l₁ l₂ l h
    unfold eqLabelIntersect at h
    split at h
    · cases h
      ext e
      simp_all
    · contradiction
  intersect_none := by
    intro l₁ l₂ h
    unfold eqLabelIntersect at h
    split at h
    · contradiction
    · ext e
      simp_all

@[simp] theorem equality_eventMatches [DecidableEq α] (l e : α) :
    (equality (α := α)).eventMatches l e ↔ e = l := by
  simp [eventMatches, equality]

theorem runFromL_eq_to_runFrom [DecidableEq α]
    {A : Automaton Loc α} {q qf : Loc} {v vf : Valuation}
    {w : TimedWord α}
    (h : RunFromL (equality (α := α)) A q v w qf vf) :
    RunFrom A q v w qf vf := by
  induction h with
  | nil q v =>
      exact RunFrom.nil _ q v
  | cons t ht hsource hmatch hnonneg hguards htail ih =>
      exact RunFrom.cons t ht hsource
        (by
          have hm := (equality_eventMatches (t.label) _).1 hmatch
          exact hm.symm)
        hnonneg hguards ih

theorem runFrom_to_runFromL_eq [DecidableEq α]
    {A : Automaton Loc α} {q qf : Loc} {v vf : Valuation}
    {w : TimedWord α}
    (h : RunFrom A q v w qf vf) :
    RunFromL (equality (α := α)) A q v w qf vf := by
  induction h with
  | nil q v =>
      exact RunFromL.nil _ q v
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      exact RunFromL.cons t ht hsource
        (by
          rw [hlabel]
          exact (equality_eventMatches _ _).2 rfl)
        hnonneg hguards ih

theorem runFromL_eq_iff [DecidableEq α]
    {A : Automaton Loc α} {q qf : Loc} {v vf : Valuation}
    {w : TimedWord α} :
    RunFromL (equality (α := α)) A q v w qf vf ↔
      RunFrom A q v w qf vf :=
  ⟨runFromL_eq_to_runFrom, runFrom_to_runFromL_eq⟩

theorem runLang_eq_lang [DecidableEq α] (A : Automaton Loc α) :
    runLang (equality (α := α)) A = A.lang := by
  ext w
  constructor
  · intro h
    rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
    exact ⟨q₀, hq₀, qf, hqf, vf, runFromL_eq_to_runFrom hrun⟩
  · intro h
    rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
    exact ⟨q₀, hq₀, qf, hqf, vf, runFrom_to_runFromL_eq hrun⟩

end LabelAlgebra

def EventMatches (alg : LabelAlgebra Label Event) (l : Label) (e : Event) : Prop :=
  alg.eventMatches l e

def AcceptsRunL (alg : LabelAlgebra Label Event) (A : Automaton Loc Label)
    (w : TimedWord Event) : Prop :=
  w ∈ LabelAlgebra.runLang alg A

namespace Automaton

def langL (alg : LabelAlgebra Label Event) (A : Automaton Loc Label) :
    Set (TimedWord Event) :=
  LabelAlgebra.runLang alg A

theorem langL_eq_lang [DecidableEq α] (A : Automaton Loc α) :
    langL (LabelAlgebra.equality (α := α)) A = A.lang :=
  LabelAlgebra.runLang_eq_lang A

end Automaton

end LeanTre2Ta
