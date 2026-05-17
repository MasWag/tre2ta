import LeanTre2Ta.TimedAutomata.Syntax
import LeanTre2Ta.Basic.TimedWord

namespace LeanTre2Ta

inductive RunFrom {Loc : Type u} {Label : Type v} :
    Automaton Loc Label → Loc → Valuation → TimedWord Label → Loc → Valuation → Prop
  | nil (A : Automaton Loc Label) (q : Loc) (v : Valuation) :
      RunFrom A q v [] q v
  | cons {A : Automaton Loc Label} {p qf : Loc} {v vf : Valuation}
      {d : ℝ} {a : Label} {w : TimedWord Label} (t : Transition Loc Label) :
      t ∈ A.transitions →
      t.source = p →
      t.label = a →
      0 ≤ d →
      guardsSat (delayVal d v) t.guards →
      RunFrom A t.target (resetVal t.resets (delayVal d v)) w qf vf →
      RunFrom A p v ((d, a) :: w) qf vf

def AcceptsRun {Loc : Type u} {Label : Type v} (A : Automaton Loc Label)
    (w : TimedWord Label) : Prop :=
  ∃ q₀ ∈ A.initial, ∃ qf ∈ A.accepting, ∃ vf,
    RunFrom A q₀ zeroVal w qf vf

namespace Automaton

def lang {Loc : Type u} {Label : Type v} (A : Automaton Loc Label) :
    Set (TimedWord Label) :=
  {w | AcceptsRun A w}

end Automaton

def emptyTA (α : Type u) : Automaton Nat α :=
  { locations := {0}
    initial := {0}
    accepting := ∅
    clocks := ∅
    transitions := ∅ }

def epsilonTA (α : Type u) : Automaton Nat α :=
  { locations := {0}
    initial := {0}
    accepting := {0}
    clocks := ∅
    transitions := ∅ }

def atomTransition (a : α) : Transition Nat α :=
  { source := 0
    label := a
    guards := []
    resets := ∅
    target := 1 }

def atomTA (a : α) : Automaton Nat α :=
  { locations := {0, 1}
    initial := {0}
    accepting := {1}
    clocks := ∅
    transitions := {atomTransition a} }

theorem runFrom_noTransitions {A : Automaton Loc Label}
    (htrans : A.transitions = ∅)
    (hrun : RunFrom A q v w qf vf) :
    w = [] ∧ qf = q ∧ vf = v := by
  cases hrun with
  | nil =>
      simp
  | cons t ht _ _ _ _ _ =>
      simp [htrans] at ht

@[simp] theorem emptyTA_lang :
    (emptyTA α).lang = (∅ : Set (TimedWord α)) := by
  ext w
  constructor
  · intro h
    rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
    simp [emptyTA] at hqf
  · intro h
    exact False.elim h

@[simp] theorem epsilonTA_lang :
    (epsilonTA α).lang = ({[]} : Set (TimedWord α)) := by
  ext w
  constructor
  · intro h
    rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
    have hw := runFrom_noTransitions (A := epsilonTA α) (by simp [epsilonTA]) hrun
    exact hw.1
  · intro h
    rcases h with rfl
    exact ⟨0, by simp [epsilonTA], 0, by simp [epsilonTA], zeroVal,
      RunFrom.nil (epsilonTA α) 0 zeroVal⟩

@[simp] theorem atomTA_lang (a : α) :
    (atomTA a).lang = {w | ∃ d, 0 ≤ d ∧ w = [(d, a)]} := by
  ext w
  constructor
  · intro h
    rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
    have hq₀' : q₀ = 0 := by simpa [atomTA] using hq₀
    have hqf' : qf = 1 := by simpa [atomTA] using hqf
    subst q₀
    subst qf
    cases hrun with
    | cons t ht hsource hlabel hd hguards htail =>
        have ht' : t = atomTransition a := by simpa [atomTA] using ht
        subst t
        cases hlabel
        cases htail with
        | nil =>
            exact ⟨_, hd, by simp [atomTransition]⟩
        | cons t' ht' hsource' _ _ _ _ =>
            have ht'' : t' = atomTransition a := by simpa [atomTA] using ht'
            subst t'
            norm_num [atomTransition] at hsource'
  · intro h
    rcases h with ⟨d, hd, rfl⟩
    refine ⟨0, by simp [atomTA], 1, by simp [atomTA],
      resetVal (atomTransition a).resets (delayVal d zeroVal), ?_⟩
    exact RunFrom.cons (A := atomTA a) (p := 0) (qf := 1)
      (v := zeroVal)
      (vf := resetVal (atomTransition a).resets (delayVal d zeroVal))
      (d := d) (a := a) (w := [])
      (atomTransition a)
      (by simp [atomTA])
      (by simp [atomTransition])
      (by simp [atomTransition])
      hd
      (by
        intro g hg
        simp [atomTransition] at hg)
      (RunFrom.nil (atomTA a) 1
        (resetVal (atomTransition a).resets (delayVal d zeroVal)))

theorem emptyTA_lang_eq_empty :
    (emptyTA α).lang = (∅ : Set (TimedWord α)) := emptyTA_lang

theorem epsilonTA_lang_eq_singleton :
    (epsilonTA α).lang = ({[]} : Set (TimedWord α)) := epsilonTA_lang

theorem atomTA_lang_eq (a : α) :
    (atomTA a).lang = {w | ∃ d, 0 ≤ d ∧ w = [(d, a)]} := atomTA_lang a

theorem atomTA_wellFormed {a : α} {w : TimedWord α}
    (h : w ∈ (atomTA a).lang) : TimedWord.WellFormed w := by
  have h' : w ∈ {w | ∃ d, 0 ≤ d ∧ w = [(d, a)]} := by
    simpa [atomTA_lang a] using h
  rcases h' with ⟨d, hd, rfl⟩
  simp [TimedWord.WellFormed, hd]

theorem accepted_word_wellFormed_empty {w : TimedWord α}
    (h : w ∈ (emptyTA α).lang) : TimedWord.WellFormed w := by
  have h' : w ∈ (∅ : Set (TimedWord α)) := by
    rw [emptyTA_lang] at h
    exact h
  exact False.elim h'

theorem accepted_word_wellFormed_epsilon {w : TimedWord α}
    (h : w ∈ (epsilonTA α).lang) : TimedWord.WellFormed w := by
  have h' : w ∈ ({[]} : Set (TimedWord α)) := by
    simpa [epsilonTA_lang] using h
  rcases h' with rfl
  simp [TimedWord.WellFormed]

end LeanTre2Ta
