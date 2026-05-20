import LeanTre2Ta.TimedAutomata.Combinators

namespace LeanTre2Ta

def edge (A : Automaton Loc Label) (p q : Loc) : Prop :=
  ∃ t ∈ A.transitions, t.source = p ∧ t.target = q

def reaches (A : Automaton Loc Label) (p q : Loc) : Prop :=
  Relation.ReflTransGen (edge A) p q

def coreachable (A : Automaton Loc Label) (p : Loc) : Prop :=
  ∃ q ∈ A.accepting, reaches A p q

def trimToAccepting (A : Automaton Loc Label) : Automaton Loc Label :=
  { locations := {p | p ∈ A.locations ∧ coreachable A p}
    initial := {p | p ∈ A.initial ∧ coreachable A p}
    accepting := {p | p ∈ A.accepting ∧ coreachable A p}
    clocks := A.clocks
    transitions := {t | t ∈ A.transitions ∧ coreachable A t.source ∧ coreachable A t.target} }

theorem trim_locations_subset (A : Automaton Loc Label) :
    (trimToAccepting A).locations ⊆ A.locations := by
  intro p hp
  exact hp.1

theorem trim_initial (A : Automaton Loc Label) :
    (trimToAccepting A).initial = {p | p ∈ A.initial ∧ coreachable A p} := rfl

theorem accepting_coreachable {A : Automaton Loc Label} {p : Loc}
    (h : p ∈ A.accepting) : coreachable A p :=
  ⟨p, h, Relation.ReflTransGen.refl⟩

theorem trim_accepting (A : Automaton Loc Label) :
    (trimToAccepting A).accepting = A.accepting := by
  ext p
  constructor
  · intro h
    exact h.1
  · intro h
    exact ⟨h, accepting_coreachable h⟩

theorem trim_transition_subset
    {A : Automaton Loc Label} {t : Transition Loc Label}
    (h : t ∈ (trimToAccepting A).transitions) :
    t ∈ A.transitions :=
  h.1

theorem trim_initial_subset
    {A : Automaton Loc Label} {q : Loc}
    (h : q ∈ (trimToAccepting A).initial) :
    q ∈ A.initial :=
  h.1

theorem trim_accepting_subset
    {A : Automaton Loc Label} {q : Loc}
    (h : q ∈ (trimToAccepting A).accepting) :
    q ∈ A.accepting :=
  h.1

theorem runFrom_trim_to_original
    {A : Automaton Loc Label}
    {q qf : Loc} {v vf : Valuation} {w : TimedWord Label}
    (h : RunFrom (trimToAccepting A) q v w qf vf) :
    RunFrom A q v w qf vf := by
  induction h with
  | nil q v =>
      exact RunFrom.nil A q v
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      exact RunFrom.cons t (trim_transition_subset ht) hsource hlabel
        hnonneg hguards ih

theorem trim_lang_subset (A : Automaton Loc Label) :
    (trimToAccepting A).lang ⊆ A.lang := by
  intro w h
  rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
  exact ⟨q₀, trim_initial_subset hq₀, qf, trim_accepting_subset hqf,
    vf, runFrom_trim_to_original hrun⟩

theorem reaches_of_edge {A : Automaton Loc Label} {p q : Loc}
    (h : edge A p q) :
    reaches A p q :=
  Relation.ReflTransGen.single h

theorem reaches_trans {A : Automaton Loc Label} {p q r : Loc}
    (hpq : reaches A p q) (hqr : reaches A q r) :
    reaches A p r :=
  Relation.ReflTransGen.trans hpq hqr

theorem coreachable_of_edge {A : Automaton Loc Label} {p q : Loc}
    (hedge : edge A p q) (hc : coreachable A q) :
    coreachable A p := by
  rcases hc with ⟨r, hr, hqr⟩
  exact ⟨r, hr, reaches_trans (reaches_of_edge hedge) hqr⟩

theorem coreachable_of_run_to_accepting
    {A : Automaton Loc Label}
    {p qf : Loc} {v vf : Valuation} {w : TimedWord Label}
    (hrun : RunFrom A p v w qf vf)
    (hacc : qf ∈ A.accepting) :
    coreachable A p := by
  induction hrun with
  | nil q v =>
      exact accepting_coreachable hacc
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      subst hsource
      exact coreachable_of_edge ⟨t, ht, rfl, rfl⟩ (ih hacc)

theorem runFrom_original_to_trim_of_accepting
    {A : Automaton Loc Label}
    {p qf : Loc} {v vf : Valuation} {w : TimedWord Label}
    (hrun : RunFrom A p v w qf vf)
    (hacc : qf ∈ A.accepting) :
    RunFrom (trimToAccepting A) p v w qf vf := by
  induction hrun with
  | nil q v =>
      exact RunFrom.nil (trimToAccepting A) q v
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      subst hsource
      have htarget : coreachable A t.target :=
        coreachable_of_run_to_accepting htail hacc
      have hsourceCore : coreachable A t.source :=
        coreachable_of_edge ⟨t, ht, rfl, rfl⟩ htarget
      have httrim : t ∈ (trimToAccepting A).transitions :=
        ⟨ht, hsourceCore, htarget⟩
      exact RunFrom.cons t httrim rfl hlabel hnonneg hguards (ih hacc)

theorem original_lang_subset_trim (A : Automaton Loc Label) :
    A.lang ⊆ (trimToAccepting A).lang := by
  intro w h
  rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
  have hq₀core : coreachable A q₀ :=
    coreachable_of_run_to_accepting hrun hqf
  exact ⟨q₀, ⟨hq₀, hq₀core⟩, qf, by
      rw [trim_accepting]
      exact hqf,
    vf, runFrom_original_to_trim_of_accepting hrun hqf⟩

theorem trim_correct (A : Automaton Loc Label) :
    (trimToAccepting A).lang = A.lang :=
  Set.Subset.antisymm (trim_lang_subset A) (original_lang_subset_trim A)

theorem trim_guardsClosed {A : Automaton Loc Label}
    (hA : guardsClosed A) :
    guardsClosed (trimToAccepting A) := by
  intro t ht
  exact hA t ht.1

end LeanTre2Ta
