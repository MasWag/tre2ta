import LeanTre2Ta.TimedAutomata.Semantics

namespace LeanTre2Ta

def mapTransition (f : Loc₁ → Loc₂) (t : Transition Loc₁ Label) :
    Transition Loc₂ Label :=
  { source := f t.source
    label := t.label
    guards := t.guards
    resets := t.resets
    target := f t.target }

def mapLocations (f : Loc₁ → Loc₂) (A : Automaton Loc₁ Label) :
    Automaton Loc₂ Label :=
  { locations := f '' A.locations
    initial := f '' A.initial
    accepting := f '' A.accepting
    clocks := A.clocks
    transitions := mapTransition f '' A.transitions }

def unionTA (A B : Automaton Nat α) : Automaton Nat α :=
  { locations := A.locations ∪ B.locations
    initial := A.initial ∪ B.initial
    accepting := A.accepting ∪ B.accepting
    clocks := A.clocks ∪ B.clocks
    transitions := A.transitions ∪ B.transitions }

/- The untagged `Nat` union above is only a structural helper: it is sound
   under location-disjointness assumptions, but not in general.  The proved
   construction below tags the two location spaces explicitly. -/

def unionTaggedTA (A : Automaton Loc₁ α) (B : Automaton Loc₂ α) :
    Automaton (Sum Loc₁ Loc₂) α :=
  { locations :=
      {q | ∃ p ∈ A.locations, q = Sum.inl p} ∪
      {q | ∃ p ∈ B.locations, q = Sum.inr p}
    initial :=
      {q | ∃ p ∈ A.initial, q = Sum.inl p} ∪
      {q | ∃ p ∈ B.initial, q = Sum.inr p}
    accepting :=
      {q | ∃ p ∈ A.accepting, q = Sum.inl p} ∪
      {q | ∃ p ∈ B.accepting, q = Sum.inr p}
    clocks := A.clocks ∪ B.clocks
    transitions :=
      (mapTransition Sum.inl '' A.transitions) ∪
      (mapTransition Sum.inr '' B.transitions) }

theorem runFrom_left_union
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {q qf : Loc₁} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom A q v w qf vf) :
    RunFrom (unionTaggedTA A B) (Sum.inl q) v w (Sum.inl qf) vf := by
  induction h with
  | nil q v =>
      exact RunFrom.nil (unionTaggedTA A B) (Sum.inl q) v
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      exact RunFrom.cons (mapTransition Sum.inl t)
        (by
          left
          exact ⟨t, ht, rfl⟩)
        (by simp [mapTransition, hsource])
        (by simp [mapTransition, hlabel])
        hnonneg
        (by simpa [mapTransition] using hguards)
        (by simpa [mapTransition] using ih)

theorem runFrom_right_union
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {q qf : Loc₂} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom B q v w qf vf) :
    RunFrom (unionTaggedTA A B) (Sum.inr q) v w (Sum.inr qf) vf := by
  induction h with
  | nil q v =>
      exact RunFrom.nil (unionTaggedTA A B) (Sum.inr q) v
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      exact RunFrom.cons (mapTransition Sum.inr t)
        (by
          right
          exact ⟨t, ht, rfl⟩)
        (by simp [mapTransition, hsource])
        (by simp [mapTransition, hlabel])
        hnonneg
        (by simpa [mapTransition] using hguards)
        (by simpa [mapTransition] using ih)

theorem runFrom_left_project_union_aux
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {qstart qend : Sum Loc₁ Loc₂} {p q : Loc₁}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (unionTaggedTA A B) qstart v w qend vf)
    (hstart : qstart = Sum.inl p) (hend : qend = Sum.inl q) :
    RunFrom A p v w q vf := by
  induction h generalizing p q with
  | nil x v =>
      cases hstart
      cases hend
      exact RunFrom.nil A p v
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      rcases ht with hleft | hright
      · rcases hleft with ⟨tA, htA, htEq⟩
        subst htEq
        have hp : p = tA.source := by
          simpa [mapTransition, hstart] using hsource.symm
        subst hp
        exact RunFrom.cons tA htA rfl
          (by simpa [mapTransition] using hlabel)
          hnonneg
          (by simpa [mapTransition] using hguards)
          (ih rfl hend)
      · rcases hright with ⟨tB, htB, htEq⟩
        subst htEq
        simp [mapTransition, hstart] at hsource

theorem runFrom_right_project_union_aux
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {qstart qend : Sum Loc₁ Loc₂} {p q : Loc₂}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (unionTaggedTA A B) qstart v w qend vf)
    (hstart : qstart = Sum.inr p) (hend : qend = Sum.inr q) :
    RunFrom B p v w q vf := by
  induction h generalizing p q with
  | nil x v =>
      cases hstart
      cases hend
      exact RunFrom.nil B p v
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      rcases ht with hleft | hright
      · rcases hleft with ⟨tA, htA, htEq⟩
        subst htEq
        simp [mapTransition, hstart] at hsource
      · rcases hright with ⟨tB, htB, htEq⟩
        subst htEq
        have hp : p = tB.source := by
          simpa [mapTransition, hstart] using hsource.symm
        subst hp
        exact RunFrom.cons tB htB rfl
          (by simpa [mapTransition] using hlabel)
          hnonneg
          (by simpa [mapTransition] using hguards)
          (ih rfl hend)

theorem runFrom_left_to_right_union_false_aux
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {qstart qend : Sum Loc₁ Loc₂} {p : Loc₁} {q : Loc₂}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (unionTaggedTA A B) qstart v w qend vf)
    (hstart : qstart = Sum.inl p) (hend : qend = Sum.inr q) :
    False := by
  induction h generalizing p q with
  | nil x v =>
      cases hstart
      cases hend
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      rcases ht with hleft | hright
      · rcases hleft with ⟨tA, htA, htEq⟩
        subst htEq
        exact ih rfl hend
      · rcases hright with ⟨tB, htB, htEq⟩
        subst htEq
        simp [mapTransition, hstart] at hsource

theorem runFrom_right_to_left_union_false_aux
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {qstart qend : Sum Loc₁ Loc₂} {p : Loc₂} {q : Loc₁}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (unionTaggedTA A B) qstart v w qend vf)
    (hstart : qstart = Sum.inr p) (hend : qend = Sum.inl q) :
    False := by
  induction h generalizing p q with
  | nil x v =>
      cases hstart
      cases hend
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      rcases ht with hleft | hright
      · rcases hleft with ⟨tA, htA, htEq⟩
        subst htEq
        simp [mapTransition, hstart] at hsource
      · rcases hright with ⟨tB, htB, htEq⟩
        subst htEq
        exact ih rfl hend

theorem unionTagged_lang_subset
    (A : Automaton Loc₁ α) (B : Automaton Loc₂ α) :
    (unionTaggedTA A B).lang ⊆ A.lang ∪ B.lang := by
  intro w h
  rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
  cases q₀ with
  | inl p₀ =>
      have hp₀ : p₀ ∈ A.initial := by
        rcases hq₀ with hleft | hright
        · rcases hleft with ⟨p, hp, hpEq⟩
          cases hpEq
          exact hp
        · rcases hright with ⟨p, hp, hbad⟩
          cases hbad
      cases qf with
      | inl pf =>
          have hpf : pf ∈ A.accepting := by
            rcases hqf with hleft | hright
            · rcases hleft with ⟨p, hp, hpEq⟩
              cases hpEq
              exact hp
            · rcases hright with ⟨p, hp, hbad⟩
              cases hbad
          left
          exact ⟨p₀, hp₀, pf, hpf, vf,
            runFrom_left_project_union_aux hrun rfl rfl⟩
      | inr qfB =>
          exact False.elim (runFrom_left_to_right_union_false_aux hrun rfl rfl)
  | inr q₀B =>
      have hq₀B : q₀B ∈ B.initial := by
        rcases hq₀ with hleft | hright
        · rcases hleft with ⟨p, hp, hbad⟩
          cases hbad
        · rcases hright with ⟨p, hp, hpEq⟩
          cases hpEq
          exact hp
      cases qf with
      | inl pf =>
          exact False.elim (runFrom_right_to_left_union_false_aux hrun rfl rfl)
      | inr qfB =>
          have hqfB : qfB ∈ B.accepting := by
            rcases hqf with hleft | hright
            · rcases hleft with ⟨p, hp, hbad⟩
              cases hbad
            · rcases hright with ⟨p, hp, hpEq⟩
              cases hpEq
              exact hp
          right
          exact ⟨q₀B, hq₀B, qfB, hqfB, vf,
            runFrom_right_project_union_aux hrun rfl rfl⟩

theorem unionTagged_lang_supset
    (A : Automaton Loc₁ α) (B : Automaton Loc₂ α) :
    A.lang ∪ B.lang ⊆ (unionTaggedTA A B).lang := by
  intro w h
  rcases h with hA | hB
  · rcases hA with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
    exact ⟨Sum.inl q₀,
      Or.inl ⟨q₀, hq₀, rfl⟩,
      Sum.inl qf,
      Or.inl ⟨qf, hqf, rfl⟩,
      vf,
      runFrom_left_union hrun⟩
  · rcases hB with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
    exact ⟨Sum.inr q₀,
      Or.inr ⟨q₀, hq₀, rfl⟩,
      Sum.inr qf,
      Or.inr ⟨qf, hqf, rfl⟩,
      vf,
      runFrom_right_union hrun⟩

theorem unionTagged_correct
    (A : Automaton Loc₁ α) (B : Automaton Loc₂ α) :
    (unionTaggedTA A B).lang = A.lang ∪ B.lang :=
  Set.Subset.antisymm (unionTagged_lang_subset A B) (unionTagged_lang_supset A B)

theorem union_correct
    (A : Automaton Loc₁ α) (B : Automaton Loc₂ α) :
    (unionTaggedTA A B).lang = A.lang ∪ B.lang :=
  unionTagged_correct A B

theorem unionTagged_guardsClosed
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    (hA : guardsClosed A) (hB : guardsClosed B) :
    guardsClosed (unionTaggedTA A B) := by
  intro t ht g hg
  rcases ht with hleft | hright
  · rcases hleft with ⟨tA, htA, rfl⟩
    exact Or.inl (hA tA htA g (by simpa [mapTransition] using hg))
  · rcases hright with ⟨tB, htB, rfl⟩
    exact Or.inr (hB tB htB g (by simpa [mapTransition] using hg))

end LeanTre2Ta
