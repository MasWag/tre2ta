import LeanTre2Ta.TimedAutomata.Constructions.TimeRestriction
import LeanTre2Ta.Basic.Language

namespace LeanTre2Ta

def acceptsEmpty (A : Automaton Loc α) : Prop :=
  [] ∈ A.lang

def concatRightClock (x : Clock) : Clock := 2 * x + 1

def concatRenameGuard (g : Guard) : Guard :=
  { clock := concatRightClock g.clock
    interval := g.interval }

def concatRenameResets (rs : Set Clock) : Set Clock :=
  concatRightClock '' rs

def concatRightVal (v : Valuation) : Valuation :=
  fun x => v (concatRightClock x)

def concatRightResetSet : Set Clock :=
  concatRenameResets Set.univ

/- A concatenation construction with tagged locations and a separated right
   clock namespace.  The switching transition consumes the event that completes
   the left component and resets the right-clock namespace before entering an
   initial right state, matching the Rust construction's handoff discipline. -/
def switchTransition (t : Transition Loc₁ α) (q : Loc₂) :
    Transition (Sum Loc₁ Loc₂) α :=
  { source := Sum.inl t.source
    label := t.label
    guards := t.guards
    resets := t.resets ∪ concatRightResetSet
    target := Sum.inr q }

def concatRightTransition (t : Transition Loc₂ α) :
    Transition (Sum Loc₁ Loc₂) α :=
  { source := Sum.inr t.source
    label := t.label
    guards := t.guards.map concatRenameGuard
    resets := concatRenameResets t.resets
    target := Sum.inr t.target }

def concatTA (A : Automaton Loc₁ α) (B : Automaton Loc₂ α) :
    Automaton (Sum Loc₁ Loc₂) α :=
  { locations :=
      {q | ∃ p ∈ A.locations, q = Sum.inl p} ∪
      {q | ∃ p ∈ B.locations, q = Sum.inr p}
    initial :=
      {q | ∃ p ∈ A.initial, q = Sum.inl p} ∪
      {q | acceptsEmpty A ∧ ∃ p ∈ B.initial, q = Sum.inr p}
    accepting :=
      {q | ∃ p ∈ B.accepting, q = Sum.inr p} ∪
      {q | acceptsEmpty B ∧ ∃ p ∈ A.accepting, q = Sum.inl p}
    clocks := A.clocks ∪ concatRenameResets B.clocks
    transitions :=
      (mapTransition Sum.inl '' A.transitions) ∪
      ((concatRightTransition (Loc₁ := Loc₁) '' B.transitions) ∪
        {u | ∃ t ∈ A.transitions, t.target ∈ A.accepting ∧
          ∃ q₀ ∈ B.initial, u = switchTransition t q₀}) }

theorem concatRightClock_injective : Function.Injective concatRightClock := by
  intro x y h
  have hmul : 2 * x = 2 * y := Nat.succ.inj h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hmul

theorem concatRightClock_mem_resets {rs : Set Clock} {x : Clock} :
    concatRightClock x ∈ concatRenameResets rs ↔ x ∈ rs := by
  constructor
  · intro h
    rcases h with ⟨y, hy, hxy⟩
    have hyx : y = x := concatRightClock_injective hxy
    cases hyx
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem concatRightVal_zero :
    concatRightVal zeroVal = zeroVal := by
  ext x
  rfl

theorem concatRightVal_delay (d : ℝ) (v : Valuation) :
    concatRightVal (delayVal d v) = delayVal d (concatRightVal v) := by
  ext x
  rfl

theorem concatRightVal_reset_right (rs : Set Clock) (v : Valuation) :
    concatRightVal (resetVal (concatRenameResets rs) v) =
      resetVal rs (concatRightVal v) := by
  ext x
  by_cases hx : x ∈ rs
  · have hmem : concatRightClock x ∈ concatRenameResets rs :=
      (concatRightClock_mem_resets).2 hx
    simp [concatRightVal, resetVal, hx, hmem]
  · have hnot : concatRightClock x ∉ concatRenameResets rs := by
      intro hmem
      exact hx ((concatRightClock_mem_resets).1 hmem)
    simp [concatRightVal, resetVal, hx, hnot]

theorem concatRightVal_reset_switch (rs : Set Clock) (v : Valuation) :
    concatRightVal (resetVal (rs ∪ concatRightResetSet) v) = zeroVal := by
  ext x
  have hmem : concatRightClock x ∈ rs ∪ concatRightResetSet := by
    right
    exact ⟨x, by simp, rfl⟩
  simp [concatRightVal, resetVal, zeroVal, hmem]

theorem guardsSat_concatRename_right {v : Valuation} {gs : List Guard} :
    guardsSat v (gs.map concatRenameGuard) ↔ guardsSat (concatRightVal v) gs := by
  constructor
  · intro h g hg
    have hmem : concatRenameGuard g ∈ gs.map concatRenameGuard :=
      List.mem_map.mpr ⟨g, hg, rfl⟩
    have hs := h (concatRenameGuard g) hmem
    simpa [Guard.sat, concatRenameGuard, concatRightVal] using hs
  · intro h g hg
    rcases List.mem_map.mp hg with ⟨g₀, hg₀, rfl⟩
    have hs := h g₀ hg₀
    simpa [Guard.sat, concatRenameGuard, concatRightVal] using hs

theorem runFrom_nil_inv
    {A : Automaton Loc α} {q qf : Loc} {v vf : Valuation}
    (h : RunFrom A q v [] qf vf) :
    qf = q ∧ vf = v := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩

theorem acceptsEmpty_iff_nil_lang {A : Automaton Loc α} :
    acceptsEmpty A ↔ ∃ q ∈ A.initial, q ∈ A.accepting := by
  constructor
  · intro h
    rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
    have hnil := runFrom_nil_inv hrun
    rcases hnil with ⟨hqf, hvf⟩
    subst qf
    subst vf
    exact ⟨q₀, hq₀, hqf⟩
  · intro h
    rcases h with ⟨q, hq₀, hqf⟩
    exact ⟨q, hq₀, q, hqf, zeroVal, RunFrom.nil A q zeroVal⟩

theorem runFrom_append
    {A : Automaton Loc α} {p q r : Loc} {v vm vf : Valuation}
    {w₁ w₂ : TimedWord α}
    (h₁ : RunFrom A p v w₁ q vm)
    (h₂ : RunFrom A q vm w₂ r vf) :
    RunFrom A p v (w₁ ++ w₂) r vf := by
  induction h₁ generalizing r vf w₂ with
  | nil q v =>
      simpa using h₂
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      exact RunFrom.cons t ht hsource hlabel hnonneg hguards (ih h₂)

theorem runFrom_left_lift_concat
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {p q : Loc₁} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom A p v w q vf) :
    RunFrom (concatTA A B) (Sum.inl p) v w (Sum.inl q) vf := by
  induction h with
  | nil q v =>
      exact RunFrom.nil (concatTA A B) (Sum.inl q) v
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

theorem runFrom_right_lift_concat
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {p q : Loc₂} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom B p v w q vf) {V : Valuation}
    (hV : concatRightVal V = v) :
    ∃ VF, concatRightVal VF = vf ∧
      RunFrom (concatTA A B) (Sum.inr p) V w (Sum.inr q) VF := by
  induction h generalizing V with
  | nil q v =>
      exact ⟨V, hV, RunFrom.nil (concatTA A B) (Sum.inr q) V⟩
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i p0 q0 v0 vf0 d a wTail
      let VNext := resetVal (concatRenameResets t.resets) (delayVal d V)
      have hVNext :
          concatRightVal VNext =
            resetVal t.resets (delayVal d v0) := by
        dsimp [VNext]
        rw [concatRightVal_reset_right, concatRightVal_delay, hV]
      rcases ih hVNext with ⟨VF, hVF, htailLift⟩
      refine ⟨VF, hVF, ?_⟩
      exact RunFrom.cons (concatRightTransition (Loc₁ := Loc₁) t)
        (by
          right
          left
          exact ⟨t, ht, rfl⟩)
        (by simp [concatRightTransition, hsource])
        (by simp [concatRightTransition, hlabel])
        hnonneg
        (by
          apply guardsSat_concatRename_right.mpr
          have hv : concatRightVal (delayVal d V) = delayVal d v0 := by
            rw [concatRightVal_delay, hV]
          simpa [hv] using hguards)
        (by
          dsimp [VNext] at htailLift
          simpa [concatRightTransition] using htailLift)

theorem runFrom_right_project_aux
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {qstart qend : Sum Loc₁ Loc₂} {p q : Loc₂}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (concatTA A B) qstart v w qend vf)
    (hstart : qstart = Sum.inr p) (hend : qend = Sum.inr q) :
    RunFrom B p (concatRightVal v) w q (concatRightVal vf) := by
  induction h generalizing p q with
  | nil x v =>
      cases hstart
      cases hend
      exact RunFrom.nil B p (concatRightVal v)
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      cases ht with
      | inl hleft =>
          rcases hleft with ⟨tA, htA, htEq⟩
          subst htEq
          simp [mapTransition, hstart] at hsource
      | inr hrest =>
          cases hrest with
          | inl hright =>
              rcases hright with ⟨tB, htB, htEq⟩
              subst htEq
              have hp : p = tB.source := by
                simpa [concatRightTransition, hstart] using hsource.symm
              subst hp
              exact RunFrom.cons tB htB rfl
                (by simpa [concatRightTransition] using hlabel)
                hnonneg
                (by
                  have hg := guardsSat_concatRename_right.mp
                    (by simpa [concatRightTransition] using hguards)
                  simpa [concatRightVal_delay] using hg)
                (by
                  have htailProj := ih rfl hend
                  simpa [concatRightTransition, concatRightVal_delay,
                    concatRightVal_reset_right] using htailProj)
          | inr hswitch =>
              rcases hswitch with ⟨tA, htA, htacc, q₀, hq₀, htEq⟩
              subst htEq
              simp [switchTransition, hstart] at hsource

theorem runFrom_right_project
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {p q : Loc₂} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (concatTA A B) (Sum.inr p) v w (Sum.inr q) vf) :
    RunFrom B p (concatRightVal v) w q (concatRightVal vf) :=
  runFrom_right_project_aux h rfl rfl

theorem runFrom_right_to_left_false_aux
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {qstart qend : Sum Loc₁ Loc₂} {p : Loc₂} {q : Loc₁}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (concatTA A B) qstart v w qend vf)
    (hstart : qstart = Sum.inr p) (hend : qend = Sum.inl q) :
    False := by
  induction h generalizing p q with
  | nil x v =>
      cases hstart
      cases hend
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      cases ht with
      | inl hleft =>
          rcases hleft with ⟨tA, htA, htEq⟩
          subst htEq
          simp [mapTransition, hstart] at hsource
      | inr hrest =>
          cases hrest with
          | inl hright =>
              rcases hright with ⟨tB, htB, htEq⟩
              subst htEq
              exact ih rfl hend
          | inr hswitch =>
              rcases hswitch with ⟨tA, htA, htacc, q₀, hq₀, htEq⟩
              subst htEq
              simp [switchTransition, hstart] at hsource

theorem runFrom_right_to_left_false
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {p : Loc₂} {q : Loc₁} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (concatTA A B) (Sum.inr p) v w (Sum.inl q) vf) :
    False :=
  runFrom_right_to_left_false_aux h rfl rfl

theorem runFrom_left_project_aux
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {qstart qend : Sum Loc₁ Loc₂} {p q : Loc₁}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (concatTA A B) qstart v w qend vf)
    (hstart : qstart = Sum.inl p) (hend : qend = Sum.inl q) :
    RunFrom A p v w q vf := by
  induction h generalizing p q with
  | nil x v =>
      cases hstart
      cases hend
      exact RunFrom.nil A p v
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      cases ht with
      | inl hleft =>
          rcases hleft with ⟨tA, htA, htEq⟩
          subst htEq
          have hp : p = tA.source := by
            simpa [mapTransition, hstart] using hsource.symm
          subst hp
          exact RunFrom.cons tA htA rfl
            (by simpa [mapTransition] using hlabel)
            hnonneg
            (by simpa [mapTransition] using hguards)
            (ih rfl hend)
      | inr hrest =>
          cases hrest with
          | inl hright =>
              rcases hright with ⟨tB, htB, htEq⟩
              subst htEq
              simp [concatRightTransition, hstart] at hsource
          | inr hswitch =>
              rcases hswitch with ⟨tA, htA, htacc, q₀, hq₀, htEq⟩
              subst htEq
              have htailFalse :
                  False :=
                runFrom_right_to_left_false_aux htail rfl hend
              exact False.elim htailFalse

theorem runFrom_left_project
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {p q : Loc₁} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (concatTA A B) (Sum.inl p) v w (Sum.inl q) vf) :
    RunFrom A p v w q vf :=
  runFrom_left_project_aux h rfl rfl

theorem runFrom_left_to_right_decomp_aux
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {qstart qend : Sum Loc₁ Loc₂} {p : Loc₁} {q : Loc₂}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (concatTA A B) qstart v w qend vf)
    (hstart : qstart = Sum.inl p) (hend : qend = Sum.inr q) :
    ∃ u, ∃ qA ∈ A.accepting, ∃ vfA,
      ∃ qB₀ ∈ B.initial, ∃ vword,
        RunFrom A p v u qA vfA ∧
        RunFrom B qB₀ zeroVal vword q (concatRightVal vf) ∧
        w = u ++ vword := by
  induction h generalizing p q with
  | nil x v =>
      cases hstart
      cases hend
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      cases ht with
      | inl hleft =>
          rcases hleft with ⟨tA, htA, htEq⟩
          subst htEq
          have hp : p = tA.source := by
            simpa [mapTransition, hstart] using hsource.symm
          subst hp
          rcases ih rfl hend with
            ⟨u, qA, hqA, vfA, qB₀, hqB₀, vword, hrunA, hrunB, hw⟩
          refine ⟨(d, a) :: u, qA, hqA, vfA, qB₀, hqB₀, vword, ?_, hrunB, ?_⟩
          · exact RunFrom.cons tA htA rfl
              (by simpa [mapTransition] using hlabel)
              hnonneg
              (by simpa [mapTransition] using hguards)
              hrunA
          · simp [hw]
      | inr hrest =>
          cases hrest with
          | inl hright =>
              rcases hright with ⟨tB, htB, htEq⟩
              subst htEq
              simp [concatRightTransition, hstart] at hsource
          | inr hswitch =>
              rcases hswitch with ⟨tA, htA, htacc, qB₀, hqB₀, htEq⟩
              subst htEq
              have hp : p = tA.source := by
                simpa [switchTransition, hstart] using hsource.symm
              subst hp
              have htailB :
                  RunFrom B qB₀ zeroVal wTail q (concatRightVal vf0) := by
                have hproj := runFrom_right_project_aux htail rfl hend
                have hzero :
                    concatRightVal
                      (resetVal (switchTransition tA qB₀).resets (delayVal d v0)) =
                      zeroVal := by
                  simpa [switchTransition] using
                    concatRightVal_reset_switch tA.resets (delayVal d v0)
                simpa [hzero] using hproj
              refine ⟨[(d, a)], tA.target, htacc,
                resetVal tA.resets (delayVal d v0),
                qB₀, hqB₀, wTail, ?_, htailB, ?_⟩
              · exact RunFrom.cons tA htA rfl
                  (by simpa [switchTransition] using hlabel)
                  hnonneg
                  (by simpa [switchTransition] using hguards)
                  (RunFrom.nil A tA.target
                    (resetVal tA.resets (delayVal d v0)))
              · simp

theorem runFrom_left_to_right_decomp
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {p : Loc₁} {q : Loc₂} {vf : Valuation} {w : TimedWord α}
    (hinit : p ∈ A.initial) (hacc : q ∈ B.accepting)
    (h : RunFrom (concatTA A B) (Sum.inl p) zeroVal w (Sum.inr q) vf) :
    ∃ u ∈ A.lang, ∃ vword ∈ B.lang, w = u ++ vword := by
  rcases runFrom_left_to_right_decomp_aux h rfl rfl with
    ⟨u, qA, hqA, vfA, qB₀, hqB₀, vword, hrunA, hrunB, hw⟩
  exact ⟨u, ⟨p, hinit, qA, hqA, vfA, hrunA⟩,
    vword, ⟨qB₀, hqB₀, q, hacc, concatRightVal vf, hrunB⟩, hw⟩

theorem runFrom_A_switch_concat_of_nonempty
    {A : Automaton Loc₁ α} {B : Automaton Loc₂ α}
    {p q : Loc₁} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom A p v w q vf)
    (hnonempty : w ≠ [])
    (hacc : q ∈ A.accepting)
    (qB : Loc₂) (hqB : qB ∈ B.initial) :
    ∃ V, concatRightVal V = zeroVal ∧
      RunFrom (concatTA A B) (Sum.inl p) v w (Sum.inr qB) V := by
  induction h generalizing qB with
  | nil q v =>
      exact False.elim (hnonempty rfl)
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i p0 q0 v0 vf0 d a wTail
      by_cases htail_empty : wTail = []
      · subst htail_empty
        have htail_inv := runFrom_nil_inv htail
        rcases htail_inv with ⟨hq, hv⟩
        subst q0
        subst vf0
        have htacc : t.target ∈ A.accepting := hacc
        let V :=
          resetVal (switchTransition t qB).resets (delayVal d v0)
        refine ⟨V, ?_, ?_⟩
        · dsimp [V]
          simpa [switchTransition] using
            concatRightVal_reset_switch t.resets (delayVal d v0)
        · exact
            RunFrom.cons (switchTransition t qB)
              (by
                right
                right
                exact ⟨t, ht, htacc, qB, hqB, rfl⟩)
              (by simp [switchTransition, hsource])
              (by simp [switchTransition, hlabel])
              hnonneg
              (by simpa [switchTransition] using hguards)
              (by
                show RunFrom (concatTA A B)
                  (switchTransition t qB).target
                  (resetVal (switchTransition t qB).resets (delayVal d v0))
                  [] (Sum.inr qB)
                    (resetVal (switchTransition t qB).resets (delayVal d v0))
                simpa [switchTransition] using
                  (RunFrom.nil (concatTA A B)
                    (switchTransition t qB).target
                    (resetVal (switchTransition t qB).resets (delayVal d v0))))
      · rcases ih htail_empty hacc qB hqB with ⟨V, hV, hrun⟩
        refine ⟨V, hV, ?_⟩
        exact RunFrom.cons (mapTransition Sum.inl t)
          (by
            left
            exact ⟨t, ht, rfl⟩)
          (by simp [mapTransition, hsource])
          (by simp [mapTransition, hlabel])
          hnonneg
          (by simpa [mapTransition] using hguards)
          hrun

theorem concat_complete
    (A : Automaton Loc₁ α) (B : Automaton Loc₂ α) :
    concatLang A.lang B.lang ⊆ (concatTA A B).lang := by
  intro w h
  rcases h with ⟨u, hu, vword, hv, rfl⟩
  rcases hu with ⟨p₀, hp₀, pf, hpf, vfA, hrunA⟩
  rcases hv with ⟨q₀, hq₀, qf, hqf, vfB, hrunB⟩
  by_cases hu_empty : u = []
  · subst u
    have hAempty : acceptsEmpty A :=
      ⟨p₀, hp₀, pf, hpf, vfA, hrunA⟩
    rcases runFrom_right_lift_concat (A := A) hrunB
        (V := zeroVal) concatRightVal_zero with
      ⟨VF, hVF, hrunLift⟩
    refine ⟨Sum.inr q₀, ?_, Sum.inr qf, ?_, VF, ?_⟩
    · right
      exact ⟨hAempty, q₀, hq₀, rfl⟩
    · left
      exact ⟨qf, hqf, rfl⟩
    · exact hrunLift
  · by_cases hv_empty : vword = []
    · subst vword
      have hBempty : acceptsEmpty B :=
        ⟨q₀, hq₀, qf, hqf, vfB, hrunB⟩
      refine ⟨Sum.inl p₀, ?_, Sum.inl pf, ?_, vfA, ?_⟩
      · left
        exact ⟨p₀, hp₀, rfl⟩
      · right
        exact ⟨hBempty, pf, hpf, rfl⟩
      · simpa using runFrom_left_lift_concat (B := B) hrunA
    · have hswitch :=
        runFrom_A_switch_concat_of_nonempty (A := A) (B := B)
          hrunA hu_empty hpf q₀ hq₀
      rcases hswitch with ⟨Vswitch, hVswitch, hrunSwitch⟩
      rcases runFrom_right_lift_concat (A := A) hrunB
          (V := Vswitch) hVswitch with
        ⟨VF, hVF, hrunRight⟩
      refine ⟨Sum.inl p₀, ?_, Sum.inr qf, ?_, VF, ?_⟩
      · left
        exact ⟨p₀, hp₀, rfl⟩
      · left
        exact ⟨qf, hqf, rfl⟩
      · exact runFrom_append hrunSwitch hrunRight

theorem concat_sound
    (A : Automaton Loc₁ α) (B : Automaton Loc₂ α) :
    (concatTA A B).lang ⊆ concatLang A.lang B.lang := by
  intro w h
  rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
  cases q₀ with
  | inl p₀ =>
      have hp₀ : p₀ ∈ A.initial := by
        rcases hq₀ with hleft | hright
        · rcases hleft with ⟨p, hp, hpEq⟩
          cases hpEq
          exact hp
        · rcases hright with ⟨hAempty, p, hp, hbad⟩
          cases hbad
      cases qf with
      | inl pf =>
          have hBempty : acceptsEmpty B := by
            rcases hqf with hright | hleftAcc
            · rcases hright with ⟨q, hq, hbad⟩
              cases hbad
            · exact hleftAcc.1
          have hpf : pf ∈ A.accepting := by
            rcases hqf with hright | hleftAcc
            · rcases hright with ⟨q, hq, hbad⟩
              cases hbad
            · rcases hleftAcc with ⟨_, p, hp, hpEq⟩
              cases hpEq
              exact hp
          have hrunA := runFrom_left_project hrun
          exact ⟨w, ⟨p₀, hp₀, pf, hpf, vf, hrunA⟩,
            [], hBempty, by simp⟩
      | inr qfB =>
          have hqfB : qfB ∈ B.accepting := by
            rcases hqf with hright | hleftAcc
            · rcases hright with ⟨q, hq, hqEq⟩
              cases hqEq
              exact hq
            · rcases hleftAcc with ⟨_, p, hp, hbad⟩
              cases hbad
          exact runFrom_left_to_right_decomp hp₀ hqfB hrun
  | inr q₀B =>
      have hAempty : acceptsEmpty A := by
        rcases hq₀ with hleft | hright
        · rcases hleft with ⟨p, hp, hbad⟩
          cases hbad
        · exact hright.1
      have hq₀B : q₀B ∈ B.initial := by
        rcases hq₀ with hleft | hright
        · rcases hleft with ⟨p, hp, hbad⟩
          cases hbad
        · rcases hright with ⟨_, q, hq, hqEq⟩
          cases hqEq
          exact hq
      cases qf with
      | inl pf =>
          exact False.elim (runFrom_right_to_left_false hrun)
      | inr qfB =>
          have hqfB : qfB ∈ B.accepting := by
            rcases hqf with hright | hleftAcc
            · rcases hright with ⟨q, hq, hqEq⟩
              cases hqEq
              exact hq
            · rcases hleftAcc with ⟨_, p, hp, hbad⟩
              cases hbad
          have hrunB := runFrom_right_project hrun
          exact ⟨[], hAempty, w,
            ⟨q₀B, hq₀B, qfB, hqfB, concatRightVal vf,
              by simpa [concatRightVal_zero] using hrunB⟩,
            by simp⟩

theorem concat_correct
    (A : Automaton Loc₁ α) (B : Automaton Loc₂ α) :
    (concatTA A B).lang = concatLang A.lang B.lang :=
  Set.Subset.antisymm (concat_sound A B) (concat_complete A B)

theorem concatLang_assoc (L₁ L₂ L₃ : Set (TimedWord α)) :
    concatLang (concatLang L₁ L₂) L₃ =
      concatLang L₁ (concatLang L₂ L₃) := by
  ext w
  constructor
  · intro h
    rcases h with ⟨w12, hw12, w3, hw3, rfl⟩
    rcases hw12 with ⟨w1, hw1, w2, hw2, rfl⟩
    exact ⟨w1, hw1, w2 ++ w3, ⟨w2, hw2, w3, hw3, rfl⟩, by simp [List.append_assoc]⟩
  · intro h
    rcases h with ⟨w1, hw1, w23, hw23, rfl⟩
    rcases hw23 with ⟨w2, hw2, w3, hw3, rfl⟩
    exact ⟨w1 ++ w2, ⟨w1, hw1, w2, hw2, rfl⟩, w3, hw3, by simp [List.append_assoc]⟩

end LeanTre2Ta
