import LeanTre2Ta.TA.Trim

namespace LeanTre2Ta

def freshClock (x : Clock) (A : Automaton Loc Label) : Prop :=
  x ∉ A.clocks

noncomputable def freshClockFor (A : Automaton Loc Label)
    (h : ∃ x : Clock, freshClock x A) : Clock :=
  Classical.choose h

theorem freshClockFor_fresh (A : Automaton Loc Label)
    (h : ∃ x : Clock, freshClock x A) :
    freshClock (freshClockFor A h) A :=
  Classical.choose_spec h

def addClock (x : Clock) (A : Automaton Loc Label) : Automaton Loc Label :=
  { A with clocks := {c | c ∈ A.clocks ∨ c = x} }

def durationClock : Clock := 0

def shiftClock (x : Clock) : Clock := x + 1

def shiftGuard (g : Guard) : Guard :=
  { clock := shiftClock g.clock
    interval := g.interval }

def shiftResets (rs : Set Clock) : Set Clock :=
  {x | 0 < x ∧ x - 1 ∈ rs}

def unshiftVal (v : Valuation) : Valuation :=
  fun x => v (shiftClock x)

def embedVal (elapsed : ℝ) (v : Valuation) : Valuation
  | 0 => elapsed
  | x + 1 => v x

def timeGuard (I : Interval) : Guard :=
  { clock := durationClock
    interval := I }

def shiftTransition (t : Transition Loc α) : Transition (Option Loc) α :=
  { source := some t.source
    label := t.label
    guards := t.guards.map shiftGuard
    resets := shiftResets t.resets
    target := some t.target }

def acceptingTransition (I : Interval) (t : Transition Loc α) :
    Transition (Option Loc) α :=
  { source := some t.source
    label := t.label
    guards := t.guards.map shiftGuard ++ [timeGuard I]
    resets := shiftResets t.resets
    target := none }

def timeRestrictAcceptsEmpty (A : Automaton Loc α) : Prop :=
  [] ∈ A.lang

def timeRestrictTA (A : Automaton Loc α) (I : Interval) :
    Automaton (Option Loc) α :=
  { locations := {q | ∃ p ∈ A.locations, q = some p} ∪ {none}
    initial :=
      {q | ∃ p ∈ A.initial, q = some p} ∪
      {q | timeRestrictAcceptsEmpty A ∧ Interval.mem 0 I ∧ q = none}
    accepting := {none}
    clocks := {durationClock} ∪ (shiftClock '' A.clocks)
    transitions :=
      (shiftTransition '' A.transitions) ∪
      {u | ∃ t ∈ A.transitions, t.target ∈ A.accepting ∧
        u = acceptingTransition I t} }

theorem unshiftVal_zero :
    unshiftVal zeroVal = zeroVal := by
  ext x
  rfl

theorem unshiftVal_delay (d : ℝ) (v : Valuation) :
    unshiftVal (delayVal d v) = delayVal d (unshiftVal v) := by
  ext x
  rfl

@[simp] theorem shiftResets_succ_mem (rs : Set Clock) (x : Clock) :
    shiftClock x ∈ shiftResets rs ↔ x ∈ rs := by
  simp [shiftClock, shiftResets]

@[simp] theorem zero_not_mem_shiftResets (rs : Set Clock) :
    durationClock ∉ shiftResets rs := by
  simp [durationClock, shiftResets]

theorem unshiftVal_reset_shift (rs : Set Clock) (v : Valuation) :
    unshiftVal (resetVal (shiftResets rs) v) =
      resetVal rs (unshiftVal v) := by
  ext x
  by_cases hx : x ∈ rs
  · simp [unshiftVal, resetVal, hx]
  · simp [unshiftVal, resetVal, hx]

theorem embedVal_zero :
    embedVal 0 zeroVal = zeroVal := by
  ext x
  cases x <;> rfl

theorem embedVal_delay (elapsed d : ℝ) (v : Valuation) :
    delayVal d (embedVal elapsed v) =
      embedVal (elapsed + d) (delayVal d v) := by
  ext x
  cases x with
  | zero => simp [delayVal, embedVal]
  | succ x => simp [delayVal, embedVal]

theorem embedVal_reset_shift (elapsed : ℝ) (rs : Set Clock) (v : Valuation) :
    resetVal (shiftResets rs) (embedVal elapsed v) =
      embedVal elapsed (resetVal rs v) := by
  ext x
  cases x with
  | zero =>
      have hzero : (0 : Clock) ∉ shiftResets rs := zero_not_mem_shiftResets rs
      simp [resetVal, embedVal, hzero]
  | succ x =>
      by_cases hx : x ∈ rs
      · simp [resetVal, embedVal, shiftResets, hx]
      · simp [resetVal, embedVal, shiftResets, hx]

theorem embedVal_step (elapsed d : ℝ) (rs : Set Clock) (v : Valuation) :
    resetVal (shiftResets rs) (delayVal d (embedVal elapsed v)) =
      embedVal (elapsed + d) (resetVal rs (delayVal d v)) := by
  rw [embedVal_delay, embedVal_reset_shift]

theorem guardsSat_shift_of_map
    {gs : List Guard} {v : Valuation} {d : ℝ}
    (h : guardsSat (delayVal d v) (gs.map shiftGuard)) :
    guardsSat (delayVal d (unshiftVal v)) gs := by
  intro g hg
  have hsg : shiftGuard g ∈ gs.map shiftGuard := by
    exact List.mem_map.mpr ⟨g, hg, rfl⟩
  have hs := h (shiftGuard g) hsg
  simpa [Guard.sat, shiftGuard, unshiftVal, shiftClock, delayVal] using hs

theorem guardsSat_map_of_shift
    {gs : List Guard} {v : Valuation} {d : ℝ}
    (h : guardsSat (delayVal d (unshiftVal v)) gs) :
    guardsSat (delayVal d v) (gs.map shiftGuard) := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨g₀, hg₀, rfl⟩
  have hs := h g₀ hg₀
  simpa [Guard.sat, shiftGuard, unshiftVal, shiftClock, delayVal] using hs

theorem timeGuard_sat_iff {I : Interval} {v : Valuation} {d : ℝ} :
    Guard.sat (delayVal d v) (timeGuard I) ↔
      Interval.mem (v durationClock + d) I := by
  rfl

theorem guardsSat_accepting_of_parts
    {I : Interval} {gs : List Guard} {v : Valuation} {d : ℝ}
    (hgs : guardsSat (delayVal d (unshiftVal v)) gs)
    (hI : Interval.mem (v durationClock + d) I) :
    guardsSat (delayVal d v) (gs.map shiftGuard ++ [timeGuard I]) := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact guardsSat_map_of_shift hgs g hg
  · simp at hg
    subst hg
    exact hI

theorem fresh_clock_tracks_duration
    {A : Automaton Loc α} {x : Clock}
    (hnoreset : ∀ t ∈ A.transitions, x ∉ t.resets)
    {q qf : Loc} {v vf : Valuation} {w : TimedWord α} {c : ℝ}
    (hrun : RunFrom A q v w qf vf)
    (hvx : v x = c) :
    vf x = c + TimedWord.duration w := by
  induction hrun generalizing c with
  | nil q v =>
      simp [TimedWord.duration, hvx]
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i p0 q0 v0 vf0 d a wTail
      have hnot := hnoreset t ht
      have hnext :
          resetVal t.resets (delayVal d v0) x = c + d := by
        rw [resetVal_not_mem hnot]
        simp [delayVal, hvx]
      have htailx := ih hnext
      calc
        vf0 x = (c + d) + TimedWord.duration wTail := htailx
        _ = c + TimedWord.duration ((d, a) :: wTail) := by
          simp [TimedWord.duration]
          rw [add_assoc]

theorem fresh_clock_tracks_duration_from_zero
    {A : Automaton Loc α} {x : Clock}
    (hnoreset : ∀ t ∈ A.transitions, x ∉ t.resets)
    {q qf : Loc} {vf : Valuation} {w : TimedWord α}
    (hrun : RunFrom A q zeroVal w qf vf) :
    vf x = TimedWord.duration w := by
  have h := fresh_clock_tracks_duration (A := A) (x := x) hnoreset hrun (c := 0) rfl
  simpa using h

theorem timeRestrict_no_reset_duration
    (A : Automaton Loc α) (I : Interval) :
    ∀ t ∈ (timeRestrictTA A I).transitions, durationClock ∉ t.resets := by
  intro t ht
  rcases ht with hshift | hacc
  · rcases hshift with ⟨tA, htA, rfl⟩
    simp [shiftTransition]
  · rcases hacc with ⟨tA, htA, htacc, rfl⟩
    simp [acceptingTransition]

theorem runFrom_nil_inv_timeRestrict
    {A : Automaton Loc α} {q qf : Loc} {v vf : Valuation}
    (h : RunFrom A q v [] qf vf) :
    qf = q ∧ vf = v := by
  cases h with
  | nil => exact ⟨rfl, rfl⟩

theorem runFrom_timeRestrict_from_none_inv
    {A : Automaton Loc α} {I : Interval}
    {qf : Option Loc} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (timeRestrictTA A I) none v w qf vf) :
    w = [] ∧ qf = none ∧ vf = v := by
  cases h with
  | nil =>
      simp
  | cons t ht hsource _ _ _ _ =>
      rcases ht with hshift | hacc
      · rcases hshift with ⟨tA, htA, htEq⟩
        subst htEq
        simp [shiftTransition] at hsource
      · rcases hacc with ⟨tA, htA, htacc, htEq⟩
        subst htEq
        simp [acceptingTransition] at hsource

theorem runFrom_timeRestrict_none_to_some_false
    {A : Automaton Loc α} {I : Interval}
    {qend : Option Loc} {q : Loc}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (timeRestrictTA A I) none v w qend vf)
    (hend : qend = some q) :
    False := by
  have hinv := runFrom_timeRestrict_from_none_inv h
  have hnone : qend = none := hinv.2.1
  rw [hend] at hnone
  cases hnone

theorem runFrom_timeRestrict_to_some_project
    {A : Automaton Loc α} {I : Interval}
    {qstart qend : Option Loc} {p q : Loc}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (timeRestrictTA A I) qstart v w qend vf)
    (hstart : qstart = some p) (hend : qend = some q) :
    RunFrom A p (unshiftVal v) w q (unshiftVal vf) := by
  induction h generalizing p q with
  | nil x v =>
      cases hstart
      cases hend
      exact RunFrom.nil A p (unshiftVal v)
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      rcases ht with hshift | hacc
      · rcases hshift with ⟨tA, htA, htEq⟩
        subst htEq
        have hp : p = tA.source := by
          simpa [shiftTransition, hstart] using hsource.symm
        subst hp
        exact RunFrom.cons tA htA rfl
          (by simpa [shiftTransition] using hlabel)
          hnonneg
          (guardsSat_shift_of_map (by simpa [shiftTransition] using hguards))
          (by
            have htailA := ih rfl hend
            simpa [shiftTransition, unshiftVal_delay, unshiftVal_reset_shift] using htailA)
      · rcases hacc with ⟨tA, htA, htacc, htEq⟩
        subst htEq
        exact False.elim (runFrom_timeRestrict_none_to_some_false htail hend)

theorem runFrom_timeRestrict_to_none_project_aux
    {A : Automaton Loc α} {I : Interval}
    {qstart qend : Option Loc} {p : Loc}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (timeRestrictTA A I) qstart v w qend vf)
    (hstart : qstart = some p) (hend : qend = none) :
    ∃ q ∈ A.accepting,
      RunFrom A p (unshiftVal v) w q (unshiftVal vf) ∧
      Interval.mem (v durationClock + TimedWord.duration w) I := by
  induction h generalizing p with
  | nil x v =>
    cases hstart
    cases hend
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i x y v0 vf0 d a wTail
      rcases ht with hshift | hacc
      · rcases hshift with ⟨tA, htA, htEq⟩
        subst htEq
        have hp : p = tA.source := by
          simpa [shiftTransition, hstart] using hsource.symm
        subst hp
        rcases ih rfl hend with ⟨q, hqacc, hrunA, hI⟩
        exact ⟨q, hqacc,
          RunFrom.cons tA htA rfl
            (by simpa [shiftTransition] using hlabel)
            hnonneg
            (guardsSat_shift_of_map (by simpa [shiftTransition] using hguards))
            (by
              simpa [shiftTransition, unshiftVal_delay, unshiftVal_reset_shift] using hrunA),
          by
            have h0 :
                resetVal (shiftTransition tA).resets (delayVal d v0) durationClock =
                  v0 durationClock + d := by
              simp [shiftTransition, resetVal, shiftResets, durationClock, delayVal]
            have hI' := hI
            rw [h0] at hI'
            simpa [TimedWord.duration, add_assoc] using hI'⟩
      · rcases hacc with ⟨tA, htA, htacc, htEq⟩
        subst htEq
        have hp : p = tA.source := by
          simpa [acceptingTransition, hstart] using hsource.symm
        subst hp
        have htail_nil := runFrom_timeRestrict_from_none_inv htail
        rcases htail_nil with ⟨hwTail, htarget, hvf⟩
        subst hwTail
        subst htarget
        subst hvf
        have hI : Interval.mem (v0 durationClock + d) I := by
          have hg := hguards (timeGuard I)
            (by simp [acceptingTransition])
          simpa [timeGuard, Guard.sat, delayVal, durationClock] using hg
        exact ⟨tA.target, htacc,
          RunFrom.cons tA htA rfl
            (by simpa [acceptingTransition] using hlabel)
            hnonneg
            (guardsSat_shift_of_map
              (by
                intro g hg
                have hmem : g ∈ tA.guards.map shiftGuard ++ [timeGuard I] :=
                  List.mem_append_left [timeGuard I] hg
                exact hguards g (by simpa [acceptingTransition] using hmem)))
            (by
              simpa [acceptingTransition, unshiftVal_delay, unshiftVal_reset_shift] using
                (RunFrom.nil A tA.target
                  (resetVal tA.resets (delayVal d (unshiftVal v0))))),
          by
            simpa [TimedWord.duration] using hI⟩

theorem runFrom_timeRestrict_to_none_project
    {A : Automaton Loc α} {I : Interval}
    {qstart : Option Loc} {p : Loc}
    {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom (timeRestrictTA A I) qstart v w none vf)
    (hstart : qstart = some p) :
    ∃ q ∈ A.accepting,
      RunFrom A p (unshiftVal v) w q (unshiftVal vf) ∧
      Interval.mem (v durationClock + TimedWord.duration w) I :=
  runFrom_timeRestrict_to_none_project_aux h hstart rfl

theorem runFrom_timeRestrict_from_none_nil
    {A : Automaton Loc α} {I : Interval}
    {vf : Valuation} {w : TimedWord α}
    (h : RunFrom (timeRestrictTA A I) none zeroVal w none vf) :
    w = [] := by
  cases h with
  | nil => rfl
  | cons t ht hsource _ _ _ _ =>
      rcases ht with hshift | hacc
      · rcases hshift with ⟨tA, htA, htEq⟩
        subst htEq
        simp [shiftTransition] at hsource
      · rcases hacc with ⟨tA, htA, htacc, htEq⟩
        subst htEq
        simp [acceptingTransition] at hsource

theorem timeRestrict_sound (A : Automaton Loc α) (I : Interval) :
    (timeRestrictTA A I).lang ⊆
      {w | w ∈ A.lang ∧ Interval.mem (TimedWord.duration w) I} := by
  intro w h
  rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
  have hqf_none : qf = none := by simpa [timeRestrictTA] using hqf
  subst qf
  rcases hq₀ with hsome | hnone
  · rcases hsome with ⟨p₀, hp₀, hpEq⟩
    subst hpEq
    rcases runFrom_timeRestrict_to_none_project hrun rfl with
      ⟨q, hqacc, hrunA, hI⟩
    constructor
    · exact ⟨p₀, hp₀, q, hqacc, unshiftVal vf, by
        simpa [unshiftVal_zero] using hrunA⟩
    · simpa [durationClock, zeroVal] using hI
  · rcases hnone with ⟨hAempty, hI0, hqEq⟩
    subst hqEq
    have hw : w = [] := runFrom_timeRestrict_from_none_nil hrun
    subst hw
    exact ⟨hAempty, by simpa [TimedWord.duration] using hI0⟩

theorem runFrom_A_to_timeRestrict_sink_of_nonempty
    {A : Automaton Loc α} {I : Interval}
    {p q : Loc} {v vf : Valuation} {w : TimedWord α}
    {elapsed : ℝ}
    (hrun : RunFrom A p v w q vf)
    (hnonempty : w ≠ [])
    (hacc : q ∈ A.accepting)
    (hI : Interval.mem (elapsed + TimedWord.duration w) I) :
    ∃ vfTR,
      RunFrom (timeRestrictTA A I) (some p) (embedVal elapsed v) w none vfTR := by
  induction hrun generalizing elapsed with
  | nil q v =>
      exact False.elim (hnonempty rfl)
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i p0 q0 v0 vf0 d a wTail
      by_cases htail_empty : wTail = []
      · subst htail_empty
        have htail_inv := runFrom_nil_inv_timeRestrict htail
        rcases htail_inv with ⟨hq, hv⟩
        subst q0
        subst vf0
        refine ⟨resetVal (shiftResets t.resets)
            (delayVal d (embedVal elapsed v0)), ?_⟩
        exact RunFrom.cons (acceptingTransition I t)
          (by
            right
            exact ⟨t, ht, hacc, rfl⟩)
          (by simp [acceptingTransition, hsource])
          (by simp [acceptingTransition, hlabel])
          hnonneg
          (by
            have hI' : Interval.mem (elapsed + d) I := by
              simpa [TimedWord.duration] using hI
            exact guardsSat_accepting_of_parts
              (by simpa [unshiftVal, embedVal] using hguards)
              (by simpa [durationClock, embedVal] using hI'))
          (RunFrom.nil (timeRestrictTA A I) none
            (resetVal (shiftResets t.resets)
              (delayVal d (embedVal elapsed v0))))
      · have hI_tail :
            Interval.mem ((elapsed + d) + TimedWord.duration wTail) I := by
          have hI' : Interval.mem (elapsed + (d + TimedWord.duration wTail)) I := by
            simpa [TimedWord.duration] using hI
          simpa [add_assoc] using hI'
        rcases ih htail_empty hacc hI_tail with ⟨vfTR, htailTR⟩
        refine ⟨vfTR, RunFrom.cons (shiftTransition t) ?_ ?_ ?_ hnonneg ?_ ?_⟩
        · left
          exact ⟨t, ht, rfl⟩
        · simp [shiftTransition, hsource]
        · simp [shiftTransition, hlabel]
        · exact guardsSat_map_of_shift (by simpa [unshiftVal, embedVal] using hguards)
        · simpa [shiftTransition, embedVal_step] using htailTR

theorem timeRestrict_complete (A : Automaton Loc α) (I : Interval) :
    {w | w ∈ A.lang ∧ Interval.mem (TimedWord.duration w) I}
      ⊆ (timeRestrictTA A I).lang := by
  intro w h
  rcases h with ⟨hA, hI⟩
  rcases hA with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
  by_cases hw : w = []
  · subst hw
    have hAempty : timeRestrictAcceptsEmpty A :=
      ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
    exact ⟨none,
      Or.inr ⟨hAempty, by simpa [TimedWord.duration] using hI, rfl⟩,
      none, by simp [timeRestrictTA],
      zeroVal, RunFrom.nil (timeRestrictTA A I) none zeroVal⟩
  · rcases runFrom_A_to_timeRestrict_sink_of_nonempty
      (A := A) (I := I) (elapsed := 0) hrun hw hqf
      (by simpa [TimedWord.duration] using hI) with
      ⟨vfTR, hrunTR⟩
    exact ⟨some q₀,
      Or.inl ⟨q₀, hq₀, rfl⟩,
      none, by simp [timeRestrictTA],
      vfTR,
      by simpa [embedVal_zero] using hrunTR⟩

theorem timeRestrict_correct (A : Automaton Loc α) (I : Interval) :
    (timeRestrictTA A I).lang =
      {w | w ∈ A.lang ∧ Interval.mem (TimedWord.duration w) I} :=
  Set.Subset.antisymm (timeRestrict_sound A I) (timeRestrict_complete A I)

end LeanTre2Ta
