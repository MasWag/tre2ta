import LeanTre2Ta.TA.Concat

namespace LeanTre2Ta

theorem resetVal_union_univ (rs : Set Clock) (v : Valuation) :
    resetVal (rs ∪ Set.univ) v = zeroVal := by
  ext x
  simp [resetVal, zeroVal]

theorem resetVal_univ (v : Valuation) :
    resetVal Set.univ v = zeroVal := by
  ext x
  simp [resetVal, zeroVal]

def restartTransition (t : Transition Loc α) (q₀ : Loc) :
    Transition Loc α :=
  { source := t.source
    label := t.label
    guards := t.guards
    resets := t.resets ∪ Set.univ
    target := q₀ }

/- Rust-like positive closure: keep the original automaton and add a duplicate
   of each transition entering an accepting state, redirected to every initial
   state.  The duplicate consumes the same event and resets the semantic clock
   valuation before the next iteration.  We use `Set.univ` for the reset set
   because Lean valuations are total functions `Clock → ℝ`; resetting only
   `A.clocks` would need a separate clock-closure invariant. -/
def plusTA (A : Automaton Loc α) : Automaton Loc α :=
  { locations := A.locations
    initial := A.initial
    accepting := A.accepting
    clocks := A.clocks
    transitions := A.transitions ∪
      {u | ∃ t ∈ A.transitions, t.target ∈ A.accepting ∧
        ∃ q₀ ∈ A.initial, u = restartTransition t q₀} }

theorem runFrom_lift_plus
    {A : Automaton Loc α} {p q : Loc} {v vf : Valuation}
    {w : TimedWord α}
    (h : RunFrom A p v w q vf) :
    RunFrom (plusTA A) p v w q vf := by
  induction h with
  | nil q v =>
      exact RunFrom.nil (plusTA A) q v
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      exact RunFrom.cons t
        (by left; exact ht)
        hsource hlabel hnonneg hguards ih

theorem run_lift_plus
    {A : Automaton Loc α}
    {q₀ qf : Loc} {vf : Valuation} {w : TimedWord α}
    (hq₀ : q₀ ∈ A.initial)
    (hqf : qf ∈ A.accepting)
    (hrun : RunFrom A q₀ zeroVal w qf vf) :
    w ∈ (plusTA A).lang :=
  ⟨q₀, hq₀, qf, hqf, vf, runFrom_lift_plus hrun⟩

theorem runFrom_A_restart_plus_of_nonempty
    {A : Automaton Loc α}
    {p q : Loc} {v vf : Valuation} {w : TimedWord α}
    (h : RunFrom A p v w q vf)
    (hnonempty : w ≠ [])
    (hacc : q ∈ A.accepting)
    (q₀ : Loc) (hq₀ : q₀ ∈ A.initial) :
    RunFrom (plusTA A) p v w q₀ zeroVal := by
  induction h generalizing q₀ with
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
        exact RunFrom.cons (restartTransition t q₀)
          (by
            right
            exact ⟨t, ht, htacc, q₀, hq₀, rfl⟩)
          (by simp [restartTransition, hsource])
          (by simp [restartTransition, hlabel])
          hnonneg
          (by simpa [restartTransition] using hguards)
          (by
            have hzero :
                resetVal (restartTransition t q₀).resets (delayVal d v0) =
                  zeroVal := by
              simpa [restartTransition] using
                resetVal_union_univ t.resets (delayVal d v0)
            show RunFrom (plusTA A)
              (restartTransition t q₀).target
              (resetVal (restartTransition t q₀).resets (delayVal d v0))
              [] q₀ zeroVal
            simpa [restartTransition, resetVal_univ] using
              (RunFrom.nil (plusTA A) q₀ zeroVal))
      · exact RunFrom.cons t
          (by left; exact ht)
          hsource hlabel hnonneg hguards
          (ih htail_empty hacc q₀ hq₀)

theorem plusLang_cons
    {L : Set (TimedWord α)} {u v : TimedWord α}
    (hu : u ∈ L) (hv : v ∈ plusLang L) :
    u ++ v ∈ plusLang L := by
  rcases hv with ⟨n, hn⟩
  exact ⟨n + 1, u, hu, v, hn, rfl⟩

theorem plus_complete_pow (A : Automaton Loc α) :
    ∀ n, langPow A.lang (n + 1) ⊆ (plusTA A).lang := by
  intro n
  induction n with
  | zero =>
      intro w h
      change w ∈ concatLang A.lang (langPow A.lang 0) at h
      rcases h with ⟨u, hu, v, hv, rfl⟩
      have hvnil : v = [] := by simpa [langPow] using hv
      subst hvnil
      rcases hu with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
      simpa using run_lift_plus hq₀ hqf hrun
  | succ n ih =>
      intro w h
      change w ∈ concatLang A.lang (langPow A.lang (n + 1)) at h
      rcases h with ⟨u, hu, vword, hvword, rfl⟩
      by_cases hu_empty : u = []
      · subst u
        simpa using ih hvword
      · rcases hu with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
        rcases ih hvword with ⟨p₀, hp₀, pf, hpf, vfPlus, hrunPlus⟩
        exact ⟨q₀, hq₀, pf, hpf, vfPlus,
          runFrom_append
            (runFrom_A_restart_plus_of_nonempty hrun hu_empty hqf p₀ hp₀)
            hrunPlus⟩

theorem plus_complete (A : Automaton Loc α) :
    plusLang A.lang ⊆ (plusTA A).lang := by
  intro w h
  rcases h with ⟨n, hn⟩
  exact plus_complete_pow A n hn

theorem plus_sound_aux
    {A : Automaton Loc α}
    {p₀ p qf : Loc} {v vf : Valuation}
    {pref suffix : TimedWord α}
    (hp₀ : p₀ ∈ A.initial)
    (hprefix : RunFrom A p₀ zeroVal pref p v)
    (hrun : RunFrom (plusTA A) p v suffix qf vf)
    (hqf : qf ∈ A.accepting) :
    pref ++ suffix ∈ plusLang A.lang := by
  induction hrun generalizing p₀ pref with
  | nil q v =>
      have hpref : pref ∈ A.lang := ⟨p₀, hp₀, q, hqf, v, hprefix⟩
      simpa using subset_plusLang A.lang hpref
  | cons t ht hsource hlabel hnonneg hguards htail ih =>
      rename_i pcur qtail vcur vfTail d a wTail
      rcases ht with htA | hrestart
      · have hstep :
            RunFrom A pcur vcur [(d, a)] t.target
              (resetVal t.resets (delayVal d vcur)) :=
          RunFrom.cons t htA hsource hlabel hnonneg hguards
            (RunFrom.nil A t.target
              (resetVal t.resets (delayVal d vcur)))
        have hprefix' := runFrom_append hprefix hstep
        have htailPlus := ih hp₀ hprefix' hqf
        simpa [List.append_assoc] using htailPlus
      · rcases hrestart with ⟨tA, htA, htacc, q₀, hq₀, htEq⟩
        subst htEq
        have hstep :
            RunFrom A pcur vcur [(d, a)] tA.target
              (resetVal tA.resets (delayVal d vcur)) :=
          RunFrom.cons tA htA
            (by simpa [restartTransition] using hsource)
            (by simpa [restartTransition] using hlabel)
            hnonneg
            (by simpa [restartTransition] using hguards)
            (RunFrom.nil A tA.target
              (resetVal tA.resets (delayVal d vcur)))
        have hprefix' := runFrom_append hprefix hstep
        have hfirst : pref ++ [(d, a)] ∈ A.lang :=
          ⟨p₀, hp₀, tA.target, htacc,
            resetVal tA.resets (delayVal d vcur), hprefix'⟩
        have hzero :
            resetVal (restartTransition tA q₀).resets (delayVal d vcur) =
              zeroVal := by
          simpa [restartTransition] using
            resetVal_union_univ tA.resets (delayVal d vcur)
        have hnil :
            RunFrom A q₀ zeroVal [] (restartTransition tA q₀).target
              (resetVal (restartTransition tA q₀).resets (delayVal d vcur)) := by
          simpa [restartTransition, resetVal_univ] using
            (RunFrom.nil A q₀ zeroVal)
        have htailPlus :
            ([] : TimedWord α) ++ wTail ∈ plusLang A.lang :=
          ih hq₀ hnil hqf
        have htailPlus' : wTail ∈ plusLang A.lang := by
          simpa using htailPlus
        have hcombined := plusLang_cons hfirst htailPlus'
        simpa [List.append_assoc] using hcombined

theorem plus_sound (A : Automaton Loc α) :
    (plusTA A).lang ⊆ plusLang A.lang := by
  intro w h
  rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
  have hs :=
    plus_sound_aux (A := A) hq₀ (RunFrom.nil A q₀ zeroVal) hrun hqf
  simpa using hs

theorem plus_correct (A : Automaton Loc α) :
    (plusTA A).lang = plusLang A.lang :=
  Set.Subset.antisymm (plus_sound A) (plus_complete A)

def starTA (A : Automaton Loc α) : Automaton (Sum Nat Loc) α :=
  unionTaggedTA (epsilonTA α) (plusTA A)

theorem star_correct (A : Automaton Loc α) :
    (starTA A).lang = starLang A.lang := by
  rw [starTA, unionTagged_correct, epsilonTA_lang, plus_correct,
    starLang_empty_union_plus]

end LeanTre2Ta
