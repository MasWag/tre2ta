import LeanTre2Ta.Basic.Interval
import LeanTre2Ta.Basic.TimedWord

namespace LeanTre2Ta

abbrev Clock := Nat
abbrev Valuation := Clock → ℝ

def zeroVal : Valuation := fun _ => 0

def delayVal (d : ℝ) (v : Valuation) : Valuation :=
  fun x => v x + d

noncomputable def resetVal (resets : Set Clock) (v : Valuation) : Valuation :=
  fun x => by
    classical
    exact if x ∈ resets then 0 else v x

structure Guard where
  clock : Clock
  interval : Interval

namespace Guard

def sat (v : Valuation) (g : Guard) : Prop :=
  Interval.mem (v g.clock) g.interval

end Guard

def guardsSat (v : Valuation) (gs : List Guard) : Prop :=
  ∀ g, g ∈ gs → Guard.sat v g

def guardsUseClocks (gs : List Guard) (clocks : Set Clock) : Prop :=
  ∀ g, g ∈ gs → g.clock ∈ clocks

structure Transition (Loc : Type u) (Label : Type v) where
  source : Loc
  label : Label
  guards : List Guard
  resets : Set Clock
  target : Loc

structure Automaton (Loc : Type u) (Label : Type v) where
  locations : Set Loc
  initial : Set Loc
  accepting : Set Loc
  clocks : Set Clock
  transitions : Set (Transition Loc Label)

def guardsClosed (A : Automaton Loc Label) : Prop :=
  ∀ t ∈ A.transitions, guardsUseClocks t.guards A.clocks

def agreeOn (clocks : Set Clock) (v₁ v₂ : Valuation) : Prop :=
  ∀ x, x ∈ clocks → v₁ x = v₂ x

theorem delayVal_apply (d : ℝ) (v : Valuation) (x : Clock) :
    delayVal d v x = v x + d := rfl

theorem resetVal_mem {rs : Set Clock} {v : Valuation} {x : Clock} (h : x ∈ rs) :
    resetVal rs v x = 0 := by
  classical
  simp [resetVal, h]

theorem resetVal_not_mem {rs : Set Clock} {v : Valuation} {x : Clock} (h : x ∉ rs) :
    resetVal rs v x = v x := by
  classical
  simp [resetVal, h]

theorem agreeOn_refl (clocks : Set Clock) (v : Valuation) :
    agreeOn clocks v v := by
  intro x hx
  rfl

theorem agreeOn_symm {clocks : Set Clock} {v₁ v₂ : Valuation}
    (h : agreeOn clocks v₁ v₂) :
    agreeOn clocks v₂ v₁ := by
  intro x hx
  exact (h x hx).symm

theorem agreeOn_delay {clocks : Set Clock} {v₁ v₂ : Valuation}
    (h : agreeOn clocks v₁ v₂) (d : ℝ) :
    agreeOn clocks (delayVal d v₁) (delayVal d v₂) := by
  intro x hx
  simp [delayVal, h x hx]

theorem agreeOn_reset {clocks resets : Set Clock} {v₁ v₂ : Valuation}
    (h : agreeOn clocks v₁ v₂) :
    agreeOn clocks (resetVal resets v₁) (resetVal resets v₂) := by
  intro x hx
  by_cases hr : x ∈ resets
  · simp [resetVal, hr]
  · simp [resetVal, hr, h x hx]

theorem agreeOn_reset_of_subset {clocks resets : Set Clock} (v : Valuation)
    (hsub : clocks ⊆ resets) :
    agreeOn clocks (resetVal resets v) zeroVal := by
  intro x hx
  have hr : x ∈ resets := hsub hx
  simp [resetVal, zeroVal, hr]

theorem guardsSat_congr_agreeOn {clocks : Set Clock} {v₁ v₂ : Valuation}
    {gs : List Guard}
    (hgs : guardsUseClocks gs clocks)
    (hv : agreeOn clocks v₁ v₂) :
    guardsSat v₁ gs ↔ guardsSat v₂ gs := by
  constructor
  · intro h g hg
    have hclock := hv g.clock (hgs g hg)
    have hs := h g hg
    simpa [Guard.sat, hclock] using hs
  · intro h g hg
    have hclock := (hv g.clock (hgs g hg)).symm
    have hs := h g hg
    simpa [Guard.sat, hclock] using hs

theorem guardsUseClocks_mono {gs : List Guard} {clocks₁ clocks₂ : Set Clock}
    (hgs : guardsUseClocks gs clocks₁) (hsub : clocks₁ ⊆ clocks₂) :
    guardsUseClocks gs clocks₂ := by
  intro g hg
  exact hsub (hgs g hg)

theorem guardsUseClocks_append {gs₁ gs₂ : List Guard} {clocks : Set Clock} :
    guardsUseClocks (gs₁ ++ gs₂) clocks ↔
      guardsUseClocks gs₁ clocks ∧ guardsUseClocks gs₂ clocks := by
  constructor
  · intro h
    constructor
    · intro g hg
      exact h g (List.mem_append_left gs₂ hg)
    · intro g hg
      exact h g (List.mem_append_right gs₁ hg)
  · intro h g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.1 g hg
    · exact h.2 g hg

end LeanTre2Ta
