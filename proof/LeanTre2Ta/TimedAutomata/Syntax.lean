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

end LeanTre2Ta
