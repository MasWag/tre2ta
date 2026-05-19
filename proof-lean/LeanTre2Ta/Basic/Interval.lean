import Mathlib.Data.Real.Basic

namespace LeanTre2Ta

structure Interval where
  lower : ℝ
  upper : Option ℝ
  lowerClosed : Bool
  upperClosed : Bool

namespace Interval

def mem (t : ℝ) (I : Interval) : Prop :=
  (if I.lowerClosed then I.lower ≤ t else I.lower < t) ∧
    match I.upper with
    | none => True
    | some u => if I.upperClosed then t ≤ u else t < u

@[simp] theorem mem_mk (t l : ℝ) (u : Option ℝ) (lc uc : Bool) :
    mem t ⟨l, u, lc, uc⟩ =
      ((if lc then l ≤ t else l < t) ∧
        match u with
        | none => True
        | some hi => if uc then t ≤ hi else t < hi) := rfl

end Interval

end LeanTre2Ta
