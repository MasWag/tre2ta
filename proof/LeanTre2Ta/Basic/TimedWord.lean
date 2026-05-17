import LeanTre2Ta.Basic.Interval

namespace LeanTre2Ta

abbrev TimedWord (α : Type u) := List (ℝ × α)

namespace TimedWord

def WellFormed : TimedWord α → Prop
  | [] => True
  | x :: xs => 0 ≤ x.1 ∧ WellFormed xs

def duration : TimedWord α → ℝ
  | [] => 0
  | x :: xs => x.1 + duration xs

@[simp] theorem wellFormed_nil : WellFormed ([] : TimedWord α) := trivial

@[simp] theorem wellFormed_cons (d : ℝ) (a : α) (w : TimedWord α) :
    WellFormed ((d, a) :: w) ↔ 0 ≤ d ∧ WellFormed w := Iff.rfl

@[simp] theorem duration_nil : duration ([] : TimedWord α) = 0 := rfl

@[simp] theorem duration_cons (d : ℝ) (a : α) (w : TimedWord α) :
    duration ((d, a) :: w) = d + duration w := rfl

theorem duration_append (w₁ w₂ : TimedWord α) :
    duration (w₁ ++ w₂) = duration w₁ + duration w₂ := by
  induction w₁ with
  | nil => simp [duration]
  | cons x xs ih =>
      cases x
      simp [duration, ih, add_assoc]

theorem wellFormed_append {w₁ w₂ : TimedWord α} :
    WellFormed (w₁ ++ w₂) ↔ WellFormed w₁ ∧ WellFormed w₂ := by
  induction w₁ with
  | nil => simp [WellFormed]
  | cons x xs ih =>
      cases x
      simp [WellFormed, ih, and_assoc]

theorem duration_singleton (d : ℝ) (a : α) :
    duration ([(d, a)] : TimedWord α) = d := by
  simp [duration]

end TimedWord

end LeanTre2Ta

