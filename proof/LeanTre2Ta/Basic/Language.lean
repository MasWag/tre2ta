import LeanTre2Ta.Basic.TimedWord

namespace LeanTre2Ta

def concatLang (L₁ L₂ : Set (TimedWord α)) : Set (TimedWord α) :=
  {w | ∃ w₁ ∈ L₁, ∃ w₂ ∈ L₂, w = w₁ ++ w₂}

def langPow (L : Set (TimedWord α)) : Nat → Set (TimedWord α)
  | 0 => {[]}
  | n + 1 => concatLang L (langPow L n)

def starLang (L : Set (TimedWord α)) : Set (TimedWord α) :=
  {w | ∃ n, w ∈ langPow L n}

def plusLang (L : Set (TimedWord α)) : Set (TimedWord α) :=
  {w | ∃ n, w ∈ langPow L (n + 1)}

theorem mem_concatLang {L₁ L₂ : Set (TimedWord α)} {w : TimedWord α} :
    w ∈ concatLang L₁ L₂ ↔ ∃ w₁ ∈ L₁, ∃ w₂ ∈ L₂, w = w₁ ++ w₂ := Iff.rfl

theorem mem_starLang {L : Set (TimedWord α)} {w : TimedWord α} :
    w ∈ starLang L ↔ ∃ n, w ∈ langPow L n := Iff.rfl

theorem mem_plusLang {L : Set (TimedWord α)} {w : TimedWord α} :
    w ∈ plusLang L ↔ ∃ n, w ∈ langPow L (n + 1) := Iff.rfl

theorem langPow_zero (L : Set (TimedWord α)) :
    langPow L 0 = {[]} := rfl

theorem langPow_succ (L : Set (TimedWord α)) (n : Nat) :
    langPow L (n + 1) = concatLang L (langPow L n) := rfl

theorem subset_plusLang (L : Set (TimedWord α)) :
    L ⊆ plusLang L := by
  intro w hw
  simp [plusLang, langPow, concatLang]
  use 0
  simp [langPow]
  exact hw

theorem plusLang_subset_starLang (L : Set (TimedWord α)) :
    plusLang L ⊆ starLang L := by
  intro w hw
  rcases hw with ⟨n, hn⟩
  simp [starLang]
  use (n + 1)

theorem starLang_empty_union_plus (L : Set (TimedWord α)) :
    starLang L = ({[]} : Set (TimedWord α)) ∪ plusLang L := by
  ext w
  constructor
  · intro hw
    rcases hw with ⟨n, hn⟩
    cases n with
    | zero =>
        unfold langPow at hn
        left
        exact hn
    | succ n =>
        right
        simp [plusLang]
        use n
  · intro hw
    rcases hw with hw | hw
    · simp [starLang]
      use 0
      simp [langPow]
      exact hw
    · rcases hw with ⟨n, hn⟩
      simp [starLang]
      use (n + 1)

end LeanTre2Ta
