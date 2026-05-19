import LeanTre2Ta.TRE.Syntax

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

namespace TRE

def lang : TRE α → Set (TimedWord α)
  | empty => ∅
  | epsilon => {[]}
  | atom a => {w | ∃ d, 0 ≤ d ∧ w = [(d, a)]}
  | union r s => lang r ∪ lang s
  | inter r s => lang r ∩ lang s
  | concat r s => concatLang (lang r) (lang s)
  | star r => starLang (lang r)
  | plus r => plusLang (lang r)
  | within r I => {w | w ∈ lang r ∧ Interval.mem (TimedWord.duration w) I}

@[simp] theorem lang_empty : lang (empty : TRE α) = ∅ := rfl
@[simp] theorem lang_epsilon : lang (epsilon : TRE α) = {[]} := rfl
@[simp] theorem lang_atom (a : α) :
    lang (atom a) = {w | ∃ d, 0 ≤ d ∧ w = [(d, a)]} := rfl
@[simp] theorem lang_union (r s : TRE α) :
    lang (union r s) = lang r ∪ lang s := rfl
@[simp] theorem lang_inter (r s : TRE α) :
    lang (inter r s) = lang r ∩ lang s := rfl
@[simp] theorem lang_concat (r s : TRE α) :
    lang (concat r s) = concatLang (lang r) (lang s) := rfl
@[simp] theorem lang_star (r : TRE α) :
    lang (star r) = starLang (lang r) := rfl
@[simp] theorem lang_plus (r : TRE α) :
    lang (plus r) = plusLang (lang r) := rfl
@[simp] theorem lang_within (r : TRE α) (I : Interval) :
    lang (within r I) =
      {w | w ∈ lang r ∧ Interval.mem (TimedWord.duration w) I} := rfl

end TRE

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

