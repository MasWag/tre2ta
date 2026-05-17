import LeanTre2Ta.TRE.Syntax
import LeanTre2Ta.Basic.Language

namespace LeanTre2Ta

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

end LeanTre2Ta
