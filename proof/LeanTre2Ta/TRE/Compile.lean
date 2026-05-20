import LeanTre2Ta.TRE.Semantics
import LeanTre2Ta.TimedAutomata.Constructions.Kleene
import LeanTre2Ta.TimedAutomata.Constructions.Intersection
import LeanTre2Ta.TimedAutomata.Constructions.Trim

namespace LeanTre2Ta

structure SomeAutomaton (α : Type u) where
  Loc : Type
  aut : Automaton Loc α

namespace SomeAutomaton

def lang (A : SomeAutomaton α) : Set (TimedWord α) :=
  A.aut.lang

end SomeAutomaton

def compile [DecidableEq α] : TRE α → SomeAutomaton α
  | .empty => ⟨Nat, emptyTA α⟩
  | .epsilon => ⟨Nat, epsilonTA α⟩
  | .atom a => ⟨Nat, atomTA a⟩
  | .union r s =>
      let A := compile r
      let B := compile s
      ⟨Sum A.Loc B.Loc, unionTaggedTA A.aut B.aut⟩
  | .inter r s =>
      let A := compile r
      let B := compile s
      ⟨A.Loc × B.Loc,
        productTA (LabelAlgebra.equality (α := α)) A.aut B.aut⟩
  | .concat r s =>
      let A := compile r
      let B := compile s
      ⟨Sum A.Loc B.Loc, concatTA A.aut B.aut⟩
  | .star r =>
      let A := compile r
      ⟨Sum Nat A.Loc, starTA A.aut⟩
  | .plus r =>
      let A := compile r
      ⟨A.Loc, plusTA A.aut⟩
  | .within r I =>
      let A := compile r
      ⟨Option A.Loc, timeRestrictTA A.aut I⟩

def compile? [DecidableEq α] (r : TRE α) : Option (SomeAutomaton α) :=
  some (compile r)

theorem compile_guardsClosed [DecidableEq α] (r : TRE α) :
    guardsClosed (compile r).aut := by
  induction r with
  | empty =>
      simpa [compile] using (emptyTA_guardsClosed (α := α))
  | epsilon =>
      simpa [compile] using (epsilonTA_guardsClosed (α := α))
  | atom a =>
      simpa [compile] using atomTA_guardsClosed a
  | union r s ihr ihs =>
      simpa [compile] using unionTagged_guardsClosed ihr ihs
  | inter r s ihr ihs =>
      simpa [compile] using
        (product_guardsClosed
          (alg := LabelAlgebra.equality (α := α))
          (A := (compile r).aut) (B := (compile s).aut)
          ihr ihs)
  | concat r s ihr ihs =>
      simpa [compile] using concat_guardsClosed ihr ihs
  | star r ih =>
      simpa [compile] using star_guardsClosed ih
  | plus r ih =>
      simpa [compile] using plus_guardsClosed ih
  | within r I ih =>
      simpa [compile] using timeRestrict_guardsClosed (I := I) ih

theorem compile_correct [DecidableEq α] (r : TRE α) :
    (compile r).lang = TRE.lang r := by
  induction r with
  | empty =>
      simp [compile, SomeAutomaton.lang, TRE.lang]
  | epsilon =>
      simp [compile, SomeAutomaton.lang, TRE.lang]
  | atom a =>
      simp [compile, SomeAutomaton.lang, TRE.lang]
  | union r s ihr ihs =>
      rw [show (compile (TRE.union r s)).lang =
          (unionTaggedTA (compile r).aut (compile s).aut).lang by rfl,
        unionTagged_correct]
      rw [show (compile r).aut.lang = (compile r).lang by rfl,
        show (compile s).aut.lang = (compile s).lang by rfl,
        ihr, ihs]
      rfl
  | inter r s ihr ihs =>
      rw [show (compile (TRE.inter r s)).lang =
          (productTA (LabelAlgebra.equality (α := α))
            (compile r).aut (compile s).aut).lang by rfl,
        product_correct_eq]
      rw [show (compile r).aut.lang = (compile r).lang by rfl,
        show (compile s).aut.lang = (compile s).lang by rfl,
        ihr, ihs]
      rfl
  | concat r s ihr ihs =>
      rw [show (compile (TRE.concat r s)).lang =
          (concatTA (compile r).aut (compile s).aut).lang by rfl,
        concat_correct (hB := compile_guardsClosed s)]
      rw [show (compile r).aut.lang = (compile r).lang by rfl,
        show (compile s).aut.lang = (compile s).lang by rfl,
        ihr, ihs]
      rfl
  | star r ih =>
      rw [show (compile (TRE.star r)).lang =
          (starTA (compile r).aut).lang by rfl,
        star_correct]
      rw [show (compile r).aut.lang = (compile r).lang by rfl, ih]
      rfl
  | plus r ih =>
      rw [show (compile (TRE.plus r)).lang =
          (plusTA (compile r).aut).lang by rfl,
        plus_correct]
      rw [show (compile r).aut.lang = (compile r).lang by rfl, ih]
      rfl
  | within r I ih =>
      rw [show (compile (TRE.within r I)).lang =
          (timeRestrictTA (compile r).aut I).lang by rfl,
        timeRestrict_correct]
      rw [show (compile r).aut.lang = (compile r).lang by rfl, ih]
      rfl

theorem compile?_correct [DecidableEq α]
    {r : TRE α} {A : SomeAutomaton α}
    (h : compile? r = some A) :
    A.lang = TRE.lang r := by
  simp [compile?] at h
  cases h
  exact compile_correct r

theorem compile_trim_correct [DecidableEq α] (r : TRE α) :
    (trimToAccepting (compile r).aut).lang = TRE.lang r := by
  rw [trim_correct]
  simpa [SomeAutomaton.lang] using compile_correct r

theorem compile?_trim_correct [DecidableEq α]
    {r : TRE α} {A : SomeAutomaton α}
    (h : compile? r = some A) :
    (trimToAccepting A.aut).lang = TRE.lang r := by
  simp [compile?] at h
  cases h
  exact compile_trim_correct r

end LeanTre2Ta
