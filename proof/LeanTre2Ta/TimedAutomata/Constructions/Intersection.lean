import LeanTre2Ta.TimedAutomata.LabelAlgebra

namespace LeanTre2Ta

theorem guardsSat_append {v : Valuation} {g₁ g₂ : List Guard} :
    guardsSat v (g₁ ++ g₂) ↔ guardsSat v g₁ ∧ guardsSat v g₂ := by
  constructor
  · intro h
    constructor
    · intro g hg
      exact h g (List.mem_append_left g₂ hg)
    · intro g hg
      exact h g (List.mem_append_right g₁ hg)
  · intro h g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact h.1 g hg
    · exact h.2 g hg

theorem product_match_left {alg : LabelAlgebra Label Event}
    {l₁ l₂ l : Label} {e : Event}
    (hi : alg.labelIntersect l₁ l₂ = some l)
    (hm : alg.eventMatches l e) :
    alg.eventMatches l₁ e := by
  have hsem := alg.intersect_some hi
  have hp : e ∈ alg.labSem l₁ ∩ alg.labSem l₂ := by
    simpa [LabelAlgebra.eventMatches, hsem] using hm
  exact hp.1

theorem product_match_right {alg : LabelAlgebra Label Event}
    {l₁ l₂ l : Label} {e : Event}
    (hi : alg.labelIntersect l₁ l₂ = some l)
    (hm : alg.eventMatches l e) :
    alg.eventMatches l₂ e := by
  have hsem := alg.intersect_some hi
  have hp : e ∈ alg.labSem l₁ ∩ alg.labSem l₂ := by
    simpa [LabelAlgebra.eventMatches, hsem] using hm
  exact hp.2

def leftClock (x : Clock) : Clock := 2 * x

def rightClock (x : Clock) : Clock := 2 * x + 1

def renameGuard (f : Clock → Clock) (g : Guard) : Guard :=
  { clock := f g.clock
    interval := g.interval }

def renameResets (f : Clock → Clock) (rs : Set Clock) : Set Clock :=
  f '' rs

def leftVal (v : Valuation) : Valuation :=
  fun x => v (leftClock x)

def rightVal (v : Valuation) : Valuation :=
  fun x => v (rightClock x)

theorem leftClock_injective : Function.Injective leftClock := by
  intro x y h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h

theorem rightClock_injective : Function.Injective rightClock := by
  intro x y h
  have hmul : 2 * x = 2 * y := Nat.succ.inj h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hmul

theorem leftClock_ne_rightClock (x y : Clock) :
    leftClock x ≠ rightClock y := by
  intro h
  have hmod := congrArg (fun n : Nat => n % 2) h
  norm_num [leftClock, rightClock, Nat.mul_mod, Nat.add_mod] at hmod

theorem rightClock_ne_leftClock (x y : Clock) :
    rightClock x ≠ leftClock y := by
  intro h
  exact leftClock_ne_rightClock y x h.symm

theorem leftClock_mem_left_resets {rs : Set Clock} {x : Clock} :
    leftClock x ∈ renameResets leftClock rs ↔ x ∈ rs := by
  constructor
  · intro h
    rcases h with ⟨y, hy, hxy⟩
    have hyx : y = x := leftClock_injective hxy
    cases hyx
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem rightClock_mem_right_resets {rs : Set Clock} {x : Clock} :
    rightClock x ∈ renameResets rightClock rs ↔ x ∈ rs := by
  constructor
  · intro h
    rcases h with ⟨y, hy, hxy⟩
    have hyx : y = x := rightClock_injective hxy
    cases hyx
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem leftClock_not_mem_right_resets {rs : Set Clock} {x : Clock} :
    leftClock x ∉ renameResets rightClock rs := by
  intro h
  rcases h with ⟨y, hy, hxy⟩
  exact leftClock_ne_rightClock x y hxy.symm

theorem rightClock_not_mem_left_resets {rs : Set Clock} {x : Clock} :
    rightClock x ∉ renameResets leftClock rs := by
  intro h
  rcases h with ⟨y, hy, hxy⟩
  exact rightClock_ne_leftClock x y hxy.symm

theorem leftVal_zero :
    leftVal zeroVal = zeroVal := by
  ext x
  rfl

theorem rightVal_zero :
    rightVal zeroVal = zeroVal := by
  ext x
  rfl

theorem leftVal_delay (d : ℝ) (v : Valuation) :
    leftVal (delayVal d v) = delayVal d (leftVal v) := by
  ext x
  rfl

theorem rightVal_delay (d : ℝ) (v : Valuation) :
    rightVal (delayVal d v) = delayVal d (rightVal v) := by
  ext x
  rfl

theorem leftVal_reset_product (rs₁ rs₂ : Set Clock) (v : Valuation) :
    leftVal (resetVal (renameResets leftClock rs₁ ∪ renameResets rightClock rs₂) v) =
      resetVal rs₁ (leftVal v) := by
  ext x
  by_cases hx : x ∈ rs₁
  · have hmem :
        leftClock x ∈ renameResets leftClock rs₁ ∪ renameResets rightClock rs₂ := by
      exact Or.inl ((leftClock_mem_left_resets).2 hx)
    simp [leftVal, resetVal, hx, hmem]
  · have hnot :
        leftClock x ∉ renameResets leftClock rs₁ ∪ renameResets rightClock rs₂ := by
      intro h
      rcases h with hleft | hright
      · exact hx ((leftClock_mem_left_resets).1 hleft)
      · exact leftClock_not_mem_right_resets hright
    simp [leftVal, resetVal, hx, hnot]

theorem rightVal_reset_product (rs₁ rs₂ : Set Clock) (v : Valuation) :
    rightVal (resetVal (renameResets leftClock rs₁ ∪ renameResets rightClock rs₂) v) =
      resetVal rs₂ (rightVal v) := by
  ext x
  by_cases hx : x ∈ rs₂
  · have hmem :
        rightClock x ∈ renameResets leftClock rs₁ ∪ renameResets rightClock rs₂ := by
      exact Or.inr ((rightClock_mem_right_resets).2 hx)
    simp [rightVal, resetVal, hx, hmem]
  · have hnot :
        rightClock x ∉ renameResets leftClock rs₁ ∪ renameResets rightClock rs₂ := by
      intro h
      rcases h with hleft | hright
      · exact rightClock_not_mem_left_resets hleft
      · exact hx ((rightClock_mem_right_resets).1 hright)
    simp [rightVal, resetVal, hx, hnot]

theorem guardsSat_rename_left {v : Valuation} {gs : List Guard} :
    guardsSat v (gs.map (renameGuard leftClock)) ↔ guardsSat (leftVal v) gs := by
  constructor
  · intro h g hg
    have hmem : renameGuard leftClock g ∈ gs.map (renameGuard leftClock) :=
      List.mem_map.mpr ⟨g, hg, rfl⟩
    have hs := h (renameGuard leftClock g) hmem
    simpa [Guard.sat, renameGuard, leftVal] using hs
  · intro h g hg
    rcases List.mem_map.mp hg with ⟨g₀, hg₀, rfl⟩
    have hs := h g₀ hg₀
    simpa [Guard.sat, renameGuard, leftVal] using hs

theorem guardsSat_rename_right {v : Valuation} {gs : List Guard} :
    guardsSat v (gs.map (renameGuard rightClock)) ↔ guardsSat (rightVal v) gs := by
  constructor
  · intro h g hg
    have hmem : renameGuard rightClock g ∈ gs.map (renameGuard rightClock) :=
      List.mem_map.mpr ⟨g, hg, rfl⟩
    have hs := h (renameGuard rightClock g) hmem
    simpa [Guard.sat, renameGuard, rightVal] using hs
  · intro h g hg
    rcases List.mem_map.mp hg with ⟨g₀, hg₀, rfl⟩
    have hs := h g₀ hg₀
    simpa [Guard.sat, renameGuard, rightVal] using hs

def productTransition (t₁ : Transition Loc₁ Label)
    (t₂ : Transition Loc₂ Label) (label : Label) :
    Transition (Loc₁ × Loc₂) Label :=
  { source := (t₁.source, t₂.source)
    label := label
    guards := t₁.guards.map (renameGuard leftClock) ++
      t₂.guards.map (renameGuard rightClock)
    resets := renameResets leftClock t₁.resets ∪
      renameResets rightClock t₂.resets
    target := (t₁.target, t₂.target) }

def productTA (alg : LabelAlgebra Label Event)
    (A : Automaton Loc₁ Label) (B : Automaton Loc₂ Label) :
    Automaton (Loc₁ × Loc₂) Label :=
  { locations := {p | p.1 ∈ A.locations ∧ p.2 ∈ B.locations}
    initial := {p | p.1 ∈ A.initial ∧ p.2 ∈ B.initial}
    accepting := {p | p.1 ∈ A.accepting ∧ p.2 ∈ B.accepting}
    clocks := (leftClock '' A.clocks) ∪ (rightClock '' B.clocks)
    transitions := {u | ∃ t₁ ∈ A.transitions, ∃ t₂ ∈ B.transitions,
      ∃ l, alg.labelIntersect t₁.label t₂.label = some l ∧
        u = productTransition t₁ t₂ l} }

theorem runFromL_product_left_aux {alg : LabelAlgebra Label Event}
    {A : Automaton Loc₁ Label} {B : Automaton Loc₂ Label}
    {qstart qend : Loc₁ × Loc₂} {p₁ q₁ : Loc₁} {p₂ q₂ : Loc₂}
    {v vf : Valuation} {w : TimedWord Event}
    (hrun : LabelAlgebra.RunFromL alg (productTA alg A B) qstart v w qend vf)
    (hstart : qstart = (p₁, p₂)) (hend : qend = (q₁, q₂)) :
    LabelAlgebra.RunFromL alg A p₁ (leftVal v) w q₁ (leftVal vf) := by
  induction hrun generalizing p₁ p₂ q₁ q₂ with
  | nil q v =>
      cases hstart
      cases hend
      exact LabelAlgebra.RunFromL.nil A p₁ (leftVal v)
  | cons t ht hsource hmatch hnonneg hguards htail ih =>
      rename_i pprod qprod v0 vf0 d a wTail
      rcases ht with ⟨t₁, ht₁, t₂, ht₂, l, hi, htEq⟩
      subst htEq
      have hsrc : p₁ = t₁.source ∧ p₂ = t₂.source := by
        simpa [productTransition, hstart] using hsource.symm
      rcases hsrc with ⟨hp₁, hp₂⟩
      cases hp₁
      cases hp₂
      have htailLeft := ih rfl hend
      have htailLeft' :
          LabelAlgebra.RunFromL alg A t₁.target
            (resetVal t₁.resets (delayVal d (leftVal v0))) wTail q₁
            (leftVal vf0) := by
        simpa [productTransition, leftVal_delay, leftVal_reset_product] using htailLeft
      exact LabelAlgebra.RunFromL.cons t₁ ht₁ rfl
        (product_match_left hi hmatch) hnonneg
        (by
          have hleftguards := guardsSat_rename_left.mp
            ((guardsSat_append.mp (by simpa [productTransition] using hguards)).1)
          simpa [leftVal_delay] using hleftguards)
        htailLeft'

theorem runFromL_product_right_aux {alg : LabelAlgebra Label Event}
    {A : Automaton Loc₁ Label} {B : Automaton Loc₂ Label}
    {qstart qend : Loc₁ × Loc₂} {p₁ q₁ : Loc₁} {p₂ q₂ : Loc₂}
    {v vf : Valuation} {w : TimedWord Event}
    (hrun : LabelAlgebra.RunFromL alg (productTA alg A B) qstart v w qend vf)
    (hstart : qstart = (p₁, p₂)) (hend : qend = (q₁, q₂)) :
    LabelAlgebra.RunFromL alg B p₂ (rightVal v) w q₂ (rightVal vf) := by
  induction hrun generalizing p₁ p₂ q₁ q₂ with
  | nil q v =>
      cases hstart
      cases hend
      exact LabelAlgebra.RunFromL.nil B p₂ (rightVal v)
  | cons t ht hsource hmatch hnonneg hguards htail ih =>
      rename_i pprod qprod v0 vf0 d a wTail
      rcases ht with ⟨t₁, ht₁, t₂, ht₂, l, hi, htEq⟩
      subst htEq
      have hsrc : p₁ = t₁.source ∧ p₂ = t₂.source := by
        simpa [productTransition, hstart] using hsource.symm
      rcases hsrc with ⟨hp₁, hp₂⟩
      cases hp₁
      cases hp₂
      have htailRight := ih rfl hend
      have htailRight' :
          LabelAlgebra.RunFromL alg B t₂.target
            (resetVal t₂.resets (delayVal d (rightVal v0))) wTail q₂
            (rightVal vf0) := by
        simpa [productTransition, rightVal_delay, rightVal_reset_product] using htailRight
      exact LabelAlgebra.RunFromL.cons t₂ ht₂ rfl
        (product_match_right hi hmatch) hnonneg
        (by
          have hrightguards := guardsSat_rename_right.mp
            ((guardsSat_append.mp (by simpa [productTransition] using hguards)).2)
          simpa [rightVal_delay] using hrightguards)
        htailRight'

theorem runFromL_product_left {alg : LabelAlgebra Label Event}
    {A : Automaton Loc₁ Label} {B : Automaton Loc₂ Label}
    {p₁ q₁ : Loc₁} {p₂ q₂ : Loc₂} {v vf : Valuation}
    {w : TimedWord Event}
    (hrun : LabelAlgebra.RunFromL alg (productTA alg A B)
      (p₁, p₂) v w (q₁, q₂) vf) :
    LabelAlgebra.RunFromL alg A p₁ (leftVal v) w q₁ (leftVal vf) :=
  runFromL_product_left_aux (A := A) (B := B) hrun rfl rfl

theorem runFromL_product_right {alg : LabelAlgebra Label Event}
    {A : Automaton Loc₁ Label} {B : Automaton Loc₂ Label}
    {p₁ q₁ : Loc₁} {p₂ q₂ : Loc₂} {v vf : Valuation}
    {w : TimedWord Event}
    (hrun : LabelAlgebra.RunFromL alg (productTA alg A B)
      (p₁, p₂) v w (q₁, q₂) vf) :
    LabelAlgebra.RunFromL alg B p₂ (rightVal v) w q₂ (rightVal vf) :=
  runFromL_product_right_aux (A := A) (B := B) hrun rfl rfl

theorem product_sound {alg : LabelAlgebra Label Event}
    (A : Automaton Loc₁ Label) (B : Automaton Loc₂ Label) :
    (productTA alg A B).langL alg ⊆ A.langL alg ∩ B.langL alg := by
  intro w h
  rcases h with ⟨q₀, hq₀, qf, hqf, vf, hrun⟩
  rcases q₀ with ⟨p₀, r₀⟩
  rcases qf with ⟨pf, rf⟩
  exact ⟨
    ⟨p₀, hq₀.1, pf, hqf.1, leftVal vf, by
      simpa [leftVal_zero] using runFromL_product_left hrun⟩,
    ⟨r₀, hq₀.2, rf, hqf.2, rightVal vf, by
      simpa [rightVal_zero] using runFromL_product_right hrun⟩⟩

theorem runFromL_product_sync {alg : LabelAlgebra Label Event}
    {A : Automaton Loc₁ Label} {B : Automaton Loc₂ Label}
    {p₁ q₁ : Loc₁} {p₂ q₂ : Loc₂} {v v₁ v₂ vf₁ vf₂ : Valuation}
    {w : TimedWord Event}
    (hleft : leftVal v = v₁)
    (hright : rightVal v = v₂)
    (h₁ : LabelAlgebra.RunFromL alg A p₁ v₁ w q₁ vf₁)
    (h₂ : LabelAlgebra.RunFromL alg B p₂ v₂ w q₂ vf₂) :
    ∃ vf, leftVal vf = vf₁ ∧ rightVal vf = vf₂ ∧
      LabelAlgebra.RunFromL alg (productTA alg A B)
        (p₁, p₂) v w (q₁, q₂) vf := by
  induction h₁ generalizing p₂ q₂ v vf₂ v₂ with
  | nil q v₁ =>
      cases h₂ with
      | nil =>
          exact ⟨v, hleft, hright,
            LabelAlgebra.RunFromL.nil (productTA alg A B) (q, p₂) v⟩
  | cons t₁ ht₁ hsource₁ hmatch₁ hnonneg₁ hguards₁ htail₁ ih =>
      rename_i pA qA vA vfA d a wTail
      cases h₂ with
      | cons t₂ ht₂ hsource₂ hmatch₂ hnonneg₂ hguards₂ htail₂ =>
          rcases alg.labelIntersect_complete hmatch₁ hmatch₂ with ⟨l, hi, hmatch⟩
          let vNext :=
            resetVal (renameResets leftClock t₁.resets ∪ renameResets rightClock t₂.resets)
              (delayVal d v)
          have hleftNext :
              leftVal vNext = resetVal t₁.resets (delayVal d vA) := by
            dsimp [vNext]
            rw [leftVal_reset_product, leftVal_delay, hleft]
          have hrightNext :
              rightVal vNext = resetVal t₂.resets (delayVal d v₂) := by
            dsimp [vNext]
            rw [rightVal_reset_product, rightVal_delay, hright]
          rcases ih hleftNext hrightNext htail₂ with ⟨vf, hvf₁, hvf₂, htailProd⟩
          refine ⟨vf, hvf₁, hvf₂, ?_⟩
          exact LabelAlgebra.RunFromL.cons
            (productTransition t₁ t₂ l)
            (by exact ⟨t₁, ht₁, t₂, ht₂, l, hi, rfl⟩)
            (by simp [productTransition, hsource₁, hsource₂])
            (by simpa [productTransition] using hmatch)
            hnonneg₁
            (by
              have hguards₁' : guardsSat (delayVal d v)
                  (t₁.guards.map (renameGuard leftClock)) := by
                apply guardsSat_rename_left.mpr
                have hv : leftVal (delayVal d v) = delayVal d vA := by
                  rw [leftVal_delay, hleft]
                simpa [hv] using hguards₁
              have hguards₂' : guardsSat (delayVal d v)
                  (t₂.guards.map (renameGuard rightClock)) := by
                apply guardsSat_rename_right.mpr
                have hv : rightVal (delayVal d v) = delayVal d v₂ := by
                  rw [rightVal_delay, hright]
                simpa [hv] using hguards₂
              simpa [productTransition] using
                (guardsSat_append.mpr ⟨hguards₁', hguards₂'⟩))
            (by
              dsimp [vNext] at htailProd
              simpa [productTransition] using htailProd)

theorem product_complete {alg : LabelAlgebra Label Event}
    (A : Automaton Loc₁ Label) (B : Automaton Loc₂ Label) :
    A.langL alg ∩ B.langL alg ⊆ (productTA alg A B).langL alg := by
  intro w h
  rcases h with ⟨hA, hB⟩
  rcases hA with ⟨p₀, hp₀, pf, hpf, vfA, hrunA⟩
  rcases hB with ⟨q₀, hq₀, qf, hqf, vfB, hrunB⟩
  rcases runFromL_product_sync
      (A := A) (B := B) (v := zeroVal)
      (by exact leftVal_zero) (by exact rightVal_zero) hrunA hrunB with
    ⟨vf, hvfA, hvfB, hrun⟩
  exact ⟨(p₀, q₀), ⟨hp₀, hq₀⟩, (pf, qf), ⟨hpf, hqf⟩, vf, hrun⟩

theorem product_correct {alg : LabelAlgebra Label Event}
    (A : Automaton Loc₁ Label) (B : Automaton Loc₂ Label) :
    (productTA alg A B).langL alg = A.langL alg ∩ B.langL alg :=
  Set.Subset.antisymm (product_sound A B) (product_complete A B)

theorem product_correct_eq [DecidableEq α]
    (A : Automaton Loc₁ α) (B : Automaton Loc₂ α) :
    (productTA (LabelAlgebra.equality (α := α)) A B).lang =
      A.lang ∩ B.lang := by
  rw [← Automaton.langL_eq_lang (productTA (LabelAlgebra.equality (α := α)) A B),
    product_correct (alg := LabelAlgebra.equality (α := α)) A B,
    Automaton.langL_eq_lang A, Automaton.langL_eq_lang B]

theorem product_guardsClosed {alg : LabelAlgebra Label Event}
    {A : Automaton Loc₁ Label} {B : Automaton Loc₂ Label}
    (hA : guardsClosed A) (hB : guardsClosed B) :
    guardsClosed (productTA alg A B) := by
  intro t ht g hg
  rcases ht with ⟨t₁, ht₁, t₂, ht₂, l, hi, rfl⟩
  have hg' :
      g ∈ t₁.guards.map (renameGuard leftClock) ++
        t₂.guards.map (renameGuard rightClock) := by
    simpa [productTransition] using hg
  rcases List.mem_append.mp hg' with hleft | hright
  · rcases List.mem_map.mp hleft with ⟨g₁, hg₁, rfl⟩
    exact Or.inl ⟨g₁.clock, hA t₁ ht₁ g₁ hg₁, rfl⟩
  · rcases List.mem_map.mp hright with ⟨g₂, hg₂, rfl⟩
    exact Or.inr ⟨g₂.clock, hB t₂ ht₂ g₂ hg₂, rfl⟩

end LeanTre2Ta
