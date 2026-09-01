import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Arrow Impossibility
Category: Frontier Mind
Target: Frontier.arrow_impossibility
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
(Note: Lean 4 does not allow a module doc-comment to precede `import`,
so this required header is given as an ordinary block comment.)
-/

import Mathlib

/-!
Arrow's impossibility theorem.

A *preference* on a type of alternatives `A` is a linear order in the "weak" sense:
a total, transitive, antisymmetric relation `pref`, where `pref x y` reads
"`x` is at least as good as `y`".  `better x y` means `x` is strictly better than `y`.

A *social welfare function* is a map `F` from profiles (one preference per voter)
to a single preference.  Arrow's theorem says that with at least three alternatives and a
finite nonempty electorate, no such `F` can simultaneously satisfy unanimity (Pareto),
independence of irrelevant alternatives, and non-dictatorship.

The proof formalized here is the classical "decisive coalitions" argument:
the field-expansion lemma upgrades weak decisiveness over one pair to full decisiveness,
the contraction lemma splits a decisive coalition, and finiteness of the electorate then
produces a decisive singleton, i.e. a dictator.
-/

namespace Frontier

/-- A ranking of the alternatives `A`: a total, transitive, antisymmetric relation.
`pref x y` means "`x` is at least as good as `y`". -/
structure Pref (A : Type*) where
  /-- `pref x y` : the alternative `x` is at least as good as the alternative `y`. -/
  pref : A → A → Prop
  total' : ∀ x y, pref x y ∨ pref y x
  trans' : ∀ x y z, pref x y → pref y z → pref x z
  antisymm' : ∀ x y, pref x y → pref y x → x = y

namespace Pref

variable {A : Type*} (r : Pref A) {x y z b c : A}

/-- `r.better x y` : the alternative `x` is strictly better than `y` according to `r`. -/
def better (x y : A) : Prop := ¬ r.pref y x

lemma refl' (x : A) : r.pref x x := by
  rcases r.total' x x with h | h <;> exact h

lemma not_better_self (x : A) : ¬ r.better x x := fun h => h (r.refl' x)

lemma pref_of_better (h : r.better x y) : r.pref x y := by
  rcases r.total' x y with h' | h'
  · exact h'
  · exact absurd h' h

lemma ne_of_better (h : r.better x y) : x ≠ y := by
  rintro rfl; exact r.not_better_self x h

lemma better_trans (h₁ : r.better x y) (h₂ : r.better y z) : r.better x z := by
  intro hzx
  rcases r.total' x y with h | h
  · exact h₂ (r.trans' z x y hzx h)
  · exact h₁ h

lemma better_of_pref_of_better (h₁ : r.pref x y) (h₂ : r.better y z) : r.better x z := by
  intro hzx
  exact h₂ (r.trans' z x y hzx h₁)

lemma better_of_better_of_pref (h₁ : r.better x y) (h₂ : r.pref y z) : r.better x z := by
  intro hzx
  exact h₁ (r.trans' y z x h₂ hzx)

/-- Modify `r` by moving `b` to the top. -/
def pushTop (r : Pref A) (b : A) : Pref A where
  pref x y := x = b ∨ (y ≠ b ∧ r.pref x y)
  total' x y := by
    by_cases hx : x = b
    · exact Or.inl (Or.inl hx)
    · by_cases hy : y = b
      · exact Or.inr (Or.inl hy)
      · rcases r.total' x y with h | h
        · exact Or.inl (Or.inr ⟨hy, h⟩)
        · exact Or.inr (Or.inr ⟨hx, h⟩)
  trans' x y z h₁ h₂ := by
    rcases h₁ with rfl | ⟨hyb, hxy⟩
    · exact Or.inl rfl
    · rcases h₂ with rfl | ⟨hzb, hyz⟩
      · exact absurd rfl hyb
      · exact Or.inr ⟨hzb, r.trans' _ _ _ hxy hyz⟩
  antisymm' x y h₁ h₂ := by
    rcases h₁ with rfl | ⟨hyb, hxy⟩
    · rcases h₂ with rfl | ⟨hxb, _⟩
      · rfl
      · exact absurd rfl hxb
    · rcases h₂ with rfl | ⟨_, hyx⟩
      · exact absurd rfl hyb
      · exact r.antisymm' _ _ hxy hyx

/-- Modify `r` by moving `c` to the bottom. -/
def pushBot (r : Pref A) (c : A) : Pref A where
  pref x y := y = c ∨ (x ≠ c ∧ r.pref x y)
  total' x y := by
    by_cases hy : y = c
    · exact Or.inl (Or.inl hy)
    · by_cases hx : x = c
      · exact Or.inr (Or.inl hx)
      · rcases r.total' x y with h | h
        · exact Or.inl (Or.inr ⟨hx, h⟩)
        · exact Or.inr (Or.inr ⟨hy, h⟩)
  trans' x y z h₁ h₂ := by
    rcases h₂ with rfl | ⟨hyc, hyz⟩
    · exact Or.inl rfl
    · rcases h₁ with rfl | ⟨hxc, hxy⟩
      · exact absurd rfl hyc
      · exact Or.inr ⟨hxc, r.trans' _ _ _ hxy hyz⟩
  antisymm' x y h₁ h₂ := by
    rcases h₁ with rfl | ⟨hxc, hxy⟩
    · rcases h₂ with rfl | ⟨hyc, _⟩
      · rfl
      · exact absurd rfl hyc
    · rcases h₂ with rfl | ⟨_, hyx⟩
      · exact absurd rfl hxc
      · exact r.antisymm' _ _ hxy hyx

@[simp] lemma pushTop_pref_top (b x : A) : (r.pushTop b).pref b x := Or.inl rfl

lemma pushTop_not_pref_top (hx : x ≠ b) : ¬ (r.pushTop b).pref x b := by
  rintro (rfl | ⟨h, -⟩)
  · exact hx rfl
  · exact h rfl

lemma pushTop_better_top (hy : y ≠ b) : (r.pushTop b).better b y :=
  r.pushTop_not_pref_top hy

lemma pushTop_pref_iff (hx : x ≠ b) (hy : y ≠ b) :
    (r.pushTop b).pref x y ↔ r.pref x y := by
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · exact absurd rfl hx
    · exact h
  · intro h; exact Or.inr ⟨hy, h⟩

lemma pushTop_better_iff (hx : x ≠ b) (hy : y ≠ b) :
    (r.pushTop b).better x y ↔ r.better x y := by
  simp only [better, r.pushTop_pref_iff hy hx]

@[simp] lemma pushBot_pref_bot (c x : A) : (r.pushBot c).pref x c := Or.inl rfl

lemma pushBot_not_pref_bot (hy : y ≠ c) : ¬ (r.pushBot c).pref c y := by
  rintro (rfl | ⟨h, -⟩)
  · exact hy rfl
  · exact h rfl

lemma pushBot_better_bot (hy : y ≠ c) : (r.pushBot c).better y c :=
  r.pushBot_not_pref_bot hy

lemma pushBot_pref_iff (hx : x ≠ c) (hy : y ≠ c) :
    (r.pushBot c).pref x y ↔ r.pref x y := by
  constructor
  · rintro (rfl | ⟨-, h⟩)
    · exact absurd rfl hy
    · exact h
  · intro h; exact Or.inr ⟨hx, h⟩

/-- Modify `r` so that `x` is the top alternative and `y` the second one. -/
def twoTop (r : Pref A) (x y : A) : Pref A := (r.pushTop y).pushTop x

lemma twoTop_better_fst (hzx : z ≠ x) : (r.twoTop x y).better x z :=
  (r.pushTop y).pushTop_better_top hzx

lemma twoTop_not_pref_fst (hzx : z ≠ x) : ¬ (r.twoTop x y).pref z x :=
  (r.pushTop y).pushTop_not_pref_top hzx

lemma twoTop_better_snd (hyx : y ≠ x) (hzx : z ≠ x) (hzy : z ≠ y) :
    (r.twoTop x y).better y z := by
  rw [twoTop, (r.pushTop y).pushTop_better_iff hyx hzx]
  exact r.pushTop_better_top hzy

lemma twoTop_pref_snd (hyx : y ≠ x) (hzx : z ≠ x) (hzy : z ≠ y) :
    (r.twoTop x y).pref y z :=
  (r.twoTop x y).pref_of_better (r.twoTop_better_snd hyx hzx hzy)

/-- A preference built from an injection into a linearly ordered type. -/
def ofInjective {B : Type*} [LinearOrder B] (f : A → B) (hf : Function.Injective f) :
    Pref A where
  pref x y := f x ≤ f y
  total' x y := le_total (f x) (f y)
  trans' _ _ _ h₁ h₂ := le_trans h₁ h₂
  antisymm' _ _ h₁ h₂ := hf (le_antisymm h₁ h₂)

end Pref

section Definitions

variable {V A : Type*} (F : (V → Pref A) → Pref A)

/-- Unanimity (the Pareto condition): if every voter strictly prefers `x` to `y`,
so does society. -/
def Unanimity : Prop :=
  ∀ (p : V → Pref A) (x y : A), (∀ v, (p v).better x y) → (F p).better x y

/-- Independence of irrelevant alternatives: society's ranking of the pair `(x, y)`
depends only on the voters' rankings of that pair. -/
def IIA : Prop :=
  ∀ (p q : V → Pref A) (x y : A),
    (∀ v, ((p v).pref x y ↔ (q v).pref x y)) → ((F p).pref x y ↔ (F q).pref x y)

/-- The voter `d` is a dictator: society always follows `d`'s strict preferences. -/
def IsDictator (d : V) : Prop :=
  ∀ (p : V → Pref A) (x y : A), (p d).better x y → (F p).better x y

/-- The coalition `S` is decisive for the ordered pair `(x, y)`: whenever all its members
strictly prefer `x` to `y`, so does society, regardless of the other voters. -/
def DecisiveFor (S : Set V) (x y : A) : Prop :=
  ∀ p : V → Pref A, (∀ v ∈ S, (p v).better x y) → (F p).better x y

/-- The coalition `S` is decisive: it is decisive for every ordered pair of distinct
alternatives. -/
def Decisive (S : Set V) : Prop := ∀ x y : A, x ≠ y → DecisiveFor F S x y

/-- The coalition `S` is weakly decisive for `(x, y)`: if its members prefer `x` to `y`
*and everybody else prefers `y` to `x`*, then society prefers `x` to `y`. -/
def WeaklyDecisive (S : Set V) (x y : A) : Prop :=
  ∀ p : V → Pref A, (∀ v ∈ S, (p v).better x y) → (∀ v ∉ S, (p v).better y x) →
    (F p).better x y

end Definitions

section Proof

variable {V A : Type*} {F : (V → Pref A) → Pref A}

lemma weaklyDecisive_of_decisiveFor {S : Set V} {x y : A} (h : DecisiveFor F S x y) :
    WeaklyDecisive F S x y := fun p hp _ => h p hp

/-- Transfer of a strict social preference between profiles agreeing on a pair (IIA). -/
lemma iia_better (hI : IIA F) (p q : V → Pref A) (x y : A)
    (h : ∀ v, ((p v).pref x y ↔ (q v).pref x y)) :
    ((F p).better y x ↔ (F q).better y x) := by
  have := hI p q x y h
  simp only [Pref.better]
  exact not_congr this

/-- Field expansion, first half: if `S` is weakly decisive for `(a, b)` then it is
decisive for `(a, c)`. -/
lemma decisiveFor_fst (hU : Unanimity F) (hI : IIA F) {S : Set V} {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hW : WeaklyDecisive F S a b) :
    DecisiveFor F S a c := by
  classical
  intro q hq
  set p : V → Pref A := fun v => if v ∈ S then (q v).twoTop a b else (q v).pushTop b with hp
  have hpS : ∀ v ∈ S, p v = (q v).twoTop a b := by intro v hv; simp [hp, hv]
  have hpN : ∀ v ∉ S, p v = (q v).pushTop b := by intro v hv; simp [hp, hv]
  -- society prefers `a` to `b`
  have h1 : (F p).better a b := by
    refine hW p (fun v hv => ?_) (fun v hv => ?_)
    · rw [hpS v hv]; exact (q v).twoTop_better_fst (Ne.symm hab)
    · rw [hpN v hv]; exact (q v).pushTop_better_top hab
  -- society prefers `b` to `c` by unanimity
  have h2 : (F p).better b c := by
    refine hU p b c (fun v => ?_)
    by_cases hv : v ∈ S
    · rw [hpS v hv]
      exact (q v).twoTop_better_snd (Ne.symm hab) (Ne.symm hac) (Ne.symm hbc)
    · rw [hpN v hv]; exact (q v).pushTop_better_top (Ne.symm hbc)
  have h3 : (F p).better a c := (F p).better_trans h1 h2
  -- transfer to `q` by IIA on the pair `(c, a)`
  have hagree : ∀ v, ((p v).pref c a ↔ (q v).pref c a) := by
    intro v
    by_cases hv : v ∈ S
    · rw [hpS v hv]
      constructor
      · intro h; exact absurd h ((q v).twoTop_not_pref_fst (Ne.symm hac))
      · intro h; exact absurd h (hq v hv)
    · rw [hpN v hv]; exact (q v).pushTop_pref_iff (Ne.symm hbc) hab
  exact (iia_better hI p q c a hagree).mp h3

/-- Field expansion, second half: if `S` is weakly decisive for `(a, b)` then it is
decisive for `(c, b)`. -/
lemma decisiveFor_snd (hU : Unanimity F) (hI : IIA F) {S : Set V} {a b c : A}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hW : WeaklyDecisive F S a b) :
    DecisiveFor F S c b := by
  classical
  intro q hq
  set p : V → Pref A := fun v => if v ∈ S then (q v).twoTop c a else (q v).pushBot a with hp
  have hpS : ∀ v ∈ S, p v = (q v).twoTop c a := by intro v hv; simp [hp, hv]
  have hpN : ∀ v ∉ S, p v = (q v).pushBot a := by intro v hv; simp [hp, hv]
  have h1 : (F p).better a b := by
    refine hW p (fun v hv => ?_) (fun v hv => ?_)
    · rw [hpS v hv]
      exact (q v).twoTop_better_snd hac hbc (Ne.symm hab)
    · rw [hpN v hv]; exact (q v).pushBot_better_bot (Ne.symm hab)
  have h2 : (F p).better c a := by
    refine hU p c a (fun v => ?_)
    by_cases hv : v ∈ S
    · rw [hpS v hv]; exact (q v).twoTop_better_fst hac
    · rw [hpN v hv]; exact (q v).pushBot_better_bot (Ne.symm hac)
  have h3 : (F p).better c b := (F p).better_trans h2 h1
  have hagree : ∀ v, ((p v).pref b c ↔ (q v).pref b c) := by
    intro v
    by_cases hv : v ∈ S
    · rw [hpS v hv]
      constructor
      · intro h; exact absurd h ((q v).twoTop_not_pref_fst hbc)
      · intro h; exact absurd h (hq v hv)
    · rw [hpN v hv]; exact (q v).pushBot_pref_iff (Ne.symm hab) (Ne.symm hac)
  exact (iia_better hI p q b c hagree).mp h3

/-- Field expansion lemma: weak decisiveness over a single pair implies full decisiveness. -/
lemma decisive_of_weaklyDecisive (hU : Unanimity F) (hI : IIA F)
    (h3 : ∀ x y : A, ∃ z, z ≠ x ∧ z ≠ y) {S : Set V} {a b : A} (hab : a ≠ b)
    (hW : WeaklyDecisive F S a b) : Decisive F S := by
  obtain ⟨c, hca, hcb⟩ := h3 a b
  -- `a` is decisive against every other alternative
  have step1 : ∀ t, t ≠ a → t ≠ b → DecisiveFor F S a t := fun t hta htb =>
    decisiveFor_fst hU hI hab (Ne.symm hta) (Ne.symm htb) hW
  -- a chain of six applications yields decisiveness for `(a, b)` itself
  have dac : DecisiveFor F S a c := step1 c hca hcb
  have dbc : DecisiveFor F S b c :=
    decisiveFor_snd hU hI (Ne.symm hca) hab hcb
      (weaklyDecisive_of_decisiveFor dac)
  have dba : DecisiveFor F S b a :=
    decisiveFor_fst hU hI (Ne.symm hcb) (Ne.symm hab) hca
      (weaklyDecisive_of_decisiveFor dbc)
  have dca : DecisiveFor F S c a :=
    decisiveFor_snd hU hI (Ne.symm hab) (Ne.symm hcb) (Ne.symm hca)
      (weaklyDecisive_of_decisiveFor dba)
  have dcb : DecisiveFor F S c b :=
    decisiveFor_fst hU hI hca hcb hab
      (weaklyDecisive_of_decisiveFor dca)
  have dab : DecisiveFor F S a b :=
    decisiveFor_snd hU hI hcb hca (Ne.symm hab)
      (weaklyDecisive_of_decisiveFor dcb)
  have hall : ∀ t, t ≠ a → DecisiveFor F S a t := by
    intro t hta
    by_cases htb : t = b
    · subst htb; exact dab
    · exact step1 t hta htb
  intro x y hxy
  by_cases hxa : x = a
  · subst hxa; exact hall y (Ne.symm hxy)
  · by_cases hya : y = a
    · subst hya
      obtain ⟨w, hwx, hwy⟩ := h3 x y
      have dxw : DecisiveFor F S x w :=
        decisiveFor_snd hU hI (Ne.symm hwy) (Ne.symm hxa) hwx
          (weaklyDecisive_of_decisiveFor (hall w hwy))
      exact decisiveFor_fst hU hI (Ne.symm hwx) hxa hwy
        (weaklyDecisive_of_decisiveFor dxw)
    · exact decisiveFor_snd hU hI (Ne.symm hya) (Ne.symm hxa) (Ne.symm hxy)
        (weaklyDecisive_of_decisiveFor (hall y hya))

/-- Three distinct alternatives exist. -/
lemma exists_three [Nonempty A] (h3 : ∀ x y : A, ∃ z, z ≠ x ∧ z ≠ y) :
    ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨a⟩ := ‹Nonempty A›
  obtain ⟨b, hba, -⟩ := h3 a a
  obtain ⟨c, hca, hcb⟩ := h3 a b
  exact ⟨a, b, c, Ne.symm hba, Ne.symm hca, Ne.symm hcb⟩

/-- Contraction lemma: if a coalition split into two disjoint parts is decisive, then one
of the two parts is already decisive. -/
lemma decisive_split [Nonempty A] (hU : Unanimity F) (hI : IIA F)
    (h3 : ∀ x y : A, ∃ z, z ≠ x ∧ z ≠ y) (r₀ : Pref A)
    {S₁ S₂ : Set V} (hdisj : Disjoint S₁ S₂) (hD : Decisive F (S₁ ∪ S₂)) :
    Decisive F S₁ ∨ Decisive F S₂ := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc⟩ := exists_three (A := A) h3
  -- members of `S₁` rank `a > b > c`, members of `S₂` rank `c > a > b`,
  -- and everybody else ranks `b > c > a`
  set p : V → Pref A := fun v =>
    if v ∈ S₁ then r₀.twoTop a b else if v ∈ S₂ then r₀.twoTop c a else r₀.twoTop b c with hp
  have hp1 : ∀ v ∈ S₁, p v = r₀.twoTop a b := by intro v hv; simp [hp, hv]
  have hp2 : ∀ v, v ∉ S₁ → v ∈ S₂ → p v = r₀.twoTop c a := by
    intro v h1 h2; simp [hp, h1, h2]
  have hp3 : ∀ v, v ∉ S₁ → v ∉ S₂ → p v = r₀.twoTop b c := by
    intro v h1 h2; simp [hp, h1, h2]
  have hnot : ∀ v ∈ S₂, v ∉ S₁ := fun v hv h1 => (Set.disjoint_left.mp hdisj h1) hv
  have hab' : (F p).better a b := by
    refine hD a b hab p (fun v hv => ?_)
    rcases hv with hv | hv
    · rw [hp1 v hv]; exact r₀.twoTop_better_fst (Ne.symm hab)
    · rw [hp2 v (hnot v hv) hv]
      exact r₀.twoTop_better_snd hac hbc (Ne.symm hab)
  by_cases hcase : (F p).better a c
  · -- then `S₁` is weakly decisive for `(a, c)`
    left
    refine decisive_of_weaklyDecisive hU hI h3 hac ?_
    intro q hq1 hq2
    have hagree : ∀ v, ((p v).pref c a ↔ (q v).pref c a) := by
      intro v
      by_cases hv : v ∈ S₁
      · rw [hp1 v hv]
        constructor
        · intro h; exact absurd h (r₀.twoTop_not_pref_fst (Ne.symm hac))
        · intro h; exact absurd h (hq1 v hv)
      · have hqv : (q v).pref c a := (q v).pref_of_better (hq2 v hv)
        by_cases hv2 : v ∈ S₂
        · rw [hp2 v hv hv2]
          simp only [hqv, iff_true]
          exact (r₀.twoTop c a).pref_of_better (r₀.twoTop_better_fst hac)
        · rw [hp3 v hv hv2]
          simp only [hqv, iff_true]
          exact r₀.twoTop_pref_snd (Ne.symm hbc) hab hac
    exact (iia_better hI p q c a hagree).mp hcase
  · -- otherwise `S₂` is weakly decisive for `(c, b)`
    right
    have hpca : (F p).pref c a := not_not.mp hcase
    have hcb' : (F p).better c b := (F p).better_of_pref_of_better hpca hab'
    refine decisive_of_weaklyDecisive hU hI h3 (Ne.symm hbc) ?_
    intro q hq1 hq2
    have hagree : ∀ v, ((p v).pref b c ↔ (q v).pref b c) := by
      intro v
      by_cases hv2 : v ∈ S₂
      · rw [hp2 v (hnot v hv2) hv2]
        constructor
        · intro h; exact absurd h (r₀.twoTop_not_pref_fst hbc)
        · intro h; exact absurd h (hq1 v hv2)
      · have hqv : (q v).pref b c := (q v).pref_of_better (hq2 v hv2)
        by_cases hv1 : v ∈ S₁
        · rw [hp1 v hv1]
          simp only [hqv, iff_true]
          exact r₀.twoTop_pref_snd (Ne.symm hab) (Ne.symm hac) (Ne.symm hbc)
        · rw [hp3 v hv1 hv2]
          simp only [hqv, iff_true]
          exact (r₀.twoTop b c).pref_of_better (r₀.twoTop_better_fst (Ne.symm hbc))
    exact (iia_better hI p q b c hagree).mp hcb'

/-- Iterating the contraction lemma over a finite electorate produces a decisive singleton. -/
lemma exists_decisive_singleton [Nonempty A] [DecidableEq V] (hU : Unanimity F) (hI : IIA F)
    (h3 : ∀ x y : A, ∃ z, z ≠ x ∧ z ≠ y) (r₀ : Pref A) :
    ∀ S : Finset V, Decisive F (↑S : Set V) → S.Nonempty → ∃ d : V, Decisive F {d} := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hS hne
    obtain ⟨d, hd⟩ := hne
    by_cases hcard : S.erase d = ∅
    · refine ⟨d, ?_⟩
      have hSd : (↑S : Set V) = {d} := by
        ext x
        simp only [Finset.mem_coe, Set.mem_singleton_iff]
        constructor
        · intro hx
          by_contra hxd
          have : x ∈ S.erase d := Finset.mem_erase.mpr ⟨hxd, hx⟩
          rw [hcard] at this
          simp at this
        · rintro rfl; exact hd
      rwa [hSd] at hS
    · have hsplit : (↑S : Set V) = {d} ∪ ↑(S.erase d) := by
        ext x
        simp only [Finset.mem_coe, Set.mem_union, Set.mem_singleton_iff, Finset.mem_erase]
        constructor
        · intro hx
          by_cases h : x = d
          · exact Or.inl h
          · exact Or.inr ⟨h, hx⟩
        · rintro (rfl | ⟨-, hx⟩)
          · exact hd
          · exact hx
      have hdisj : Disjoint ({d} : Set V) (↑(S.erase d) : Set V) := by
        rw [Set.disjoint_singleton_left]
        simp
      rw [hsplit] at hS
      rcases decisive_split hU hI h3 r₀ hdisj hS with h | h
      · exact ⟨d, h⟩
      · exact ih (S.erase d) (Finset.erase_ssubset hd) h (Finset.nonempty_of_ne_empty hcard)

end Proof

section Main

variable {V A : Type*}

/-- If there are at least three alternatives, then for any two of them there is a third. -/
lemma exists_third [Fintype A] (hA : 3 ≤ Fintype.card A) (x y : A) :
    ∃ z, z ≠ x ∧ z ≠ y := by
  classical
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset A) ⊆ {x, y} := by
    intro z _
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases h' : z = x
    · exact Or.inl h'
    · exact Or.inr (hc z h')
  have h₁ := Finset.card_le_card hsub
  have h₂ : ({x, y} : Finset A).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  simp only [Finset.card_univ] at h₁
  omega

/-- **Arrow's theorem** (dictator form): with at least three alternatives and a finite
nonempty electorate, every social welfare function satisfying unanimity and independence
of irrelevant alternatives has a dictator. -/
theorem arrow_dictator [Finite V] [Nonempty V] [Fintype A] (hA : 3 ≤ Fintype.card A)
    (F : (V → Pref A) → Pref A) (hU : Unanimity F) (hI : IIA F) :
    ∃ d : V, IsDictator F d := by
  classical
  have _ : Fintype V := Fintype.ofFinite V
  have hneA : Nonempty A := Fintype.card_pos_iff.mp (by omega)
  have h3 : ∀ x y : A, ∃ z, z ≠ x ∧ z ≠ y := exists_third hA
  let r₀ : Pref A := Pref.ofInjective (Fintype.equivFin A) (Equiv.injective _)
  have huniv : Decisive F (Set.univ : Set V) := by
    intro x y _ p hp
    exact hU p x y (fun v => hp v (Set.mem_univ v))
  obtain ⟨d, hd⟩ := exists_decisive_singleton hU hI h3 r₀ Finset.univ
    (by simpa using huniv) Finset.univ_nonempty
  refine ⟨d, fun p x y hxy => ?_⟩
  refine hd x y ((p d).ne_of_better hxy) p ?_
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  subst hv
  exact hxy

/-- **Arrow's impossibility theorem**: with at least three alternatives and a finite
nonempty electorate, no social welfare function satisfies unanimity, independence of
irrelevant alternatives and non-dictatorship simultaneously. -/
theorem arrow_impossibility [Finite V] [Nonempty V] [Fintype A] (hA : 3 ≤ Fintype.card A)
    (F : (V → Pref A) → Pref A) :
    ¬ (Unanimity F ∧ IIA F ∧ ∀ d : V, ¬ IsDictator F d) := by
  rintro ⟨hU, hI, hnd⟩
  obtain ⟨d, hd⟩ := arrow_dictator hA F hU hI
  exact hnd d hd

/-- Sanity check (non-vacuity): the three conditions are not jointly contradictory in a
trivial way — the dictatorial rule "always copy voter `d`" does satisfy unanimity and
independence of irrelevant alternatives; by the theorem above it must (and does) fail
non-dictatorship. -/
example {V A : Type*} (d : V) :
    Unanimity (fun p : V → Pref A => p d) ∧ IIA (fun p : V → Pref A => p d) ∧
      IsDictator (fun p : V → Pref A => p d) d :=
  ⟨fun _ _ _ h => h d, fun _ _ _ _ h => h d, fun _ _ _ h => h⟩

end Main

end Frontier

