/-
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## What is formalised here

Belyi's theorem says that a smooth projective curve is defined over `ℚ̄` if and only if it admits
a map to `ℙ¹` ramified only over `{0, 1, ∞}`.  The substantial half of Belyi's proof is the
*Belyi reduction*: an explicit algorithm which, starting from a map whose branch locus is a finite
set of algebraic points, composes it with suitable polynomials until the branch locus is contained
in `{0, 1, ∞}`.

This file formalises that algorithm over `ℚ`, in the self-contained form of an equivalence
(the statement `Math2.belyi_theorem`):

> a set `S ⊆ ℚ` is finite **iff** there is a non-constant `P ∈ ℚ[X]` which maps `S` into `{0,1}`
> and all of whose finite critical values lie in `{0,1}`.

Viewed as a self-map of `ℙ¹`, such a `P` is unramified outside `{0, 1, ∞}` (a polynomial is
totally ramified over `∞`), i.e. it *is* a Belyi map for `ℙ¹` which moreover kills the prescribed
set `S` of marked points.  The forward direction is the Belyi reduction algorithm (normalise `S`
by an affine map, then repeatedly compose with the Belyi polynomials
`c · x^m (1-x)^n`, each step lowering the number of bad values); the backward direction says that
only finitely many points can be marked this way, since `P⁻¹{0,1}` is finite.
-/

open Polynomial

namespace Math2

/-- A polynomial `P ∈ ℚ[X]` is a *Belyi polynomial* if it is non-constant and all of its finite
critical values lie in `{0, 1}`.  Viewed as a map `ℙ¹ → ℙ¹`, such a `P` is unramified outside
`{0, 1, ∞}`, the point `∞` being totally ramified for every polynomial. -/
def IsBelyiPoly (P : ℚ[X]) : Prop :=
  0 < P.natDegree ∧ ∀ x : ℚ, (derivative P).eval x = 0 → P.eval x = 0 ∨ P.eval x = 1

/-- The classical Belyi polynomial `c · X^(m+1) · (1-X)^(n+1)`, normalised so that its value at
the interior critical point `(m+1)/(m+n+2)` equals `1`. -/
noncomputable def belyiPoly (m n : ℕ) : ℚ[X] :=
  C (((m + n + 2 : ℚ) ^ (m + n + 2)) / ((m + 1 : ℚ) ^ (m + 1) * (n + 1 : ℚ) ^ (n + 1)))
    * X ^ (m + 1) * (1 - X) ^ (n + 1)

/-- The affine polynomial `u * X + v`. -/
noncomputable def affinePoly (u v : ℚ) : ℚ[X] := C u * X + C v

/-! ### Basic tools -/

/-- A polynomial taking two different values is non-constant. -/
lemma natDegree_pos_of_eval_ne {P : ℚ[X]} {x y : ℚ} (h : P.eval x ≠ P.eval y) :
    0 < P.natDegree := by
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | h0
  · exact absurd (by obtain ⟨a, rfl⟩ := natDegree_eq_zero.mp h0; simp) h
  · exact h0

lemma eval_affinePoly (u v x : ℚ) : (affinePoly u v).eval x = u * x + v := by
  simp [affinePoly]

lemma isBelyiPoly_affinePoly {u : ℚ} (hu : u ≠ 0) (v : ℚ) : IsBelyiPoly (affinePoly u v) := by
  constructor
  · exact natDegree_pos_of_eval_ne (x := 0) (y := 1) (by simp [eval_affinePoly, hu])
  · intro x hx
    simp [affinePoly, hu] at hx

/-- Composition of Belyi polynomials: if `Q` is a Belyi polynomial mapping `{0,1}` into `{0,1}`
and `R` is a Belyi polynomial, then `Q ∘ R` is a Belyi polynomial. -/
lemma isBelyiPoly_comp {Q R : ℚ[X]} (hQ : IsBelyiPoly Q) (hR : IsBelyiPoly R)
    (h0 : Q.eval 0 = 0 ∨ Q.eval 0 = 1) (h1 : Q.eval 1 = 0 ∨ Q.eval 1 = 1) :
    IsBelyiPoly (Q.comp R) := by
  refine ⟨?_, ?_⟩
  · rw [natDegree_comp]
    exact Nat.mul_pos hQ.1 hR.1
  · intro x hx
    rw [derivative_comp] at hx
    simp only [eval_mul, eval_comp, mul_eq_zero] at hx
    rw [eval_comp]
    rcases hx with hx | hx
    · rcases hR.2 x hx with h | h <;> rw [h]
      · exact h0
      · exact h1
    · exact hQ.2 _ hx

/-! ### The Belyi polynomials -/

lemma eval_belyiPoly (m n : ℕ) (x : ℚ) :
    (belyiPoly m n).eval x =
      ((m + n + 2 : ℚ) ^ (m + n + 2) / ((m + 1 : ℚ) ^ (m + 1) * (n + 1 : ℚ) ^ (n + 1)))
        * x ^ (m + 1) * (1 - x) ^ (n + 1) := by
  simp [belyiPoly]

lemma belyiPoly_const_ne_zero (m n : ℕ) :
    ((m + n + 2 : ℚ) ^ (m + n + 2) / ((m + 1 : ℚ) ^ (m + 1) * (n + 1 : ℚ) ^ (n + 1))) ≠ 0 := by
  have h1 : ((m : ℚ) + n + 2) ^ (m + n + 2) ≠ 0 := by positivity
  have h2 : ((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1) ≠ 0 := by positivity
  exact div_ne_zero h1 h2

lemma eval_belyiPoly_zero (m n : ℕ) : (belyiPoly m n).eval 0 = 0 := by
  simp [eval_belyiPoly]

lemma eval_belyiPoly_one (m n : ℕ) : (belyiPoly m n).eval 1 = 0 := by
  simp [eval_belyiPoly]

lemma eval_belyiPoly_crit (m n : ℕ) :
    (belyiPoly m n).eval ((m + 1 : ℚ) / (m + n + 2)) = 1 := by
  rw [eval_belyiPoly]
  have h1 : (1 : ℚ) - (m + 1 : ℚ) / (m + n + 2) = (n + 1) / (m + n + 2) := by
    have hM : (m + n + 2 : ℚ) ≠ 0 := by positivity
    field_simp; ring
  have hm : ((m : ℚ) + 1) ^ (m + 1) ≠ 0 := by positivity
  have hn : ((n : ℚ) + 1) ^ (n + 1) ≠ 0 := by positivity
  have hM : (m + n + 2 : ℚ) ≠ 0 := by positivity
  rw [h1, div_pow, div_pow]
  field_simp
  rw [← pow_add]
  congr 1
  omega

lemma eval_derivative_belyiPoly (m n : ℕ) (x : ℚ) :
    (derivative (belyiPoly m n)).eval x =
      ((m + n + 2 : ℚ) ^ (m + n + 2) / ((m + 1 : ℚ) ^ (m + 1) * (n + 1 : ℚ) ^ (n + 1)))
        * x ^ m * (1 - x) ^ n * ((m + 1 : ℚ) - (m + n + 2 : ℚ) * x) := by
  simp only [belyiPoly, derivative_mul, derivative_pow, derivative_X, derivative_C,
    derivative_sub, derivative_one, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_sub,
    eval_one, eval_zero, zero_mul, zero_add, mul_one, Nat.add_sub_cancel]
  push_cast
  ring

/-- The Belyi polynomials are Belyi polynomials: their finite critical values are `0` and `1`. -/
lemma isBelyiPoly_belyiPoly (m n : ℕ) : IsBelyiPoly (belyiPoly m n) := by
  have hc := belyiPoly_const_ne_zero m n
  refine ⟨natDegree_pos_of_eval_ne (x := 0) (y := (m + 1 : ℚ) / (m + n + 2)) ?_, ?_⟩
  · rw [eval_belyiPoly_zero, eval_belyiPoly_crit]
    exact zero_ne_one
  · intro x hx
    rw [eval_derivative_belyiPoly] at hx
    have hM : (m + n + 2 : ℚ) ≠ 0 := by positivity
    rcases mul_eq_zero.mp hx with hx' | hx'
    · rcases mul_eq_zero.mp hx' with hx'' | hx''
      · rcases mul_eq_zero.mp hx'' with h | h
        · exact absurd h hc
        · -- `x ^ m = 0` forces `x = 0`
          have hx0 : x = 0 := pow_eq_zero_iff'.mp h |>.1
          subst hx0
          left; exact eval_belyiPoly_zero m n
      · have hx1 : (1 : ℚ) - x = 0 := pow_eq_zero_iff'.mp hx'' |>.1
        have : x = 1 := by linarith
        subst this
        left; exact eval_belyiPoly_one m n
    · have : x = (m + 1 : ℚ) / (m + n + 2) := by
        field_simp
        linarith
      subst this
      right; exact eval_belyiPoly_crit m n

/-! ### The Belyi reduction algorithm -/

/-- Every rational number strictly between `0` and `1` is of the form `(m+1)/(m+n+2)`. -/
lemma exists_repr_of_mem_Ioo {l : ℚ} (h0 : 0 < l) (h1 : l < 1) :
    ∃ m n : ℕ, l = (m + 1 : ℚ) / (m + n + 2) := by
  set p : ℕ := l.num.toNat with hp
  have hnum : (0 : ℤ) < l.num := Rat.num_pos.mpr h0
  have hpnum : (p : ℤ) = l.num := Int.toNat_of_nonneg hnum.le
  have hplt : p < l.den := by
    have hden : (0 : ℚ) < (l.den : ℚ) := by exact_mod_cast l.pos
    have hkey : (l.num : ℚ) = l * (l.den : ℚ) := (Rat.mul_den_eq_num l).symm
    have hlt : (l.num : ℚ) < (l.den : ℚ) := by rw [hkey]; nlinarith
    have : l.num < (l.den : ℤ) := by exact_mod_cast hlt
    omega
  have hppos : 0 < p := by omega
  refine ⟨p - 1, l.den - p - 1, ?_⟩
  have e1 : ((p - 1 : ℕ) : ℚ) + 1 = (p : ℚ) := by
    have key : (p - 1) + 1 = p := by omega
    exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) key
  have e2 : ((p - 1 : ℕ) : ℚ) + ((l.den - p - 1 : ℕ) : ℚ) + 2 = (l.den : ℚ) := by
    have key : (p - 1) + (l.den - p - 1) + 2 = l.den := by omega
    exact_mod_cast congrArg (fun k : ℕ => (k : ℚ)) key
  rw [e1, e2]
  rw [show ((p : ℚ)) = ((l.num : ℚ)) by exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hpnum]
  exact (Rat.num_div_den l).symm

/-- **Belyi reduction over `ℚ`.**  For every finite set `S` of rational numbers there is a Belyi
polynomial mapping `S` into `{0, 1}`. -/
lemma exists_isBelyiPoly (S : Finset ℚ) :
    ∃ P : ℚ[X], IsBelyiPoly P ∧ ∀ s ∈ S, P.eval s = 0 ∨ P.eval s = 1 := by
  classical
  generalize hk : S.card = k
  induction k using Nat.strong_induction_on generalizing S with
  | _ k IH =>
    subst hk
    by_cases hcard : S.card ≤ 1
    · rcases S.eq_empty_or_nonempty with rfl | hne
      · exact ⟨X, ⟨by simp, by intro x hx; simp at hx⟩, by simp⟩
      · obtain ⟨a, ha⟩ := hne
        refine ⟨X - C a, ⟨by simp, ?_⟩, ?_⟩
        · intro x hx; simp at hx
        · intro s hs
          have : s = a := Finset.card_le_one.mp hcard s hs a ha
          subst this
          left; simp
    · push_neg at hcard
      have h2 : 2 ≤ S.card := hcard
      have hne : S.Nonempty := Finset.card_pos.mp (by omega)
      set a := S.min' hne with hadef
      set b := S.max' hne with hbdef
      have hab : a < b := S.min'_lt_max'_of_card (by omega)
      have hba : (0 : ℚ) < b - a := by linarith
      set A : ℚ[X] := affinePoly (1 / (b - a)) (-a / (b - a)) with hAdef
      have hAeval : ∀ x : ℚ, A.eval x = (x - a) / (b - a) := by
        intro x
        rw [hAdef, eval_affinePoly]
        field_simp
        ring
      have hA : IsBelyiPoly A := isBelyiPoly_affinePoly (by positivity) _
      set T : Finset ℚ := S.image (fun s => A.eval s) with hTdef
      have hTbounds : ∀ t ∈ T, 0 ≤ t ∧ t ≤ 1 := by
        intro t ht
        rw [hTdef, Finset.mem_image] at ht
        obtain ⟨s, hs, rfl⟩ := ht
        have h1 : a ≤ s := S.min'_le s hs
        have h2 : s ≤ b := S.le_max' s hs
        rw [hAeval]
        constructor
        · exact div_nonneg (by linarith) hba.le
        · rw [div_le_one hba]; linarith
      have h0T : (0 : ℚ) ∈ T := by
        rw [hTdef, Finset.mem_image]
        exact ⟨a, S.min'_mem hne, by rw [hAeval]; simp⟩
      have h1T : (1 : ℚ) ∈ T := by
        rw [hTdef, Finset.mem_image]
        refine ⟨b, S.max'_mem hne, ?_⟩
        rw [hAeval]
        field_simp
      have hcardT : T.card = S.card := by
        rw [hTdef]
        refine Finset.card_image_of_injective _ ?_
        intro x y hxy
        have hxy' : (x - a) / (b - a) = (y - a) / (b - a) := by
          rw [← hAeval, ← hAeval]; exact hxy
        have hne' : b - a ≠ 0 := ne_of_gt hba
        field_simp at hxy'
        linarith
      by_cases hT2 : T.card ≤ 2
      · -- `T = {0,1}` : the affine map already works
        have hsub : ({0, 1} : Finset ℚ) ⊆ T := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact h0T
          · exact h1T
        have hTeq : T = ({0, 1} : Finset ℚ) :=
          (Finset.eq_of_subset_of_card_le hsub (by simpa using hT2)).symm
        refine ⟨A, hA, ?_⟩
        intro s hs
        have : A.eval s ∈ T := by rw [hTdef]; exact Finset.mem_image_of_mem _ hs
        rw [hTeq] at this
        simpa using this
      · push_neg at hT2
        -- there is a third value `l`, strictly between `0` and `1`
        obtain ⟨l, hlT, hl0, hl1⟩ : ∃ l ∈ T, l ≠ 0 ∧ l ≠ 1 := by
          by_contra hcon
          push_neg at hcon
          have : T ⊆ ({0, 1} : Finset ℚ) := by
            intro x hx
            rcases eq_or_ne x 0 with rfl | hx0
            · simp
            · have := hcon x hx hx0
              simp [this]
          have hle := Finset.card_le_card this
          have hc2 : ({0, 1} : Finset ℚ).card ≤ 2 := by
            simp
          omega
        obtain ⟨hl0', hl1'⟩ := hTbounds l hlT
        have hlpos : 0 < l := lt_of_le_of_ne hl0' (Ne.symm hl0)
        have hllt : l < 1 := lt_of_le_of_ne hl1' hl1
        obtain ⟨m, n, hmn⟩ := exists_repr_of_mem_Ioo hlpos hllt
        set B : ℚ[X] := belyiPoly m n with hBdef
        have hB : IsBelyiPoly B := isBelyiPoly_belyiPoly m n
        set T' : Finset ℚ := T.image (fun t => B.eval t) with hT'def
        have hB0 : B.eval 0 = 0 := eval_belyiPoly_zero m n
        have hB1 : B.eval 1 = 0 := eval_belyiPoly_one m n
        have hBl : B.eval l = 1 := by rw [hmn]; exact eval_belyiPoly_crit m n
        -- the image is strictly smaller since `0` and `1` are identified
        have hcardT' : T'.card < T.card := by
          have hsub : T' ⊆ (T.erase 1).image (fun t => B.eval t) := by
            intro y hy
            rw [hT'def, Finset.mem_image] at hy
            obtain ⟨t, ht, rfl⟩ := hy
            rcases eq_or_ne t 1 with rfl | ht1
            · refine Finset.mem_image.mpr ⟨0, ?_, ?_⟩
              · exact Finset.mem_erase.mpr ⟨zero_ne_one, h0T⟩
              · rw [hB0, hB1]
            · exact Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨ht1, ht⟩)
          have h1 : T'.card ≤ (T.erase 1).card :=
            le_trans (Finset.card_le_card hsub) (Finset.card_image_le)
          have h2 : (T.erase 1).card = T.card - 1 := Finset.card_erase_of_mem h1T
          have : 0 < T.card := Finset.card_pos.mpr ⟨1, h1T⟩
          omega
        have h0T' : (0 : ℚ) ∈ T' := by
          rw [hT'def, Finset.mem_image]
          exact ⟨0, h0T, hB0⟩
        have h1T' : (1 : ℚ) ∈ T' := by
          rw [hT'def, Finset.mem_image]
          exact ⟨l, hlT, hBl⟩
        obtain ⟨Q, hQ, hQval⟩ := IH T'.card (by omega) T' rfl
        refine ⟨Q.comp (B.comp A), ?_, ?_⟩
        · refine isBelyiPoly_comp hQ (isBelyiPoly_comp hB hA ?_ ?_) (hQval 0 h0T') (hQval 1 h1T')
          · left; exact hB0
          · left; exact hB1
        · intro s hs
          have hAs : A.eval s ∈ T := by rw [hTdef]; exact Finset.mem_image_of_mem _ hs
          have hBs : B.eval (A.eval s) ∈ T' := by
            rw [hT'def]; exact Finset.mem_image_of_mem _ hAs
          simpa [eval_comp] using hQval _ hBs

/-! ### The main theorem -/

/-- **Belyi's theorem (rational branch points, `ℙ¹` case).**

A set `S ⊆ ℚ` of marked points is finite — i.e. is cut out by algebraic data over `ℚ` — if and
only if there is a Belyi map for `ℙ¹` killing it: a non-constant polynomial `P ∈ ℚ[X]` sending
every point of `S` into `{0, 1}` and having all of its finite critical values in `{0, 1}`.  Such a
`P`, viewed as a self-map of `ℙ¹`, is ramified only over `{0, 1, ∞}`.

The forward implication is Belyi's reduction algorithm (`Math2.exists_isBelyiPoly`); the reverse
implication holds because the fibre `P⁻¹{0,1}` of a non-constant polynomial is finite. -/
theorem belyi_theorem (S : Set ℚ) :
    S.Finite ↔ ∃ P : ℚ[X], IsBelyiPoly P ∧ ∀ s ∈ S, P.eval s = 0 ∨ P.eval s = 1 := by
  constructor
  · intro hS
    obtain ⟨P, hP, hPval⟩ := exists_isBelyiPoly hS.toFinset
    exact ⟨P, hP, fun s hs => hPval s (by simpa using hs)⟩
  · rintro ⟨P, hP, hPval⟩
    have hP0 : P ≠ 0 := by
      intro h
      have hd := hP.1
      rw [h] at hd
      simp at hd
    have hP1 : P - 1 ≠ 0 := by
      intro h
      have hd := hP.1
      have hPeq : P = 1 := by linear_combination (norm := ring_nf) h
      rw [hPeq] at hd
      simp at hd
    have hfin : ({x : ℚ | P.IsRoot x} ∪ {x : ℚ | (P - 1).IsRoot x}).Finite :=
      (Polynomial.finite_setOf_isRoot hP0).union (Polynomial.finite_setOf_isRoot hP1)
    refine hfin.subset ?_
    intro s hs
    rcases hPval s hs with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      show (P - 1).IsRoot s
      simp [IsRoot.def, h]

end Math2

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

