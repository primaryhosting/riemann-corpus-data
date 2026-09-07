import Mathlib

/-!
# Brockian.Characters5

Additive-character theory of `ZMod 5` / the five-ray Brockian wheel.

Assembled from individually AXLE-verified Aristotle proof files
(`aristotle/best_proofs/Brockian_Characters5_*.lean`).  Shared definitions
(`omega`, `e`, `dft`, `rayIndicator`, `raySum`) are declared once; each
distinct theorem is the best proof selected from the source attempts, with the
original statement preserved verbatim.

Provenance: Aristotle theorem prover (Harmonic).
-/

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

set_option grind.warning false

namespace Brockian.Characters5

/-! ## Shared definitions -/

/-- The primitive fifth root of unity `ω = exp (2πi/5)`, the Brockian ray rotation. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

local notation "ω" => omega

/-- The bespoke additive character `e : ZMod 5 → ℂ`, `e k = ω ^ k.val`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The (unnormalized) discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (-(a * x))

/-- Indicator of the ray `n ≡ r (mod 5)`. -/
noncomputable def rayIndicator (r : ZMod 5) (n : ℕ) : ℂ := if (n : ZMod 5) = r then 1 else 0

/-- The number of elements of a finite set `S` of naturals lying on the ray `r` mod `5`. -/
def raySum (S : Finset ℕ) (r : ZMod 5) : ℕ := (S.filter fun n : ℕ => ((n : ZMod 5) = r)).card

/-! ## Root-of-unity facts -/

/-- `ω` is a primitive fifth root of unity. -/
theorem isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using this

/-- The Brockian ray rotation returns to start after five steps: `ω ^ 5 = 1`. -/
theorem omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

/-- The sum of all five 5th roots of unity vanishes. -/
theorem sum_omega_pow : ∑ k ∈ Finset.range 5, omega ^ k = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

/-- `ω` has unit modulus. -/
theorem norm_omega : ‖omega‖ = 1 := by
  simp [omega, Complex.norm_exp]

/-! ## Character basics -/

/-- The additive character has unit modulus: `‖e k‖ = 1` for every `k : ZMod 5`. -/
theorem norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  simp [e, norm_pow, norm_omega]

theorem e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  rw [e, e, e, ← pow_add]
  have hval : (j + k).val = (j.val + k.val) % 5 := by
    rw [ZMod.val_add]
  rw [hval]
  conv_rhs => rw [← Nat.div_add_mod (j.val + k.val) 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

/-- The bespoke character equals Mathlib's standard additive character mod `5`. -/
theorem e_eq_stdAddChar (k : ZMod 5) : e k = ZMod.stdAddChar (N := 5) k := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, e, omega, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma e_zero : e 0 = 1 := by simp [e]

lemma conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have h1 : e k * e (-k) = 1 := by rw [← e_add]; simp [e_zero]
  have h2 : (e k)⁻¹ = (starRingEnd ℂ) (e k) := Complex.inv_eq_conj (norm_e k)
  rw [← h2]
  exact inv_eq_of_mul_eq_one_right h1

/-- The character sum of `e` over `ZMod 5` vanishes. -/
theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  have h : ∑ x : ZMod 5, e x = ∑ k ∈ Finset.range 5, omega ^ k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => omega ^ k) 5]
    rfl
  rw [h, sum_omega_pow]

/-- Additive-character orthogonality on `ZMod 5`. -/
theorem sum_e_mul (a : ZMod 5) : ∑ x : ZMod 5, e (a * x) = if a = 0 then 5 else 0 := by
  by_cases ha : a = 0
  · subst ha
    simp [e, ZMod.val_zero]
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [if_neg ha]
    rw [← sum_e]
    exact Fintype.sum_equiv (Equiv.mulLeft₀ a ha) _ _ (fun x => rfl)

/-! ## Parseval / Plancherel -/

/-- The complex-valued core Parseval identity. -/
lemma parseval_core (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = 5 * ∑ x : ZMod 5, f x * (starRingEnd ℂ) (f x) := by
  have hexp : ∀ a : ZMod 5, dft f a * (starRingEnd ℂ) (dft f a)
      = ∑ x : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (y - x)) := by
    intro a
    rw [dft, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    have key : e (-(a * x)) * e (- -(a * y)) = e (a * (y - x)) := by
      rw [← e_add]; congr 1; ring
    rw [map_mul, conj_e]
    linear_combination (f x * (starRingEnd ℂ) (f y)) * key
  rw [Finset.sum_congr rfl (fun a _ => hexp a)]
  rw [Finset.sum_comm]
  have : ∀ x : ZMod 5, ∑ a : ZMod 5, ∑ y : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (y - x))
      = 5 * (f x * (starRingEnd ℂ) (f x)) := by
    intro x
    rw [Finset.sum_comm]
    have hin : ∀ y : ZMod 5, ∑ a : ZMod 5, f x * (starRingEnd ℂ) (f y) * e (a * (y - x))
        = if y = x then 5 * (f x * (starRingEnd ℂ) (f y)) else 0 := by
      intro y
      rw [← Finset.mul_sum]
      have : ∑ a : ZMod 5, e (a * (y - x)) = if y - x = 0 then 5 else 0 := by
        rw [← sum_e_mul (y - x)]
        exact Finset.sum_congr rfl (fun a _ => by rw [mul_comm])
      rw [this]
      by_cases h : y = x
      · subst h; simp [mul_comm]
      · have : y - x ≠ 0 := sub_ne_zero_of_ne h
        simp [this, h]
    rw [Finset.sum_congr rfl (fun y _ => hin y), Finset.sum_ite_eq' Finset.univ x]
    simp
  rw [Finset.sum_congr rfl (fun x _ => this x), ← Finset.mul_sum]

/-- Parseval/Plancherel on `ZMod 5` for the unnormalized transform. -/
theorem parseval (f : ZMod 5 → ℂ) :
    ∑ a : ZMod 5, ‖dft f a‖ ^ 2 = 5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 := by
  have h := parseval_core f
  simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  have h2 : ((∑ a : ZMod 5, ‖dft f a‖ ^ 2 : ℝ) : ℂ) = ((5 * ∑ x : ZMod 5, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    push_cast at h
    exact h
  exact_mod_cast h2

/-! ## Ray counting -/

theorem rayIndicator_eq_charSum (r : ZMod 5) (n : ℕ) :
    rayIndicator r n = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * ((n : ZMod 5) - r)) := by
  set b : ZMod 5 := (n : ZMod 5) - r with hbdef
  have hsum : ∑ a : ZMod 5, e (a * b) = ∑ a : ZMod 5, e (b * a) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [mul_comm]
  rw [hsum, sum_e_mul, rayIndicator]
  have hiff : b = 0 ↔ (n : ZMod 5) = r := by
    rw [hbdef, sub_eq_zero]
  by_cases h : (n : ZMod 5) = r
  · rw [if_pos h, if_pos (hiff.mpr h)]
    norm_num
  · rw [if_neg h, if_neg (fun hc => h (hiff.mp hc))]
    norm_num

/-- Orthogonality with the summation index in the first factor. -/
lemma charSum_eq (x : ZMod 5) :
    ∑ a : ZMod 5, e (a * x) = if x = 0 then (5 : ℂ) else 0 := by
  have h : ∑ a : ZMod 5, e (a * x) = ∑ a : ZMod 5, e (x * a) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rw [mul_comm]
  rw [h, sum_e_mul]

/-- The indicator of the ray through `r` (both arguments in `ZMod 5`), as a character sum. -/
lemma rayIndicator_zmod_eq_charSum (n r : ZMod 5) :
    (if n = r then (1 : ℂ) else 0) = (1 / 5 : ℂ) * ∑ a : ZMod 5, e (a * (n - r)) := by
  rw [charSum_eq]
  by_cases h : n = r
  · simp [h]
  · simp [h, sub_ne_zero_of_ne h]

/-- Ray-count identity: the number of elements of `S` on the ray `r` mod `5` equals
`(1/5) ∑_{a : ZMod 5} ∑_{n ∈ S} e (a * (n - r))`. -/
theorem raySum_eq_charSum (S : Finset ℕ) (r : ZMod 5) :
    ((raySum S r : ℕ) : ℂ) = (1 / 5 : ℂ) * ∑ a : ZMod 5, ∑ n ∈ S, e (a * ((n : ZMod 5) - r)) := by
  rw [raySum, Finset.card_filter]
  push_cast
  rw [Finset.sum_comm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => rayIndicator_zmod_eq_charSum (n : ZMod 5) r

/-! ## Dirichlet-character orthogonality -/

/-- Orthogonality for a nontrivial Dirichlet character mod 5 with values in ℂ:
the sum of its values over `ZMod 5` vanishes. -/
theorem dirichlet_sum_eq_zero (χ : DirichletCharacter ℂ 5) (hχ : χ ≠ 1) :
    ∑ x : ZMod 5, χ x = 0 :=
  MulChar.sum_eq_zero_of_ne_one hχ

end Brockian.Characters5
