import Mathlib

/-!
# Parseval
Category: Characters
Target: Brockian.Characters5.parseval
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

/-- The primitive fifth root of unity `exp (2πi/5)`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e k = ω ^ k` on `ZMod 5`. -/
noncomputable def e (k : ZMod 5) : ℂ := omega ^ k.val

/-- The (unnormalized) discrete Fourier transform on `ZMod 5`. -/
noncomputable def dft (f : ZMod 5 → ℂ) (a : ZMod 5) : ℂ := ∑ x : ZMod 5, f x * e (-(a * x))

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using this

lemma omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

lemma omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_add (k l : ZMod 5) : e (k + l) = e k * e l := by
  simp only [e, ZMod.val_add, omega_pow_mod, pow_add]

lemma norm_omega : ‖omega‖ = 1 := by
  simp [omega, Complex.norm_exp]

lemma norm_e (k : ZMod 5) : ‖e k‖ = 1 := by
  simp [e, norm_pow, norm_omega]

lemma conj_e (k : ZMod 5) : (starRingEnd ℂ) (e k) = e (-k) := by
  have h1 : e k * e (-k) = 1 := by rw [← e_add]; simp [e_zero]
  have h2 : (e k)⁻¹ = (starRingEnd ℂ) (e k) := Complex.inv_eq_conj (norm_e k)
  rw [← h2]
  exact inv_eq_of_mul_eq_one_right h1

/-- Orthogonality of characters on `ZMod 5`. -/
lemma sum_e_mul (k : ZMod 5) : ∑ x : ZMod 5, e (k * x) = if k = 0 then 5 else 0 := by
  have hval : ∀ x : ZMod 5, e (k * x) = (e k) ^ x.val := by
    intro x
    simp only [e, ← pow_mul]
    rw [ZMod.val_mul, omega_pow_mod]
  rw [Finset.sum_congr rfl (fun x _ => hval x)]
  have hrange : ∑ x : ZMod 5, (e k) ^ x.val = ∑ j ∈ Finset.range 5, (e k) ^ j :=
    Fin.sum_univ_eq_sum_range (fun j => (e k) ^ j) 5
  rw [hrange]
  by_cases hk : k = 0
  · subst hk
    simp [e_zero]
  · have hne : e k ≠ 1 := by
      intro h
      apply hk
      have : omega ^ k.val = 1 := h
      have hdvd : (5 : ℕ) ∣ k.val := (isPrimitiveRoot_omega.pow_eq_one_iff_dvd k.val).1 this
      have hlt : k.val < 5 := ZMod.val_lt k
      have hz : k.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
      exact (ZMod.val_eq_zero k).1 hz
    have hpow : (e k) ^ 5 = 1 := by
      simp only [e, ← pow_mul, mul_comm]
      rw [pow_mul, omega_pow_five, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]
    simp [hk]

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

end Brockian.Characters5

