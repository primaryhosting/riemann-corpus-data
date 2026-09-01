import Mathlib

/-!
# Twist Partial Sum Norm Le
Category: Characters
Target: Brockian.Characters5.twistPartialSum_norm_le
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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character of `ZMod 5` sending `x` to `ω ^ x.val`. -/
noncomputable def e (x : ZMod 5) : ℂ := omega ^ x.val

lemma isPrimitiveRoot_omega : IsPrimitiveRoot omega 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [omega] using h

lemma omega_pow_five : omega ^ 5 = 1 := isPrimitiveRoot_omega.pow_eq_one

lemma norm_omega : ‖omega‖ = 1 := by
  simp [omega, Complex.norm_exp]

lemma norm_e (x : ZMod 5) : ‖e x‖ = 1 := by
  simp [e, norm_pow, norm_omega]

lemma sum_omega_pow : ∑ j ∈ Finset.range 5, omega ^ j = 0 :=
  isPrimitiveRoot_omega.geom_sum_eq_zero (by norm_num)

lemma e_natCast (n : ℕ) : e ((n : ZMod 5)) = omega ^ n := by
  have hv : ((n : ZMod 5)).val = n % 5 := ZMod.val_natCast 5 n
  have : omega ^ n = (omega ^ 5) ^ (n / 5) * omega ^ (n % 5) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [e, hv, this, omega_pow_five, one_pow, one_mul]

/-- The partial sums of the zero-mean twist. -/
noncomputable def twistPartialSum (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, e ((n : ZMod 5))

lemma twistPartialSum_eq (N : ℕ) : twistPartialSum N = ∑ n ∈ Finset.range N, omega ^ n := by
  simp [twistPartialSum, e_natCast]

lemma twistPartialSum_add_five (N : ℕ) : twistPartialSum (N + 5) = twistPartialSum N := by
  rw [twistPartialSum_eq, twistPartialSum_eq, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) (Nat.le_add_right N 5)]
  have : ∑ n ∈ Finset.Ico N (N + 5), omega ^ n = omega ^ N * ∑ j ∈ Finset.range 5, omega ^ j := by
    rw [Finset.mul_sum, Finset.sum_Ico_eq_sum_range]
    simp [pow_add]
  rw [this, sum_omega_pow, mul_zero, add_zero]

lemma twistPartialSum_mod (N : ℕ) : twistPartialSum N = twistPartialSum (N % 5) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 5 with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 5 := ⟨N - 5, by omega⟩
      rw [twistPartialSum_add_five, ih M (by omega), Nat.add_mod_right]

theorem twistPartialSum_norm_le (N : ℕ) : ‖twistPartialSum N‖ ≤ 2 := by
  rw [twistPartialSum_mod]
  have h5 : N % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hsum : (1 : ℂ) + omega + omega ^ 2 + omega ^ 3 + omega ^ 4 = 0 := by
    have := sum_omega_pow
    simp [Finset.sum_range_succ] at this
    linear_combination this
  have hno : ‖omega‖ = 1 := norm_omega
  interval_cases h : N % 5 <;>
    simp only [twistPartialSum_eq, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, pow_zero, pow_one]
  · simp
  · simp
  · calc ‖(1 : ℂ) + omega‖ ≤ ‖(1 : ℂ)‖ + ‖omega‖ := norm_add_le _ _
      _ = 2 := by rw [hno]; norm_num
  · have h3 : (1 : ℂ) + omega + omega ^ 2 = -(omega ^ 3 + omega ^ 4) := by
      linear_combination hsum
    rw [h3, norm_neg]
    calc ‖omega ^ 3 + omega ^ 4‖ ≤ ‖omega ^ 3‖ + ‖omega ^ 4‖ := norm_add_le _ _
      _ = 2 := by rw [norm_pow, norm_pow, hno]; norm_num
  · have h4 : (1 : ℂ) + omega + omega ^ 2 + omega ^ 3 = -(omega ^ 4) := by
      linear_combination hsum
    rw [h4, norm_neg, norm_pow, hno]
    norm_num

end Characters5
end Brockian

