import Mathlib
/-!
# Batch 7 — fifth roots of unity ω = exp(2πi/5): the Brockian-five / QFT-on-ℤ5 core. All TRUE.
-/
namespace BrockianQuantum
open Complex
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

theorem om_pow_five : om ^ 5 = 1 := by
  rw [om, ← Complex.exp_nat_mul,
    show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by
      push_cast; ring]
  exact Complex.exp_two_pi_mul_I

theorem om_pow_ten : om ^ 10 = 1 := by
  rw [show (10 : ℕ) = 5 * 2 from rfl, pow_mul, om_pow_five, one_pow]

theorem om_inv_eq : om⁻¹ = om ^ 4 := by
  have h4 : om ^ 4 * om = 1 := by linear_combination om_pow_five
  exact (eq_inv_of_mul_eq_one_left h4).symm

theorem om_norm_one : ‖om‖ = 1 := by
  rw [om, Complex.norm_exp]
  simp

theorem om_conj_eq : (starRingEnd ℂ) om = om ^ 4 := by
  rw [← Complex.inv_eq_conj om_norm_one, om_inv_eq]

theorem om_ne_one : om ≠ 1 := by
  rw [Ne, om, Complex.exp_eq_one_iff]
  push_neg
  intro n h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz : (2 : ℂ) * Real.pi * Complex.I ≠ 0 := by simp [hpi, Complex.I_ne_zero]
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) * (1 / 5)
      = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
    linear_combination h
  have h3 := mul_left_cancel₀ hz h2
  have h5 : (n : ℂ) * 5 = 1 := by linear_combination -5 * h3
  have h5' : (n : ℚ) * 5 = 1 := by exact_mod_cast h5
  have hn : (n : ℚ) = 1 / 5 := by linarith
  have hden : ((n : ℤ) : ℚ).den = 1 := Rat.den_intCast n
  rw [hn] at hden
  norm_num at hden

theorem om_geom_sum : 1 + om + om ^ 2 + om ^ 3 + om ^ 4 = 0 := by
  have hsub : om - 1 ≠ 0 := sub_ne_zero.mpr om_ne_one
  have h : (om - 1) * (1 + om + om ^ 2 + om ^ 3 + om ^ 4) = 0 := by
    linear_combination om_pow_five
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hsub
  · exact h'
end BrockianQuantum

