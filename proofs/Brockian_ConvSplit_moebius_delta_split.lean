import Mathlib

open ArithmeticFunction
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

noncomputable section

namespace Brockian.ConvSplit

def truncLE (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ U then f n else 0
  map_zero' := by simp

def truncGT (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if U < n then f n else 0
  map_zero' := by simp

theorem truncLE_add_truncGT (U : ℕ) (f : ArithmeticFunction ℝ) :
    truncLE U f + truncGT U f = f := by
  ext n
  simp only [truncLE, truncGT, ArithmeticFunction.add_apply, ArithmeticFunction.coe_mk]
  by_cases h : n ≤ U
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]

-- THE PRIZE: fully general, reusable for every Vaughan term
theorem truncLE_mul_add_truncGT_mul (U : ℕ) (f g : ArithmeticFunction ℝ) :
    truncLE U f * g + truncGT U f * g = f * g := by
  rw [← add_mul, truncLE_add_truncGT]

-- Corollary A: re-derives the von Mangoldt split (needs moebius_mul_log_eq_vonMangoldt)
theorem vonMangoldt_split (U : ℕ) :
    truncLE U (moebius : ArithmeticFunction ℝ) * log
      + truncGT U (moebius : ArithmeticFunction ℝ) * log
      = vonMangoldt := by
  rw [truncLE_mul_add_truncGT_mul, moebius_mul_log_eq_vonMangoldt]

-- Corollary B: the Möbius/δ split, IF μ * ζ = 1 is available.
theorem moebius_delta_split (U : ℕ) :
    truncLE U (moebius : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)
      + truncGT U (moebius : ArithmeticFunction ℝ) * (ζ : ArithmeticFunction ℝ)
      = 1 := by
  rw [truncLE_mul_add_truncGT_mul]
  exact coe_moebius_mul_coe_zeta

end Brockian.ConvSplit
