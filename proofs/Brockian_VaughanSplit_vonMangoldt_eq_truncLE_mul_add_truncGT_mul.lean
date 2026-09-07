import Mathlib

open ArithmeticFunction

noncomputable section

namespace Brockian.VaughanSplit

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

theorem vonMangoldt_eq_truncLE_mul_add_truncGT_mul (U : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ)
      = truncLE U (moebius : ArithmeticFunction ℝ) * log
        + truncGT U (moebius : ArithmeticFunction ℝ) * log := by
  rw [← add_mul, truncLE_add_truncGT, moebius_mul_log_eq_vonMangoldt]

end Brockian.VaughanSplit
