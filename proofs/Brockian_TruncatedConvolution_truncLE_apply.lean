import Mathlib

open ArithmeticFunction

noncomputable section

namespace Brockian.TruncatedConvolution

def truncLE (U : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ U then f n else 0
  map_zero' := by simp

@[simp] theorem truncLE_apply (U : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    (truncLE U f) n = if n ≤ U then f n else 0 := rfl

theorem truncLE_mul_apply (U : ℕ) (f g : ArithmeticFunction ℝ) (n : ℕ) :
    ((truncLE U f) * g) n
      = ∑ d ∈ n.divisors.filter (fun d => d ≤ U), f d * g (n / d) := by
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal (f := fun a b => (truncLE U f) a * g b)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [truncLE_apply]
  rw [ite_mul, zero_mul]

end Brockian.TruncatedConvolution
