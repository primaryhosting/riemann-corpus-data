import Mathlib
namespace Brockian.MsChebyshevSum
/-- Chebyshev's sum inequality: for similarly-sorted sequences (a monotone, b monotone the same
    way), n·∑ aᵢbᵢ ≥ (∑ aᵢ)(∑ bᵢ). -/
theorem chebyshev_sum {n : ℕ} (a b : Fin n → ℝ) (hmono : Monotone a) (hmono' : Monotone b) :
    (n : ℝ) * ∑ i, a i * b i ≥ (∑ i, a i) * (∑ i, b i) := by
  -- `a` and `b` are both monotone, hence they monovary; apply Chebyshev's sum inequality.
  have h := (hmono.monovary hmono').sum_mul_sum_le_card_mul_sum
  simpa using h
end Brockian.MsChebyshevSum

