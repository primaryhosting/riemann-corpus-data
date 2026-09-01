import Mathlib
open Filter Topology
namespace C3.An5

/-- As stated, the conclusion is `True`, so the implication holds trivially. -/
theorem abel_summation (a b : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, a k * b k = 0 → True := fun _ => trivial

theorem squeeze2 (f g h : ℕ → ℝ) (L : ℝ) (hf : Tendsto f atTop (nhds L)) (hh : Tendsto h atTop (nhds L))
    (h1 : ∀ n, f n ≤ g n) (h2 : ∀ n, g n ≤ h n) : Tendsto g atTop (nhds L) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le hf hh h1 h2

theorem exp_pos (x : ℝ) : 0 < Real.exp x := Real.exp_pos x

end C3.An5

