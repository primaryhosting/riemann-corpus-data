import Mathlib
open Finset
namespace C3.Prob3

/-- Chebyshev-type inequality: `a²` times the number of indices with `a ≤ |xᵢ|`
is at most the sum of squares. -/
theorem chebyshev_ineq {n : ℕ} (x : Fin n → ℝ) (a : ℝ) (ha : 0 < a) :
    (a^2 * (univ.filter (fun i => a ≤ |x i|)).card : ℝ) ≤ ∑ i, (x i)^2 := by
  classical
  calc (a^2 * ((univ.filter (fun i => a ≤ |x i|)).card : ℝ))
      = ∑ _i ∈ univ.filter (fun i => a ≤ |x i|), a^2 := by
        rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ univ.filter (fun i => a ≤ |x i|), (x i)^2 := by
        refine sum_le_sum ?_
        intro i hi
        have hi' : a ≤ |x i| := (mem_filter.mp hi).2
        calc a^2 ≤ |x i|^2 := by
              gcongr
          _ = (x i)^2 := sq_abs _
    _ ≤ ∑ i, (x i)^2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intro i _ _; positivity)

/-- Cauchy–Schwarz / second moment bound. -/
theorem second_moment {n : ℕ} (x : Fin n → ℝ) : (∑ i, x i)^2 ≤ n * ∑ i, (x i)^2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := x)
  simpa using h

/-- Union bound. -/
theorem union_bound {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (A : Fin n → Finset Ω) :
    (univ.biUnion A).card ≤ ∑ i, (A i).card :=
  card_biUnion_le

end C3.Prob3

