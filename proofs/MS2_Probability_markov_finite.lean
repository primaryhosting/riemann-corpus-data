import Mathlib
open Finset
namespace MS2.Probability
/-- Finite Markov inequality. The hypothesis `0 < a` is kept as stated, although the
proof does not need it (nonnegativity of `x` alone suffices). -/
theorem markov_finite {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (a : ℝ) (ha : 0 < a) :
    (a * (univ.filter (fun i => a ≤ x i)).card : ℝ) ≤ ∑ i, x i := by
  calc (a * (univ.filter (fun i => a ≤ x i)).card : ℝ)
      = ∑ _i ∈ univ.filter (fun i => a ≤ x i), a := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ univ.filter (fun i => a ≤ x i), x i :=
        Finset.sum_le_sum (fun i hi => (Finset.mem_filter.mp hi).2)
    _ ≤ ∑ i, x i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => hx i)

theorem boole_inequality {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (A : Fin n → Finset Ω) :
    (Finset.univ.biUnion A).card ≤ ∑ i, (A i).card :=
  Finset.card_biUnion_le

theorem linearity_expectation {n : ℕ} (x y : Fin n → ℝ) (p : Fin n → ℝ) :
    ∑ i, p i * (x i + y i) = (∑ i, p i * x i) + (∑ i, p i * y i) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => mul_add _ _ _)

theorem cauchy_schwarz_expect {n : ℕ} (x y : Fin n → ℝ) :
    (∑ i, x i * y i)^2 ≤ (∑ i, (x i)^2) * (∑ i, (y i)^2) :=
  Finset.sum_mul_sq_le_sq_mul_sq _ x y

theorem chebyshev_sum {n : ℕ} (x : Fin n → ℝ) (a : ℝ) (ha : 0 < a) :
    (a^2 * (univ.filter (fun i => a ≤ |x i|)).card : ℝ) ≤ ∑ i, (x i)^2 := by
  calc (a^2 * (univ.filter (fun i => a ≤ |x i|)).card : ℝ)
      = ∑ _i ∈ univ.filter (fun i => a ≤ |x i|), a^2 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i ∈ univ.filter (fun i => a ≤ |x i|), (x i)^2 := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        have h := (Finset.mem_filter.mp hi).2
        calc a ^ 2 ≤ |x i| ^ 2 := by
              exact pow_le_pow_left₀ ha.le h 2
          _ = (x i) ^ 2 := sq_abs _
    _ ≤ ∑ i, (x i)^2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => sq_nonneg _)
end MS2.Probability

