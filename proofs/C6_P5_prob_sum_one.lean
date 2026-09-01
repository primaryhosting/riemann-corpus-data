import Mathlib
open Finset
namespace C6.P5
theorem prob_sum_one {n : ℕ} (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : ∀ i, p i ≤ 1 := by
  intro i
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)

theorem var_expand {n : ℕ} (x : Fin n → ℝ) (m : ℝ) :
    ∑ i, (x i - m)^2 = (∑ i, (x i)^2) - 2*m*(∑ i, x i) + n*m^2 := by
  have h : ∀ i, (x i - m)^2 = (x i)^2 - (2*m) * x i + m^2 := fun i => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem nonneg_expectation {n : ℕ} (x p : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hp : ∀ i, 0 ≤ p i) :
    0 ≤ ∑ i, p i * x i :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (hx i)
end C6.P5

