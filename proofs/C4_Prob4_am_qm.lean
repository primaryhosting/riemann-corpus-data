import Mathlib
open Finset
namespace C4.Prob4

/-- AM–QM inequality. The nonnegativity hypothesis `hx` is part of the requested
statement, but it is not needed for the proof. -/
theorem am_qm {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hn : 0 < n) :
    (∑ i, x i)/n ≤ Real.sqrt ((∑ i, (x i)^2)/n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcs : (∑ i, x i) ^ 2 ≤ (n : ℝ) * ∑ i, (x i) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := x)
    simpa using this
  have key : ((∑ i, x i)/n) ^ 2 ≤ (∑ i, (x i)^2)/n := by
    rw [div_pow, div_le_div_iff₀ (by positivity) hn']
    calc (∑ i, x i) ^ 2 * n ≤ ((n : ℝ) * ∑ i, (x i) ^ 2) * n := by
          exact mul_le_mul_of_nonneg_right hcs hn'.le
      _ = (∑ i, (x i) ^ 2) * (n : ℝ) ^ 2 := by ring
  calc (∑ i, x i)/n ≤ |(∑ i, x i)/n| := le_abs_self _
    _ = Real.sqrt (((∑ i, x i)/n) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, (x i)^2)/n) := Real.sqrt_le_sqrt key

theorem sum_sq_zero {n : ℕ} (x : Fin n → ℝ) (h : ∑ i, (x i)^2 = 0) : ∀ i, x i = 0 := by
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => sq_nonneg (x j))).mp h i (Finset.mem_univ i)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

theorem expectation_bound {n : ℕ} (x : Fin n → ℝ) (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (M : ℝ) (hM : ∀ i, x i ≤ M) : ∑ i, p i * x i ≤ M := by
  calc ∑ i, p i * x i ≤ ∑ i, p i * M :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i) (hp i)
    _ = M := by rw [← Finset.sum_mul, hs, one_mul]

end C4.Prob4

