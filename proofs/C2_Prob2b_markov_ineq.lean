import Mathlib
open Finset
namespace C2.Prob2b

/-- Markov's inequality (counting form): for nonnegative reals `x i`,
`a` times the number of indices with `a ≤ x i` is at most `∑ i, x i`.
The hypothesis `0 < a` turns out to be unnecessary for the proof. -/
theorem markov_ineq {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (a : ℝ) (ha : 0 < a) :
    (a * ((univ.filter (fun i => a ≤ x i)).card) : ℝ) ≤ ∑ i, x i := by
  classical
  have h1 : (a * ((univ.filter (fun i => a ≤ x i)).card) : ℝ)
      = ∑ _i ∈ univ.filter (fun i => a ≤ x i), a := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [h1]
  calc ∑ _i ∈ univ.filter (fun i => a ≤ x i), a
      ≤ ∑ i ∈ univ.filter (fun i => a ≤ x i), x i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        simpa using (Finset.mem_filter.mp hi).2
    _ ≤ ∑ i, x i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => hx i)

/-- Jensen's inequality for a finite average: a convex function of the mean is at most
the mean of the values. -/
theorem jensen_sum {n : ℕ} (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) (x : Fin n → ℝ) (hn : 0 < n) :
    f ((∑ i, x i)/n) ≤ (∑ i, f (x i))/n := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have := hf.map_sum_le (t := (univ : Finset (Fin n))) (w := fun _ => (n : ℝ)⁻¹) (p := x)
    (fun i _ => by positivity) (by simp [Finset.card_univ]; field_simp) (fun i _ => Set.mem_univ _)
  simpa [smul_eq_mul, ← Finset.mul_sum, div_eq_inv_mul] using this

/-- The variance of a finite family of reals is nonnegative (Cauchy–Schwarz / Chebyshev). -/
theorem variance_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ (∑ i, (x i)^2)/n - ((∑ i, x i)/n)^2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn : (0:ℝ) < n := by exact_mod_cast h
  rw [sub_nonneg, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin n))) (f := x)
  simp only [Finset.card_univ, Fintype.card_fin] at this
  nlinarith [this]

end C2.Prob2b

