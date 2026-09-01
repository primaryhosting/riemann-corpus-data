import Mathlib
open Finset
namespace MS.Inequalities
theorem cauchy_schwarz {n : ℕ} (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, (a i) ^ 2) * (∑ i, (b i) ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq _ a b

theorem am_gm_n {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (hn : 0 < n) :
    (∏ i, a i) ^ ((1 : ℝ) / n) ≤ (∑ i, a i) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => 1 / n) a
    (fun i _ => by positivity) (by simp [Finset.card_univ]; field_simp) (fun i _ => ha i)
  rw [Real.finset_prod_rpow _ _ (fun i _ => ha i)] at key
  refine key.trans_eq ?_
  simp only
  rw [← Finset.mul_sum]
  ring

theorem jensen_convex (f : ℝ → ℝ) (hf : ConvexOn ℝ Set.univ f) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) : f ((∑ i, x i) / n) ≤ (∑ i, f (x i)) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key := hf.map_sum_le (t := Finset.univ) (w := fun _ : Fin n => 1 / (n : ℝ)) (p := x)
    (fun i _ => by positivity) (by simp [Finset.card_univ]; field_simp) (fun i _ => Set.mem_univ _)
  simp only [smul_eq_mul, ← Finset.mul_sum] at key
  rw [show (1 / (n : ℝ)) * ∑ i, x i = (∑ i, x i) / n by ring] at key
  exact key.trans_eq (by ring)

theorem power_mean_two {n : ℕ} (a : Fin n → ℝ) :
    (∑ i, a i) ^ 2 ≤ n * ∑ i, (a i) ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => (1 : ℝ)) a
  simpa [Finset.card_univ, mul_comm] using this

theorem young_inequality (a b p q : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) : a * b ≤ a ^ p / p + b ^ q / q :=
  Real.young_inequality_of_nonneg ha hb
    (Real.holderConjugate_iff.2 ⟨hp, by rw [← one_div, ← one_div]; exact hpq⟩)
end MS.Inequalities

