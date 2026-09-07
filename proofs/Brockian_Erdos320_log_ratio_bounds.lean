/-
  Brockian/Erdos320Lemmas.lean

  Machine-checked harvest of the ONE genuinely unconditional analytic step in
  "Erdős Problem #320: A Spectral Completion" (C. Brock).

  The paper's Lemma 3.1 ("Reduction to U(N) and E(N)") rests on the elementary
  real inequality, stated there as:

      for 0 ≤ t ≤ 1/2,   0 ≤ -log(1 - t) ≤ t/(1-t) ≤ 2t.

  This is the load-bearing bound that turns the per-step deficit ε_n into the
  loss exponent L(N) and yields  0 ≤ L(N) ≤ 2·E(N).  Everything downstream in
  the paper is conditional on named conjectures; this chain of inequalities is
  the piece that must hold unconditionally, so it is exactly what to verify.

  We prove each link separately and then the paper's exact conjunction.
  No sorry / admit / axiom.
-/
import Mathlib

namespace Brockian.Erdos320

open Real

/-- Lower link: `0 ≤ -log(1 - t)` for `0 ≤ t ≤ 1/2` (indeed for `0 ≤ t < 1`).
    Since `0 < 1 - t ≤ 1`, `log(1 - t) ≤ 0`. -/
theorem neg_log_one_sub_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    0 ≤ -Real.log (1 - t) := by
  have h : Real.log (1 - t) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  linarith

/-- Middle link: `-log(1 - t) ≤ t/(1-t)` for `t < 1`.
    Proof: apply `log x ≤ x - 1` at `x = (1-t)⁻¹ > 0`, use `log x⁻¹ = -log x`,
    and simplify `(1-t)⁻¹ - 1 = t/(1-t)`. -/
theorem neg_log_one_sub_le_div {t : ℝ} (ht : t < 1) :
    -Real.log (1 - t) ≤ t / (1 - t) := by
  have hu : 0 < 1 - t := by linarith
  have hne : (1 - t) ≠ 0 := ne_of_gt hu
  have hinv : 0 < (1 - t)⁻¹ := inv_pos.mpr hu
  have h1 : Real.log (1 - t)⁻¹ ≤ (1 - t)⁻¹ - 1 := Real.log_le_sub_one_of_pos hinv
  rw [Real.log_inv] at h1
  have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by
    field_simp
    ring
  linarith [h1, heq.le, heq.ge]

/-- Upper link plus the whole chain: `-log(1 - t) ≤ 2t` for `0 ≤ t ≤ 1/2`.
    Combines the middle link with `t/(1-t) ≤ 2t` (valid since `1 - t ≥ 1/2`). -/
theorem neg_log_one_sub_le_two_mul {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    -Real.log (1 - t) ≤ 2 * t := by
  have hu : 0 < 1 - t := by linarith
  have hdiv : -Real.log (1 - t) ≤ t / (1 - t) := neg_log_one_sub_le_div (by linarith)
  have hbound : t / (1 - t) ≤ 2 * t := by
    rw [div_le_iff₀ hu]
    nlinarith [mul_nonneg ht0 (show (0 : ℝ) ≤ 1 - 2 * t by linarith)]
  linarith

/-- The paper's exact inequality chain (Lemma 3.1, the unconditional core):
    for `0 ≤ t ≤ 1/2`,
        `0 ≤ -log(1 - t)`  and  `-log(1 - t) ≤ 2t`.
    This is what makes `0 ≤ L(N) ≤ 2·E(N)` hold; it is genuinely unconditional. -/
theorem log_ratio_bounds {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    0 ≤ -Real.log (1 - t) ∧ -Real.log (1 - t) ≤ 2 * t :=
  ⟨neg_log_one_sub_nonneg ht0 ht, neg_log_one_sub_le_two_mul ht0 ht⟩

/-- Instantiation matching the paper's substitution `t = ε_n / 2` with `0 < ε_n ≤ 1`:
    each non-doubling step contributes `0 ≤ -log(1 - ε/2) ≤ ε`, so the summed loss
    `L(N)` obeys `0 ≤ L(N) ≤ E(N)` termwise (the paper writes `≤ 2·E(N)`; the
    sharper termwise bound `≤ ε` is what actually holds and implies theirs). -/
theorem step_loss_bounds {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 ≤ -Real.log (1 - ε / 2) ∧ -Real.log (1 - ε / 2) ≤ ε := by
  have ht0 : 0 ≤ ε / 2 := by linarith
  have ht : ε / 2 ≤ 1 / 2 := by linarith
  refine ⟨neg_log_one_sub_nonneg ht0 ht, ?_⟩
  have := neg_log_one_sub_le_two_mul ht0 ht
  linarith

end Brockian.Erdos320
