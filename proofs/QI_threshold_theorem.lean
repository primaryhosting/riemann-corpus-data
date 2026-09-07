import Mathlib

/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

/-- The logical error rate of a circuit location after `L` levels of code
concatenation, given a physical error rate `p` and a constant `c` counting the
number of malignant pairs of fault locations in one level-1 gadget.

One level of concatenation replaces each location by a gadget that fails only if
at least two of its locations fail, giving the standard recursion
`p_{L+1} = c * p_L ^ 2`. -/
noncomputable def logicalError (c p : ℝ) : ℕ → ℝ
  | 0 => p
  | (L + 1) => c * (logicalError c p L) ^ 2

@[simp] lemma logicalError_zero (c p : ℝ) : logicalError c p 0 = p := rfl

@[simp] lemma logicalError_succ (c p : ℝ) (L : ℕ) :
    logicalError c p (L + 1) = c * (logicalError c p L) ^ 2 := rfl

/-- Closed form for the concatenation recursion: after `L` levels the logical
error rate is `(c * p) ^ (2 ^ L) / c`, i.e. it is doubly exponentially small in
the number of levels as soon as `c * p < 1`. -/
lemma logicalError_eq_pow (c p : ℝ) (hc : c ≠ 0) (L : ℕ) :
    logicalError c p L = (c * p) ^ (2 ^ L) / c := by
  induction L with
  | zero => simp [mul_div_cancel_left₀ p hc]
  | succ L ih =>
      rw [logicalError_succ, ih, pow_succ 2 L, pow_mul]
      field_simp

/-- **Threshold theorem** (quantitative core).

`p_th = 1 / c` is a constant error threshold: if the physical error rate `p`
satisfies `p < p_th` (equivalently `c * p < 1`), then by concatenating the code
enough times the logical error rate can be made smaller than any prescribed
accuracy `ε > 0`, and it stays below `ε` for every larger number of levels.
Hence fault-tolerant quantum computation to arbitrary accuracy is possible below
the threshold. -/
theorem threshold_theorem {c p : ℝ} (hc : 0 < c) (hp : 0 ≤ p) (hthr : c * p < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → logicalError c p L < ε := by
  set q : ℝ := c * p with hq
  have hq0 : 0 ≤ q := mul_nonneg hc.le hp
  have hq1 : q < 1 := hthr
  obtain ⟨L₀, hL₀⟩ : ∃ n : ℕ, q ^ n < ε * c :=
    exists_pow_lt_of_lt_one (by positivity) hq1
  refine ⟨L₀, fun L hL => ?_⟩
  have hle : q ^ (2 ^ L) ≤ q ^ L₀ := by
    refine pow_le_pow_of_le_one hq0 hq1.le ?_
    exact le_trans hL (Nat.le_of_lt (Nat.lt_two_pow_self))
  rw [logicalError_eq_pow c p hc.ne', div_lt_iff₀ hc]
  exact lt_of_le_of_lt hle hL₀

/-- Below threshold, the logical error rate tends to `0` as the number of
concatenation levels grows. -/
theorem logicalError_tendsto_zero {c p : ℝ} (hc : 0 < c) (hp : 0 ≤ p)
    (hthr : c * p < 1) :
    Filter.Tendsto (fun L : ℕ => logicalError c p L) Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := threshold_theorem hc hp hthr hε
  refine ⟨L₀, fun L hL => ?_⟩
  have hnonneg : 0 ≤ logicalError c p L := by
    rw [logicalError_eq_pow c p hc.ne']
    exact div_nonneg (pow_nonneg (mul_nonneg hc.le hp) _) hc.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact hL₀ L hL

end QI

#print axioms QI.threshold_theorem
#print axioms QI.logicalError_tendsto_zero

