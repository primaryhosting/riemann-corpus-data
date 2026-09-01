import Mathlib

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

/-!
# Threshold Theorem
Category: Frontier Qi
Target: QI.threshold_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-- `logicalError c p L` is the logical failure rate of a level-`L` concatenated
fault-tolerant encoding, when the physical error rate is `p` and each level of
concatenation fails only if at least two of its sub-blocks fail, so that the
error rate is squared and multiplied by a combinatorial constant `c` at each level. -/
noncomputable def logicalError (c p : ℝ) : ℕ → ℝ
  | 0 => p
  | (L + 1) => c * (logicalError c p L) ^ 2

@[simp] lemma logicalError_zero (c p : ℝ) : logicalError c p 0 = p := rfl

@[simp] lemma logicalError_succ (c p : ℝ) (L : ℕ) :
    logicalError c p (L + 1) = c * (logicalError c p L) ^ 2 := rfl

/-- Closed form for the level-`L` logical error rate:
`logicalError c p L = (c * p) ^ (2 ^ L) / c`. -/
lemma logicalError_eq (c p : ℝ) (hc : 0 < c) (L : ℕ) :
    logicalError c p L = (c * p) ^ (2 ^ L) / c := by
  induction L with
  | zero => simp; field_simp
  | succ L ih =>
      rw [logicalError_succ, ih]
      rw [pow_succ 2 L, pow_mul]
      field_simp

/-- The logical error rate is nonnegative below threshold. -/
lemma logicalError_nonneg (c p : ℝ) (hc : 0 < c) (hp : 0 ≤ p) (L : ℕ) :
    0 ≤ logicalError c p L := by
  rw [logicalError_eq c p hc L]
  positivity

/-- **Threshold theorem** (concatenated-code form).

If the physical error rate `p` is nonnegative and lies strictly below the
constant threshold `1 / c` (where `c > 0` is the combinatorial constant of the
fault-tolerant gadget), then for every target accuracy `ε > 0` there is a level
of concatenation `L₀` such that every deeper encoding achieves a logical error
rate that is nonnegative and smaller than `ε`.  Thus arbitrarily accurate
(fault-tolerant) quantum computation is possible below the threshold. -/
theorem threshold_theorem (c p : ℝ) (hc : 0 < c) (hp : 0 ≤ p) (hthr : p < 1 / c)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      0 ≤ logicalError c p L ∧ logicalError c p L < ε := by
  set q : ℝ := c * p with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by
    rw [hq]
    rw [lt_div_iff₀ hc] at hthr
    linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (x := c * ε) (y := q) (by positivity) hq1
  refine ⟨N, fun L hL => ⟨logicalError_nonneg c p hc hp L, ?_⟩⟩
  rw [logicalError_eq c p hc L, div_lt_iff₀ hc, mul_comm ε c]
  calc q ^ (2 ^ L) ≤ q ^ N := by
        refine pow_le_pow_of_le_one hq0 hq1.le ?_
        exact le_trans hL (Nat.le_of_lt (Nat.lt_two_pow_self))
    _ < c * ε := hN

end QI

