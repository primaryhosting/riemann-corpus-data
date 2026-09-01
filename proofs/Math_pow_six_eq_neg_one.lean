import Mathlib

/-!
# Mobius Root Sum 12
Category: Pure Mathematics
Target: Math.mobius_root_sum_12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset

namespace Math

/-- If `z` is a primitive `12`-th root of unity in `ℂ`, then `z ^ 6 = -1`. -/
lemma pow_six_eq_neg_one {z : ℂ} (hz : IsPrimitiveRoot z 12) : z ^ 6 = -1 := by
  have h12 : (z ^ 6) ^ 2 = 1 := by
    rw [← pow_mul]; exact hz.pow_eq_one
  have hne : z ^ 6 ≠ 1 := hz.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have hfac : (z ^ 6 - 1) * (z ^ 6 + 1) = 0 := by linear_combination h12
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hne
  · linear_combination h

/-- Negation maps primitive `12`-th roots of unity to primitive `12`-th roots of unity. -/
lemma neg_mem_primitiveRoots_twelve {z : ℂ} (hz : z ∈ primitiveRoots 12 ℂ) :
    -z ∈ primitiveRoots 12 ℂ := by
  rw [mem_primitiveRoots (by norm_num)] at hz ⊢
  have h6 : z ^ 6 = -1 := pow_six_eq_neg_one hz
  have h7 : z ^ 7 = -z := by
    calc z ^ 7 = z ^ 6 * z := by ring
      _ = -z := by rw [h6]; ring
  have h := hz.pow_of_coprime 7 (by norm_num)
  rwa [h7] at h

/-- **Möbius root sum for `n = 12`.**
The sum of the primitive `12`-th roots of unity in `ℂ` equals `μ 12` (which is `0`,
since `12 = 2 ^ 2 * 3` is not squarefree). -/
theorem mobius_root_sum_12 :
    ∑ z ∈ primitiveRoots 12 ℂ, z = (ArithmeticFunction.moebius 12 : ℂ) := by
  have hmu : ArithmeticFunction.moebius 12 = 0 :=
    ArithmeticFunction.moebius_eq_zero_of_not_squarefree (by decide)
  rw [hmu]
  push_cast
  refine Finset.sum_involution (fun z _ => -z) (fun z _ => by ring) ?_
    (fun z hz => neg_mem_primitiveRoots_twelve hz) (fun z _ => neg_neg z)
  intro z hz hz0 hcon
  exact hz0 (by linear_combination (-1 / 2 : ℂ) * hcon)

/-- Sanity check: the sum above is over a nonempty set — there are exactly
`φ 12 = 4` primitive `12`-th roots of unity in `ℂ`. -/
lemma card_primitiveRoots_twelve : (primitiveRoots 12 ℂ).card = 4 := by
  rw [(Complex.isPrimitiveRoot_exp 12 (by norm_num)).card_primitiveRoots]
  decide

end Math
#print axioms Math.mobius_root_sum_12

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

