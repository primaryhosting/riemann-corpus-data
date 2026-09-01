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

import Mathlib
/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set

namespace Brockian.DilationGenerator

/-- The substitution `x = exp t` turns the `L²`-integral on `(0, ∞)` into the `L²`-integral on
`ℝ` of `t ↦ exp (t/2) • f (exp t)`.  This is the norm-preserving property of the Mellin
(logarithmic) change of variables `U f (t) = e^{t/2} f(e^t)`. -/
theorem mellin_log_unitary {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ x in Set.Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  have himg : Real.exp '' (Set.univ : Set ℝ) = Set.Ioi (0 : ℝ) := by
    rw [Set.image_univ, Real.range_exp]
  rw [← himg, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    Measure.restrict_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hsq : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [sq, ← Real.exp_add]; ring_nf
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, hsq,
    smul_eq_mul]

end Brockian.DilationGenerator

