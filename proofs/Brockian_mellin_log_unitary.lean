import Mathlib

/-!
# Mellin Log Unitary
Category: Gate1 Operator
Target: Brockian.DilationGenerator.mellin_log_unitary
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

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exponential is a bijection from `ℝ` onto `(0, ∞)`. -/
theorem image_exp_univ : Real.exp '' (univ : Set ℝ) = Ioi (0 : ℝ) := by
  rw [Set.image_univ, Real.range_exp]

/-- Change of variables `x = e^t` for an arbitrary (vector valued) integrand:
`∫_{(0,∞)} g = ∫_ℝ e^t • g(e^t)`. -/
theorem integral_Ioi_eq_integral_exp_smul (g : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), g x = ∫ t : ℝ, Real.exp t • g (Real.exp t) := by
  rw [← image_exp_univ,
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    Measure.restrict_univ]
  simp [abs_of_pos (Real.exp_pos _)]

/-- **Mellin/logarithmic substitution is unitary.**

The substitution `x = e^t` induces the map `U f (t) = e^{t/2} • f (e^t)` from functions on
`(0, ∞)` to functions on `ℝ`, and this map preserves the `L²` integral:
`∫_{(0,∞)} ‖f x‖² dx = ∫_ℝ ‖e^{t/2} • f (e^t)‖² dt`.

No integrability or measurability hypotheses are needed: the identity is an instance of the
change-of-variables formula for the diffeomorphism `exp : ℝ ≃ (0, ∞)`, whose Jacobian `e^t`
is exactly the square of the normalising factor `e^{t/2}`. -/
theorem mellin_log_unitary (f : ℝ → E) :
    ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 = ∫ t : ℝ, ‖Real.exp (t / 2) • f (Real.exp t)‖ ^ 2 := by
  rw [integral_Ioi_eq_integral_exp_smul (fun x => ‖f x‖ ^ 2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have h2 : Real.exp (t / 2) ^ 2 = Real.exp t := by
    rw [sq, ← Real.exp_add]; ring_nf
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), h2, smul_eq_mul]

/-- The inverse substitution: `(U⁻¹ h) (x) = x^{-1/2} • h (log x)` really does invert
`U f (t) = e^{t/2} • f (e^t)` on `(0, ∞)`. -/
theorem inv_apply_apply (f : ℝ → E) {x : ℝ} (hx : 0 < x) :
    (x ^ (-(1 : ℝ) / 2) • (fun t : ℝ => Real.exp (t / 2) • f (Real.exp t)) (Real.log x)) = f x := by
  have h1 : Real.exp (Real.log x / 2) = x ^ ((1 : ℝ) / 2) := by
    rw [Real.rpow_def_of_pos hx]; ring_nf
  show x ^ (-(1 : ℝ) / 2) • (Real.exp (Real.log x / 2) • f (Real.exp (Real.log x))) = f x
  rw [Real.exp_log hx, h1, smul_smul, ← Real.rpow_add hx]
  norm_num

end DilationGenerator
end Brockian

