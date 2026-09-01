import Mathlib

/-!
# Conjugation To Momentum
Category: Gate1 Operator
Target: Brockian.DilationGenerator.conjugation_to_momentum
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

/-- The unitary implementing the logarithmic substitution on the level of functions:
`(U f) t = e^{t/2} f (e^t)`. -/
noncomputable def logSubst (f : ℝ → ℂ) : ℝ → ℂ :=
  fun t => Real.exp (t / 2) • f (Real.exp t)

/-- Key intermediate lemma: the derivative of `t ↦ e^{t/2} f(e^t)` at `t`,
computed by the chain and product rules, for `f` differentiable at `e^t`. -/
theorem hasDerivAt_logSubst {f : ℝ → ℂ} {t : ℝ} (hf : DifferentiableAt ℝ f (Real.exp t)) :
    HasDerivAt (logSubst f)
      (Real.exp (t / 2) • ((1 / 2) * f (Real.exp t)
        + Real.exp t * deriv f (Real.exp t))) t := by
  have hexp2 : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    simpa using ((hasDerivAt_id t).div_const 2).exp
  have hexp : HasDerivAt (fun s : ℝ => Real.exp s) (Real.exp t) t := Real.hasDerivAt_exp t
  have hcomp : HasDerivAt (fun s : ℝ => f (Real.exp s))
      (deriv f (Real.exp t) * Real.exp t) t := by
    have := (hf.hasDerivAt).scomp t hexp
    simpa [Function.comp, mul_comm, smul_eq_mul] using this
  have hprod := hexp2.smul hcomp
  have hgoal : Real.exp (t / 2) • ((1 / 2) * f (Real.exp t)
        + Real.exp t * deriv f (Real.exp t))
      = Real.exp (t / 2) • (deriv f (Real.exp t) * Real.exp t)
        + (Real.exp (t / 2) * (1 / 2)) • f (Real.exp t) := by
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [hgoal]
  exact hprod

/-- Under the log substitution `(U f) t = e^{t/2} f (e^t)`, the dilation generator
`A f = i ((1/2) f + x f')` transports to the momentum operator `i d/dt`:
pointwise, `U (A f) t = i (U f)' t`.

The hypotheses of smoothness and compact support inside `(0, ∞)` are those of the intended
operator-theoretic setting; only differentiability of `f` at `e^t` is actually needed for this
pointwise identity. This is a pointwise statement only; no operator-level (essential
self-adjointness) claim is made. -/
theorem conjugation_to_momentum {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (_hsupp : HasCompactSupport f) (_hsupp' : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) • (Complex.I * ((1 / 2) * f (Real.exp t)
        + Real.exp t * deriv f (Real.exp t)))
      = Complex.I * deriv (fun s => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hdiff : DifferentiableAt ℝ f (Real.exp t) := (hf.differentiable (by simp)).differentiableAt
  have hd : deriv (fun s => Real.exp (s / 2) • f (Real.exp s)) t
      = Real.exp (t / 2) • ((1 / 2) * f (Real.exp t)
        + Real.exp t * deriv f (Real.exp t)) :=
    (hasDerivAt_logSubst hdiff).deriv
  rw [hd]
  simp only [Complex.real_smul]
  ring

end DilationGenerator
end Brockian

#print axioms Brockian.DilationGenerator.conjugation_to_momentum

