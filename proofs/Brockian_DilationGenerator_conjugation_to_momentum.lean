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

namespace Brockian.DilationGenerator

/-- **Conjugation of the dilation generator to the momentum operator (pointwise form).**

Let `U` be the log substitution `(U f)(t) = e^{t/2} • f (e^t)` and let
`A f = i ((1/2) f + x f')` be the dilation generator on `(0, ∞)`.  For `f : ℝ → ℂ`
smooth with compact support contained in `(0, ∞)`, the pointwise intertwining identity
`U (A f) (t) = i · (U f)' (t)` holds, i.e. `A = U⁻¹ ∘ (i · d/dt) ∘ U` on the core.

This is the pointwise identity only; no operator-level (essential self-adjointness)
claim is made.

The compact-support hypotheses `hsupp` and `hpos` are kept because they are part of the
requested statement, but the proof only needs differentiability of `f` at `e^t`. -/
theorem conjugation_to_momentum
    (f : ℝ → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f)
    (hpos : tsupport f ⊆ Set.Ioi (0 : ℝ)) (t : ℝ) :
    Real.exp (t / 2) •
        (Complex.I * ((1 / 2) * f (Real.exp t) + (Real.exp t : ℂ) * deriv f (Real.exp t)))
      = Complex.I * deriv (fun s => Real.exp (s / 2) • f (Real.exp s)) t := by
  have hE : HasDerivAt (fun s : ℝ => Real.exp (s / 2)) (Real.exp (t / 2) * (1 / 2)) t := by
    simpa using ((Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2))
  have hE2 : HasDerivAt (fun s : ℝ => Real.exp s) (Real.exp t) t := Real.hasDerivAt_exp t
  have hfd : HasDerivAt f (deriv f (Real.exp t)) (Real.exp t) :=
    (hf.differentiable (by simp)).differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun s : ℝ => f (Real.exp s))
      (Real.exp t • deriv f (Real.exp t)) t := hfd.scomp t hE2
  have hmul : HasDerivAt (fun s : ℝ => (Real.exp (s / 2) : ℂ) * f (Real.exp s))
      ((Real.exp (t / 2) * (1 / 2) : ℝ) * f (Real.exp t)
        + (Real.exp (t / 2) : ℂ) * (Real.exp t • deriv f (Real.exp t))) t :=
    (hE.ofReal_comp).mul hcomp
  have hEq : (fun s : ℝ => Real.exp (s / 2) • f (Real.exp s))
      = fun s : ℝ => (Real.exp (s / 2) : ℂ) * f (Real.exp s) := by
    funext s; simp [Complex.real_smul]
  rw [hEq, hmul.deriv]
  push_cast [Complex.real_smul]
  ring

end Brockian.DilationGenerator

