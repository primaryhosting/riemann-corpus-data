import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

open SchwartzMap

namespace QPhys

/-- The position operator `X : f ↦ (x ↦ x • f x)` on the Schwartz space `𝓢(ℝ, ℂ)`. -/
noncomputable def posOp : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))

/-- The momentum operator `p = -i ℏ d/dx` on the Schwartz space `𝓢(ℝ, ℂ)`. -/
noncomputable def momOp (hbar : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  (-(Complex.I * hbar)) • SchwartzMap.derivCLM ℂ ℂ

/-- `posOp` really is multiplication by the coordinate: `(x · f)(t) = t * f t`. -/
@[simp]
theorem posOp_apply (f : 𝓢(ℝ, ℂ)) (t : ℝ) : posOp f t = (t : ℂ) * f t := by
  have hg : Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ)) := by fun_prop
  simp [posOp, smulLeftCLM_apply hg]

/-- `momOp` really is `-i ℏ d/dx`: `(p f)(t) = -i ℏ * (deriv f) t`. -/
@[simp]
theorem momOp_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    momOp hbar f t = -(Complex.I * hbar) * deriv (f : ℝ → ℂ) t := by
  simp [momOp, derivCLM_apply]

/-- The canonical commutation relation `[x, p] = i ℏ` on Schwartz space. -/
theorem canonical_commutator (hbar : ℝ) :
    ⁅posOp, momOp hbar⁆ = (Complex.I * hbar) • ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ) := by
  have hg : Function.HasTemperateGrowth (fun x : ℝ => (x : ℂ)) := by fun_prop
  ext f x
  have hf : Differentiable ℝ (f : ℝ → ℂ) := f.differentiable
  simp [posOp, momOp, Ring.lie_def, smulLeftCLM_apply hg, derivCLM_apply]
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using Complex.ofRealCLM.hasDerivAt (x := x)
  have h2 : HasDerivAt (f : ℝ → ℂ) (deriv (f : ℝ → ℂ) x) x := (hf x).hasDerivAt
  have h3 : HasDerivAt (fun y : ℝ => (y : ℂ) * f y) (1 * f x + x * deriv (f : ℝ → ℂ) x) x :=
    h1.mul h2
  rw [h3.deriv]
  ring

/-- Pointwise form of the canonical commutation relation:
`(x p f - p x f)(t) = i ℏ f t` for every Schwartz function `f`. -/
theorem canonical_commutator_apply (hbar : ℝ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) :
    ⁅posOp, momOp hbar⁆ f t = (Complex.I * hbar) * f t := by
  rw [canonical_commutator hbar]
  simp

end QPhys

