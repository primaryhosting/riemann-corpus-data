/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is
-- given as a plain block comment; it is repeated verbatim as a module docstring below.)

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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

/-- The position operator `X` acting on complex-valued functions of one real variable:
`(X f)(x) = x · f(x)`. -/
noncomputable def positionOp (f : ℝ → ℂ) : ℝ → ℂ := fun x => (x : ℂ) * f x

/-- The momentum operator `p = -i ℏ d/dx` acting on complex-valued functions of one real
variable. -/
noncomputable def momentumOp (hbar : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -Complex.I * (hbar : ℂ) * deriv f x

/-- **Canonical commutation relation.** On Schwartz space, with `p = -i ℏ d/dx` and `X` the
multiplication-by-`x` operator, one has `[X, p] = i ℏ`, pointwise:
`(X p f - p X f)(x) = i ℏ f(x)` for every Schwartz function `f : 𝓢(ℝ, ℂ)` and every `x : ℝ`. -/
theorem canonical_commutator (hbar : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    (positionOp (momentumOp hbar f) - momentumOp hbar (positionOp f)) x
      = Complex.I * (hbar : ℂ) * f x := by
  have hf : HasDerivAt (fun y : ℝ => f y) (deriv (fun y : ℝ => f y) x) x :=
    (f.differentiableAt).hasDerivAt
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
  have hmul : HasDerivAt (fun y : ℝ => (y : ℂ) * f y)
      (1 * f x + (x : ℂ) * deriv (fun y : ℝ => f y) x) x := hid.mul hf
  have hd : deriv (positionOp f) x = f x + (x : ℂ) * deriv (fun y : ℝ => f y) x := by
    simp only [positionOp]
    rw [hmul.deriv]; ring
  simp only [Pi.sub_apply, positionOp, momentumOp, hd]
  ring

end QPhys

