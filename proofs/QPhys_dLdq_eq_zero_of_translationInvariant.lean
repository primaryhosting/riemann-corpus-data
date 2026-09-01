import Mathlib

/-!
# Noether's theorem in one dimension: translation invariance ⟹ conservation of momentum

We work with a Lagrangian `L : ℝ → ℝ → ℝ`, where `L q v` is the Lagrangian evaluated at
position `q` and velocity `v`.

* The *canonical momentum* along a trajectory `q : ℝ → ℝ` is
  `momentum L q t = ∂L/∂v (q t, q' t)`.
* The *Euler–Lagrange equation* says that the time derivative of the momentum equals
  `∂L/∂q (q t, q' t)`.

If `L` is translation invariant, i.e. `L (x + s) v = L x v` for all `s`, then `∂L/∂q = 0`,
hence the momentum is constant in time.
-/

namespace QPhys

/-- The partial derivative of the Lagrangian with respect to the position variable. -/
noncomputable def dLdq (L : ℝ → ℝ → ℝ) (q v : ℝ) : ℝ := deriv (fun x => L x v) q

/-- The partial derivative of the Lagrangian with respect to the velocity variable. -/
noncomputable def dLdv (L : ℝ → ℝ → ℝ) (q v : ℝ) : ℝ := deriv (fun w => L q w) v

/-- The canonical momentum along a trajectory `q`. -/
noncomputable def momentum (L : ℝ → ℝ → ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  dLdv L (q t) (deriv q t)

/-- `L` is translation invariant if shifting the position leaves it unchanged. -/
def TranslationInvariant (L : ℝ → ℝ → ℝ) : Prop := ∀ s x v, L (x + s) v = L x v

/-- A translation invariant Lagrangian has vanishing partial derivative in the position. -/
theorem dLdq_eq_zero_of_translationInvariant {L : ℝ → ℝ → ℝ}
    (h : TranslationInvariant L) (q v : ℝ) : dLdq L q v = 0 := by
  have hconst : (fun x => L x v) = fun _ : ℝ => L 0 v := by
    funext x
    simpa using h x 0 v
  simp [dLdq, hconst]

/-- **Noether's theorem (1D translations).**  If the Lagrangian `L` is invariant under
translations of the position variable, then along any trajectory `q` satisfying the
Euler–Lagrange equation the canonical momentum is conserved. -/
theorem noether_translation {L : ℝ → ℝ → ℝ} {q : ℝ → ℝ}
    (hinv : TranslationInvariant L)
    (hEL : ∀ t : ℝ, HasDerivAt (momentum L q) (dLdq L (q t) (deriv q t)) t)
    (t₁ t₂ : ℝ) : momentum L q t₁ = momentum L q t₂ := by
  have hEL0 : ∀ t : ℝ, HasDerivAt (momentum L q) 0 t := by
    intro t
    simpa [dLdq_eq_zero_of_translationInvariant hinv] using hEL t
  have hdiff : Differentiable ℝ (momentum L q) := fun t => (hEL0 t).differentiableAt
  have hderiv : ∀ t : ℝ, deriv (momentum L q) t = 0 := fun t => (hEL0 t).deriv
  exact is_const_of_deriv_eq_zero hdiff hderiv t₁ t₂

end QPhys

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

