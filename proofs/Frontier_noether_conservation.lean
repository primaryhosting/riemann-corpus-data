/-
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Noether Conservation
Category: Frontier Physics
Target: Frontier.noether_conservation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- **Noether's theorem, one-dimensional case.**

Setting: a mechanical system with one degree of freedom, described by a Lagrangian
`L : ℝ → ℝ → ℝ`, `L q v`, whose partial derivatives are `Lq` (with respect to the position `q`)
and `Lv` (with respect to the velocity `v`).

* `q : ℝ → ℝ` is a (differentiable) trajectory with velocity `deriv q`.
* `X : ℝ → ℝ` is the infinitesimal generator of a one-parameter group of symmetries, i.e. the
  variation of the position is `δq = X (q t)`, and the induced variation of the velocity is
  `δv = deriv X (q t) * deriv q t`.
* `hEL` is the Euler–Lagrange equation `d/dt (Lv (q t) (q' t)) = Lq (q t) (q' t)` along the
  trajectory.
* `hsym` is the infinitesimal invariance of the Lagrangian under the symmetry:
  `Lq u v * X u + Lv u v * (deriv X u * v) = 0` for all `(u, v)` in phase space.

Conclusion: the Noether current `J t = Lv (q t) (q' t) * X (q t)`, the momentum conjugate to the
symmetry direction, is conserved: it takes the same value at all times. -/
theorem noether_conservation
    (Lq Lv : ℝ → ℝ → ℝ) (q X : ℝ → ℝ)
    (hq : Differentiable ℝ q) (hX : Differentiable ℝ X)
    (hEL : ∀ t : ℝ, HasDerivAt (fun s => Lv (q s) (deriv q s)) (Lq (q t) (deriv q t)) t)
    (hsym : ∀ u v : ℝ, Lq u v * X u + Lv u v * (deriv X u * v) = 0) :
    ∀ t s : ℝ, Lv (q t) (deriv q t) * X (q t) = Lv (q s) (deriv q s) * X (q s) := by
  -- The Noether current has derivative zero everywhere.
  have hJ : ∀ t : ℝ, HasDerivAt (fun s => Lv (q s) (deriv q s) * X (q s)) 0 t := by
    intro t
    have hXq : HasDerivAt (fun s => X (q s)) (deriv X (q t) * deriv q t) t :=
      (hX (q t)).hasDerivAt.comp t (hq t).hasDerivAt
    have h := (hEL t).mul hXq
    rwa [hsym (q t) (deriv q t)] at h
  have hdiff : Differentiable ℝ fun s => Lv (q s) (deriv q s) * X (q s) := fun t =>
    (hJ t).differentiableAt
  exact is_const_of_deriv_eq_zero hdiff fun t => (hJ t).deriv

end Frontier

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

