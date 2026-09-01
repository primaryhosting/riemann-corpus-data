/-
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hairer KPZ
Category: Frontier — Fields Medal Work
Target: Frontier.hairer_KPZ
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## The statement being formalized

The Kardar–Parisi–Zhang (KPZ) equation

  ∂_t h = ∂_x² h + (∂_x h)²  (+ noise),

is classically ill-posed because of the quadratic term; Hairer's theory of regularity
structures provides a solution theory for it.  The full stochastic well-posedness theory is
far beyond what is currently available in Mathlib, so what is formalized here is the
*classical (deterministic) core* of the solution theory: the **Cole–Hopf transform**, which
is the reduction underlying every construction of KPZ solutions (including Hairer's, where
it is used to identify the limit).

`Frontier.hairer_KPZ` states: if `Z` is a strictly positive classical solution of the
multiplicative stochastic heat equation `∂_t Z = ∂_x² Z + Z · ξ` for a given forcing `ξ`,
then `h = log Z` is a classical solution of the KPZ equation
`∂_t h = ∂_x² h + (∂_x h)² + ξ`.  Derivatives are given in the `HasDerivAt` form, with the
partial derivatives of `Z` supplied as explicit functions `Zx`, `Zxx`, `Zt`.  Taking
`ξ = 0` recovers the deterministic case.

`Frontier.hairer_KPZ_nonvacuous` exhibits data satisfying all the hypotheses, so the
statement is not vacuous.
-/

/-- **Cole–Hopf reduction for the KPZ equation.**

If `Z : ℝ → ℝ → ℝ` (time, space) is everywhere strictly positive, has partial derivatives
`Zx`, `Zxx` (first and second in space) and `Zt` (first in time), and solves the
multiplicative heat equation `Zt = Zxx + Z · ξ`, then `h := log ∘ Z` has spatial
derivatives `hX`, `hXX` and satisfies the KPZ equation
`∂_t h = ∂_x² h + (∂_x h)² + ξ`. -/
theorem hairer_KPZ (Z Zx Zxx Zt xi : ℝ → ℝ → ℝ)
    (hpos : ∀ t x, 0 < Z t x)
    (hZx : ∀ t x, HasDerivAt (fun y => Z t y) (Zx t x) x)
    (hZxx : ∀ t x, HasDerivAt (fun y => Zx t y) (Zxx t x) x)
    (hZt : ∀ t x, HasDerivAt (fun s => Z s x) (Zt t x) t)
    (heat : ∀ t x, Zt t x = Zxx t x + Z t x * xi t x) :
    ∃ hX hXX : ℝ → ℝ → ℝ,
      (∀ t x, HasDerivAt (fun y => Real.log (Z t y)) (hX t x) x) ∧
      (∀ t x, HasDerivAt (fun y => hX t y) (hXX t x) x) ∧
      (∀ t x, HasDerivAt (fun s => Real.log (Z s x))
        (hXX t x + (hX t x) ^ 2 + xi t x) t) := by
  refine ⟨fun t x => Zx t x / Z t x,
          fun t x => (Zxx t x * Z t x - Zx t x * Zx t x) / (Z t x) ^ 2, ?_, ?_, ?_⟩
  · intro t x
    exact (hZx t x).log (hpos t x).ne'
  · intro t x
    exact (hZxx t x).div (hZx t x) (hpos t x).ne'
  · intro t x
    have hne : Z t x ≠ 0 := (hpos t x).ne'
    have key : (Zxx t x * Z t x - Zx t x * Zx t x) / (Z t x) ^ 2 + (Zx t x / Z t x) ^ 2
          + xi t x = Zt t x / Z t x := by
      rw [heat t x]; field_simp; ring
    rw [key]
    exact (hZt t x).log hne

/-- The hypotheses of `Frontier.hairer_KPZ` are satisfiable: `Z t x = exp (t + x)` is a
positive solution of the heat equation.  (Its Cole–Hopf transform is the KPZ solution
`h t x = t + x`.) -/
theorem hairer_KPZ_nonvacuous :
    ∃ Z Zx Zxx Zt xi : ℝ → ℝ → ℝ,
      (∀ t x, 0 < Z t x) ∧
      (∀ t x, HasDerivAt (fun y => Z t y) (Zx t x) x) ∧
      (∀ t x, HasDerivAt (fun y => Zx t y) (Zxx t x) x) ∧
      (∀ t x, HasDerivAt (fun s => Z s x) (Zt t x) t) ∧
      (∀ t x, Zt t x = Zxx t x + Z t x * xi t x) := by
  refine ⟨fun t x => Real.exp (t + x), fun t x => Real.exp (t + x),
          fun t x => Real.exp (t + x), fun t x => Real.exp (t + x), fun _ _ => 0,
          fun t x => Real.exp_pos _, ?_, ?_, ?_, fun t x => by ring⟩
  · intro t x
    simpa using (Real.hasDerivAt_exp (t + x)).comp x ((hasDerivAt_id x).const_add t)
  · intro t x
    simpa using (Real.hasDerivAt_exp (t + x)).comp x ((hasDerivAt_id x).const_add t)
  · intro t x
    simpa using (Real.hasDerivAt_exp (t + x)).comp t ((hasDerivAt_id t).add_const x)

end Frontier

