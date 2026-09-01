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

namespace Math

/-- **Weierstrass approximation theorem** (density form):
the set of continuous functions on `[a,b]` that come from a real polynomial is dense in
`C([a,b], ℝ)`, which carries the sup norm. -/
theorem weierstrass_approx (a b : ℝ) :
    Dense {f : C(Set.Icc a b, ℝ) |
      ∃ p : Polynomial ℝ, p.toContinuousMapOn (Set.Icc a b) = f} := by
  have h : {f : C(Set.Icc a b, ℝ) |
      ∃ p : Polynomial ℝ, p.toContinuousMapOn (Set.Icc a b) = f}
      = (polynomialFunctions (Set.Icc a b) : Set C(Set.Icc a b, ℝ)) := by
    rw [polynomialFunctions_coe]
    ext f
    simp [Polynomial.toContinuousMapOnAlgHom, eq_comm]
  rw [h, dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe,
    polynomialFunctions_closure_eq_top a b]
  simp

/-- **Weierstrass approximation theorem** (epsilon form): every function continuous on `[a,b]`
is uniformly approximated on `[a,b]`, to any accuracy `ε > 0`, by a real polynomial. -/
theorem weierstrass_approx_eps (a b : ℝ) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b))
    (ε : ℝ) (hε : 0 < ε) : ∃ p : Polynomial ℝ, ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε :=
  exists_polynomial_near_of_continuousOn a b f hf ε hε

end Math

