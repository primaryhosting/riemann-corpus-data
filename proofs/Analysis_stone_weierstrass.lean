import Mathlib

/-!
# Stone Weierstrass
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.stone_weierstrass
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Analysis

/-- **Stone–Weierstrass theorem (polynomial form).**
On a compact interval `[a, b] ⊆ ℝ`, the subalgebra of polynomial functions is dense in the
algebra `C([a,b], ℝ)` of continuous real-valued functions with the uniform (sup-norm) topology:
its topological closure is the whole space. -/
theorem stone_weierstrass (a b : ℝ) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ :=
  polynomialFunctions_closure_eq_top a b

/-- Uniform-approximation form of the Stone–Weierstrass theorem, derived from
`Analysis.stone_weierstrass`: every continuous function on `[a, b]` is uniformly approximated,
to within any `ε > 0`, by (the evaluation of) a real polynomial. -/
theorem stone_weierstrass_approx (a b : ℝ) (f : C(Set.Icc a b, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, ∀ x : Set.Icc a b, |p.eval (x : ℝ) - f x| < ε := by
  -- `f` lies in the topological closure of the polynomial functions.
  have hmem : f ∈ closure ((polynomialFunctions (Set.Icc a b) : Subalgebra ℝ C(Set.Icc a b, ℝ)) :
      Set C(Set.Icc a b, ℝ)) := by
    have : f ∈ (polynomialFunctions (Set.Icc a b)).topologicalClosure := by
      rw [stone_weierstrass a b]; trivial
    exact this
  -- Hence some polynomial function is within `ε` of `f` in the sup norm.
  obtain ⟨g, hg, hgf⟩ := Metric.mem_closure_iff.mp hmem ε hε
  obtain ⟨p, -, hp⟩ := hg
  refine ⟨p, fun x => ?_⟩
  have h := ContinuousMap.dist_apply_le_dist (f := g) (g := f) x
  have hx : dist (g x) (f x) < ε := lt_of_le_of_lt h (by simpa [dist_comm] using hgf)
  rw [← hp] at hx
  simpa [Polynomial.toContinuousMapOnAlgHom, Polynomial.toContinuousMapOn,
    Polynomial.toContinuousMap, Real.dist_eq] using hx

end Analysis

