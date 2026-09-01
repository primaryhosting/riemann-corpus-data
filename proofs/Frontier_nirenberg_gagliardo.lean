import Mathlib

/-!
# Nirenberg Gagliardo
Category: Frontier Abel
Target: Frontier.nirenberg_gagliardo
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

open scoped ENNReal NNReal
open MeasureTheory Module

namespace Frontier

/-- **The Gagliardo–Nirenberg–Sobolev interpolation inequality.**

Let `E` be a finite-dimensional real normed space of dimension `n > 0`, equipped with an
additive Haar measure `μ`, and let `F` be a finite-dimensional real normed space.
Let `1 ≤ p` and let the Sobolev conjugate exponent `p'` satisfy `(p')⁻¹ = p⁻¹ - n⁻¹`.

Then there is a constant `C`, depending only on `E`, `F`, `μ` and `p` (and not on the
function), such that for every compactly supported `C¹` function `u : E → F` the `Lᵖ'`
norm of `u` is bounded by `C` times the `Lᵖ` norm of its Fréchet derivative. -/
theorem nirenberg_gagliardo
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hn : 0 < finrank ℝ E)
    (hp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (finrank ℝ E : ℝ)⁻¹) :
    ∃ C : ℝ≥0, ∀ u : E → F, ContDiff ℝ 1 u → HasCompactSupport u →
      eLpNorm u p' μ ≤ C * eLpNorm (fderiv ℝ u) p μ :=
  -- This is `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` from Mathlib
  -- (`Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean`), with the explicit
  -- constant `MeasureTheory.SNormLESNormFDerivOfEqConst F μ p`.
  ⟨SNormLESNormFDerivOfEqConst F μ p, fun _u hu h2u =>
    eLpNorm_le_eLpNorm_fderiv_of_eq μ hu h2u hp hn hp'⟩

end Frontier

