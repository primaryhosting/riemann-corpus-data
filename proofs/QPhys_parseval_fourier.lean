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

open MeasureTheory SchwartzMap
open scoped FourierTransform ComplexInnerProductSpace

namespace QPhys

/-- **Plancherel/Parseval theorem**: the Fourier transform is an `L²` isometry.

For square-integrable functions on a finite-dimensional real inner product space `E`
with values in a complex Hilbert space `F`, the Fourier transform
`𝓕 : L²(E, F) → L²(E, F)` preserves the norm and the inner product. -/
theorem parseval_fourier {E F : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (f g : Lp (α := E) F 2) :
    ‖𝓕 f‖ = ‖f‖ ∧ ⟪𝓕 f, 𝓕 g⟫ = ⟪f, g⟫ :=
  ⟨MeasureTheory.Lp.norm_fourier_eq f, MeasureTheory.Lp.inner_fourier_eq f g⟩

/-- Concrete form of Parseval's identity on the real line: for a Schwartz function
`f : ℝ → ℂ`, the Fourier integral `𝓕 f ξ = ∫ x, exp (-2πi x ξ) • f x` satisfies
`∫ ‖𝓕 f ξ‖² dξ = ∫ ‖f x‖² dx`. -/
theorem parseval_fourier_integral_real (f : 𝓢(ℝ, ℂ)) :
    ∫ ξ : ℝ, ‖𝓕 (fun x : ℝ => f x) ξ‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  simpa [SchwartzMap.fourier_coe] using SchwartzMap.integral_norm_sq_fourier f

end QPhys

