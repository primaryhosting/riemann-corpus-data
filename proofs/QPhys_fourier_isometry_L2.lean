/-
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Fourier transform is an `L²` isometry (Plancherel/Parseval).

* `QPhys.fourier_isometry_L2` : the abstract statement, `‖𝓕 f‖ = ‖f‖` for `f ∈ L²(ℝ, ℂ)`.
* `QPhys.parseval_fourier` : the concrete Parseval identity for wave functions, i.e. for
  Schwartz functions `f g : 𝓢(ℝ, ℂ)`,
  `∫ x, conj (f x) * g x = ∫ ξ, conj (𝓕 f ξ) * 𝓕 g ξ`.
* `QPhys.plancherel_fourier_norm_sq` : the special case `f = g`, i.e. conservation of the total
  probability `∫ ‖f x‖² = ∫ ‖𝓕 f ξ‖²`.
-/

open SchwartzMap MeasureTheory FourierTransform

namespace QPhys

/-- **Plancherel's theorem**: the Fourier transform is an isometry of `L²(ℝ, ℂ)`. -/
theorem fourier_isometry_L2 (f : Lp (α := ℝ) ℂ 2) : ‖𝓕 f‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- **Parseval's identity** for Schwartz-class wave functions on the line: the Fourier transform
preserves the `L²` inner product,
`∫ x, conj (f x) * g x = ∫ ξ, conj (𝓕 f ξ) * (𝓕 g) ξ`. -/
theorem parseval_fourier (f g : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, (starRingEnd ℂ) (f x) * g x = ∫ ξ : ℝ, (starRingEnd ℂ) (𝓕 f ξ) * 𝓕 g ξ := by
  have key := MeasureTheory.Lp.inner_fourier_eq (E := ℝ) (F := ℂ) (f.toLp 2) (g.toLp 2)
  rw [SchwartzMap.toLp_fourier_eq, SchwartzMap.toLp_fourier_eq, L2.inner_def, L2.inner_def] at key
  have h1 : ∫ a : ℝ, inner ℂ ((f.toLp 2 : ℝ → ℂ) a) ((g.toLp 2 : ℝ → ℂ) a)
      = ∫ x : ℝ, (starRingEnd ℂ) (f x) * g x := by
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp f 2 volume,
      SchwartzMap.coeFn_toLp g 2 volume] with a ha hb
    rw [ha, hb, RCLike.inner_apply, mul_comm]
  have h2 : ∫ a : ℝ, inner ℂ (((𝓕 f).toLp 2 : ℝ → ℂ) a) (((𝓕 g).toLp 2 : ℝ → ℂ) a)
      = ∫ ξ : ℝ, (starRingEnd ℂ) (𝓕 f ξ) * 𝓕 g ξ := by
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕 f) 2 volume,
      SchwartzMap.coeFn_toLp (𝓕 g) 2 volume] with a ha hb
    rw [ha, hb, RCLike.inner_apply, mul_comm]
  rw [h1, h2] at key
  exact key.symm

/-- **Plancherel/Parseval for the total probability**: for a Schwartz wave function on the line,
the Fourier transform preserves `∫ ‖·‖²`. -/
theorem plancherel_fourier_norm_sq (f : 𝓢(ℝ, ℂ)) :
    ∫ x : ℝ, ‖f x‖ ^ 2 = ∫ ξ : ℝ, ‖𝓕 f ξ‖ ^ 2 := by
  have hconj : ∀ z : ℂ, (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [mul_comm, Complex.mul_conj]
    norm_cast
    simp [Complex.normSq_eq_norm_sq]
  have key := parseval_fourier f f
  simp only [hconj] at key
  rw [integral_complex_ofReal, integral_complex_ofReal] at key
  exact_mod_cast key

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

