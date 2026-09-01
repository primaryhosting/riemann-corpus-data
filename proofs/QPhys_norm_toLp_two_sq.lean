/-
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 forbids a module docstring `/-! ... -/` before `import`; the required header is
-- reproduced verbatim as a module docstring immediately after the import below.)

import Mathlib

/-!
# Parseval Fourier
Category: Quantum Physics
Target: QPhys.parseval_fourier
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

open MeasureTheory SchwartzMap FourierTransform

section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The squared `L²`-norm of (the `L²`-class of) a Schwartz function is the integral of the
squared pointwise norm. -/
theorem norm_toLp_two_sq (f : 𝓢(V, ℂ)) :
    ‖f.toLp 2 volume‖ ^ 2 = ∫ x : V, ‖f x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  have h2 : ∀ᵐ x : V, inner ℂ ((f.toLp 2 volume : V → ℂ) x) ((f.toLp 2 volume : V → ℂ) x)
      = ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    filter_upwards [SchwartzMap.coeFn_toLp f 2 volume] with x hx
    rw [hx, inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [integral_congr_ae h2, integral_complex_ofReal]
  simp

/-- **Parseval/Plancherel theorem** for the Fourier transform, in integral form:
for a Schwartz function `f` on a finite-dimensional real inner product space, the total
"energy" `∫ ‖f x‖²` is preserved by the Fourier transform. -/
theorem parseval_fourier' (f : 𝓢(V, ℂ)) :
    ∫ w : V, ‖(𝓕 f) w‖ ^ 2 = ∫ x : V, ‖f x‖ ^ 2 := by
  rw [← norm_toLp_two_sq, ← norm_toLp_two_sq, norm_fourier_toL2_eq f]

end

/-- **Parseval's theorem for the Fourier transform** (Plancherel), on the real line:
for every Schwartz function `f : ℝ → ℂ`, the Fourier transform preserves the `L²`-energy,
`∫ |𝓕f(w)|² dw = ∫ |f(x)|² dx`. -/
theorem parseval_fourier (f : 𝓢(ℝ, ℂ)) :
    ∫ w : ℝ, ‖(𝓕 f) w‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 :=
  parseval_fourier' f

/-- The `L²`-version of Parseval's theorem: the Fourier transform is an isometry of
`L²(ℝ, ℂ)`. -/
theorem parseval_fourier_L2_norm (f : Lp (α := ℝ) ℂ 2) : ‖𝓕 f‖ = ‖f‖ :=
  MeasureTheory.Lp.norm_fourier_eq f

/-- Parseval's identity for inner products: the Fourier transform preserves the `L²` inner
product. -/
theorem parseval_fourier_L2_inner (f g : Lp (α := ℝ) ℂ 2) :
    inner ℂ (𝓕 f) (𝓕 g) = inner ℂ f g :=
  MeasureTheory.Lp.inner_fourier_eq f g

end QPhys

