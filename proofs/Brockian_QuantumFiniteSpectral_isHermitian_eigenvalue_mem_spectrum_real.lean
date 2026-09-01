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

/-
# Finite-dimensional spectral bridges for quantum mechanics

Composite bridge lemmas over `Matrix`/`EuclideanSpace` that downstream Brockian
results (spectral scaffolds, Hilbert-Polya style operator arguments) can consume.
Everything here is finite and algebraic: no asymptotics, no O-notation.
-/
import Mathlib

namespace Brockian.QuantumFiniteSpectral

/-- The real eigenvalues of a Hermitian matrix, viewed in `ℂ`, are spectral values of the
associated linear map, and they are real (zero imaginary part). -/
theorem isHermitian_eigenvalue_mem_spectrum_real {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (i : n) :
    (hA.eigenvalues i : ℂ) ∈ spectrum ℂ (Matrix.toLin' A) ∧ (hA.eigenvalues i : ℂ).im = 0 := by
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Matrix.spectrum_toLin', hA.spectrum_eq_image_range]
  exact ⟨hA.eigenvalues i, Set.mem_range_self i, rfl⟩

end Brockian.QuantumFiniteSpectral

