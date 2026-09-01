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

open Matrix

/-- Unitary conjugation preserves the spectrum of the induced linear map. -/
theorem unitary_conj_spectrum_eq {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ)
    {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ) :
    spectrum ℂ (Matrix.toLin' (U * A * Uᴴ)) = spectrum ℂ (Matrix.toLin' A) := by
  have hmat : ∀ M : Matrix n n ℂ, Matrix.toLin' M = Matrix.toLinAlgEquiv' M := fun _ => rfl
  rw [hmat, hmat, AlgEquiv.spectrum_eq, AlgEquiv.spectrum_eq]
  let u : (Matrix n n ℂ)ˣ := Unitary.toUnits (⟨U, hU⟩ : unitary (Matrix n n ℂ))
  have h1 : (u : Matrix n n ℂ) = U := rfl
  have h2 : ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ) = Uᴴ := rfl
  calc spectrum ℂ (U * A * Uᴴ)
      = spectrum ℂ ((u : Matrix n n ℂ) * A * ((u⁻¹ : (Matrix n n ℂ)ˣ) : Matrix n n ℂ)) := by
        rw [h1, h2]
    _ = spectrum ℂ A := spectrum.units_conjugate

end Brockian.QuantumFiniteSpectral

