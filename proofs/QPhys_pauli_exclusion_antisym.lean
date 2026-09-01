import Mathlib

/-!
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
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

namespace QPhys

variable {𝕜 H : Type*} [CommRing 𝕜] [AddCommGroup H] [Module 𝕜 H]

/-- The antisymmetrized (unnormalized) two-particle state built from single-particle
states `u` and `v`: the Slater-determinant combination `u ⊗ v - v ⊗ u`. -/
noncomputable def antisymState (u v : H) : TensorProduct 𝕜 H H :=
  u ⊗ₜ[𝕜] v - v ⊗ₜ[𝕜] u

/-- Exchanging the two particles flips the sign of the antisymmetrized state. -/
theorem antisymState_swap (u v : H) :
    antisymState (𝕜 := 𝕜) v u = -antisymState (𝕜 := 𝕜) u v := by
  simp [antisymState]

/-- **Pauli exclusion principle.** A two-fermion antisymmetric state whose two
single-particle states coincide is the zero vector. -/
theorem pauli_exclusion_antisym (u : H) : antisymState (𝕜 := 𝕜) u u = 0 :=
  sub_self _

/-- The same statement in the exterior algebra: the wedge `u ∧ u` of a single-particle
state with itself vanishes.  This is `ExteriorAlgebra.ι_sq_zero`. -/
theorem pauli_exclusion_wedge (u : H) :
    ExteriorAlgebra.ι 𝕜 u * ExteriorAlgebra.ι 𝕜 u = 0 :=
  ExteriorAlgebra.ι_sq_zero u

/-- Amplitude form of the exclusion principle: if a two-particle wavefunction
`Psi : ι → ι → ℂ` is antisymmetric under exchange, then the amplitude for both fermions
to occupy the same single-particle mode `i` vanishes. -/
theorem pauli_exclusion_amplitude {ι : Type*} (Psi : ι → ι → ℂ)
    (hPsi : ∀ i j, Psi i j = -Psi j i) (i : ι) : Psi i i = 0 := by
  have h := hPsi i i
  linear_combination h / 2

end QPhys

