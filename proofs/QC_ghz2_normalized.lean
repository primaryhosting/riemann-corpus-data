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

namespace QC

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 2 → Fin 2)` whose index type is the set of 2-bit strings.
Its amplitude is `1/√2` on the all-zeros and all-ones strings, and `0` elsewhere. -/
noncomputable def ghz2 : EuclideanSpace ℂ (Fin 2 → Fin 2) :=
  WithLp.toLp 2 (fun x : Fin 2 → Fin 2 =>
    if (∀ i, x i = 0) ∨ (∀ i, x i = 1) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The 2-qubit GHZ state is a unit vector. -/
theorem ghz2_normalized : ‖ghz2‖ = 1 := by
  have huniv : (Finset.univ : Finset (Fin 2 → Fin 2)) = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by
    decide
  rw [EuclideanSpace.norm_eq, huniv]
  norm_num [ghz2, Fin.forall_fin_two]

end QC

