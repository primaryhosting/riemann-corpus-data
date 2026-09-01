/-
# Ghz 4 Normalized
Category: Quantum Computing
Target: QC.ghz4_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2 × Fin 2)` of four qubits. -/
noncomputable def ghz4 : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun x => if x = (0, 0, 0, 0) ∨ x = (1, 1, 1, 1) then ((1 : ℂ) / Real.sqrt 2)
    else 0)

/-- The 4-qubit GHZ state is a unit vector. -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ghz4, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

end QC

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

