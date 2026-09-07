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

/-- The 4-qubit GHZ state `(|0000⟩ + |1111⟩)/√2`, as a vector of the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2 × Fin 2)`: its amplitude is `1/√2` at the
all-zeros and all-ones basis states and `0` elsewhere. -/
noncomputable def ghz4 : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2 × Fin 2) :=
  WithLp.toLp 2 (fun v => if v = (0, 0, 0, 0) then ((Real.sqrt 2)⁻¹ : ℂ)
    else if v = (1, 1, 1, 1) then ((Real.sqrt 2)⁻¹ : ℂ) else 0)

/-- `ghz4` really is `(1/√2) • (|0000⟩ + |1111⟩)`, expressed with the standard basis
vectors `EuclideanSpace.single`. -/
theorem ghz4_eq_smul_add_single :
    ghz4 = ((Real.sqrt 2)⁻¹ : ℂ) •
      (EuclideanSpace.single ((0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)) (1 : ℂ)
        + EuclideanSpace.single ((1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2)) (1 : ℂ)) := by
  ext v
  simp [ghz4, EuclideanSpace.single_apply]
  split <;> split <;> simp_all

/-- The 4-qubit GHZ state is a unit vector. -/
theorem ghz4_normalized : ‖ghz4‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [ghz4, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

end QC

