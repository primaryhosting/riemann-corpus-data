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

/-- The computational-basis ket `|x⟩` for a 5-bit string `x`, as a vector in the
5-qubit state space `ℂ^(2^5)`, modelled as `EuclideanSpace ℂ (Fin 5 → Fin 2)`. -/
noncomputable def ket (x : Fin 5 → Fin 2) : EuclideanSpace ℂ (Fin 5 → Fin 2) :=
  EuclideanSpace.single x 1

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`. -/
noncomputable def ghz5 : EuclideanSpace ℂ (Fin 5 → Fin 2) :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (ket (fun _ => 0) + ket (fun _ => 1))

theorem zeros_ne_ones : ((fun _ => 0 : Fin 5 → Fin 2)) ≠ (fun _ => 1) := by
  intro h
  have := congrFun h 0
  simp at this

/-- Coordinates of the GHZ state: it is `1/√2` on the all-zeros and all-ones basis
strings and `0` elsewhere. -/
theorem ghz5_apply (x : Fin 5 → Fin 2) :
    ghz5.ofLp x
      = if x = (fun _ => 0) ∨ x = (fun _ => 1) then ((Real.sqrt 2)⁻¹ : ℂ) else 0 := by
  by_cases h0 : x = (fun _ => 0) <;> by_cases h1 : x = (fun _ => 1) <;>
    simp [ghz5, ket, EuclideanSpace.single_apply, h0, h1, zeros_ne_ones, zeros_ne_ones.symm]

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2` is a unit vector. -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have key : ∀ x : Fin 5 → Fin 2,
      ‖ghz5.ofLp x‖ ^ 2
        = (if x = (fun _ => 0) then (1 / 2 : ℝ) else 0)
          + (if x = (fun _ => 1) then (1 / 2 : ℝ) else 0) := by
    intro x
    rw [ghz5_apply]
    by_cases h0 : x = (fun _ => 0) <;> by_cases h1 : x = (fun _ => 1) <;>
      simp [h0, h1, zeros_ne_ones, zeros_ne_ones.symm]
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ ((fun _ => 0 : Fin 5 → Fin 2)) (fun _ => (1 / 2 : ℝ)),
    Finset.sum_ite_eq' Finset.univ ((fun _ => 1 : Fin 5 → Fin 2)) (fun _ => (1 / 2 : ℝ))]
  norm_num

end QC

