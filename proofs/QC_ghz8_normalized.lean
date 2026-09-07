/-
# Ghz 8 Normalized
Category: Quantum Computing
Target: QC.ghz8_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The state space of 8 qubits: the complex Hilbert space with orthonormal basis indexed by
the computational basis states `Fin 8 → Bool`. -/
abbrev Qubits8 := EuclideanSpace ℂ (Fin 8 → Bool)

/-- The computational basis state `|b⟩` of 8 qubits. -/
noncomputable def basisState (b : Fin 8 → Bool) : Qubits8 := EuclideanSpace.single b 1

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`. -/
noncomputable def ghz8 : Qubits8 :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) • (basisState (fun _ => false) + basisState (fun _ => true))

/-- For two distinct computational basis states, `‖|x⟩ + |y⟩‖ = √2`. -/
theorem norm_basisState_add_basisState {x y : Fin 8 → Bool} (h : x ≠ y) :
    ‖basisState x + basisState y‖ = Real.sqrt 2 := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  have key : ∀ b : (Fin 8 → Bool), ‖(basisState x + basisState y : Qubits8) b‖ ^ 2
      = (if b = x then (1 : ℝ) else 0) + (if b = y then 1 else 0) := by
    intro b
    by_cases hx : b = x <;> by_cases hy : b = y <;>
      simp_all [basisState, EuclideanSpace.single_apply]
  calc ∑ b : (Fin 8 → Bool), ‖(basisState x + basisState y : Qubits8) b‖ ^ 2
      = ∑ b : (Fin 8 → Bool), ((if b = x then (1 : ℝ) else 0) + (if b = y then 1 else 0)) :=
        Finset.sum_congr rfl (fun b _ => key b)
    _ = 2 := by rw [Finset.sum_add_distrib]; simp; norm_num

/-- The 8-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2` is a unit vector. -/
theorem ghz8_normalized : ‖ghz8‖ = 1 := by
  have hne : (fun _ => false : Fin 8 → Bool) ≠ (fun _ => true) := by
    intro h
    have := congrFun h 0
    simp at this
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  rw [ghz8, norm_smul, norm_basisState_add_basisState hne]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.sqrt 2)]
  field_simp

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

