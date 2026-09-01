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

/-- The state space of 7 qubits: the complex Hilbert space `ℂ^(2^7)`, indexed by
bit strings `Fin 7 → Fin 2`. -/
abbrev Qubits7 : Type := EuclideanSpace ℂ (Fin 7 → Fin 2)

/-- The 7-qubit GHZ state `(|0…0⟩ + |1…1⟩)/√2`: the amplitude is `1/√2` on the
all-zeros and all-ones bit strings, and `0` elsewhere. -/
noncomputable def ghz7 : Qubits7 :=
  WithLp.toLp 2 fun v =>
    if v = (fun _ => 0) ∨ v = (fun _ => 1) then (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) else 0

/-- The 7-qubit GHZ state is a unit vector. -/
theorem ghz7_normalized : ‖ghz7‖ = 1 := by
  have hne : (fun _ : Fin 7 => (0 : Fin 2)) ≠ (fun _ : Fin 7 => (1 : Fin 2)) := by
    intro h
    have := congrFun h ⟨0, by norm_num⟩
    simp at this
  rw [EuclideanSpace.norm_eq]
  have key : ∀ v : (Fin 7 → Fin 2), ‖ghz7.ofLp v‖ ^ 2
      = if v ∈ ({(fun _ => 0), (fun _ => 1)} : Finset (Fin 7 → Fin 2)) then (2 : ℝ)⁻¹ else 0 := by
    intro v
    simp only [ghz7, WithLp.ofLp_toLp, Finset.mem_insert, Finset.mem_singleton]
    by_cases h : v = (fun _ => 0) ∨ v = (fun _ => 1)
    · rw [if_pos h, if_pos h, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), ← Real.sqrt_inv, Real.sq_sqrt (by norm_num)]
    · rw [if_neg h, if_neg h]
      simp
  simp only [key]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Finset.card_pair hne]
  norm_num

end QC

