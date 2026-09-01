/-!
# Ghz 5 Normalized
Category: Quantum Computing
Target: QC.ghz5_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QC

/-- The 5-qubit GHZ state `(|00000⟩ + |11111⟩)/√2`, as a vector in the
Hilbert space `ℂ^(2^5)` whose coordinates are indexed by bit strings `Fin 5 → Bool`. -/
noncomputable def ghz5 : EuclideanSpace ℂ (Fin 5 → Bool) :=
  WithLp.toLp 2 (fun b =>
    if b = (fun _ => false) ∨ b = (fun _ => true) then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- The 5-qubit GHZ state is a unit vector. -/
theorem ghz5_normalized : ‖ghz5‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hne : ¬ ((fun _ => false : Fin 5 → Bool) = (fun _ => true)) := by
    intro hc; simpa using congrFun hc 0
  have h : ∀ b : Fin 5 → Bool, ‖ghz5.ofLp b‖ ^ 2
      = (if b = (fun _ => false) then (1/2 : ℝ) else 0)
        + (if b = (fun _ => true) then (1/2 : ℝ) else 0) := by
    intro b
    by_cases h0 : b = (fun _ => false) <;> by_cases h1 : b = (fun _ => true) <;>
      simp [ghz5, h0, h1, hne, Ne.symm hne, Complex.norm_real, Real.sq_sqrt]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
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

