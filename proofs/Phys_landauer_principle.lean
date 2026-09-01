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
# Landauer Principle
Category: Frontier Phys
Target: Phys.landauer_principle
Statement: Erasing one bit dissipates at least kT ln 2 of heat (Landauer).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace Phys

open Finset

/-- Gibbs/Shannon entropy `S(p) = -k ∑ᵢ pᵢ log pᵢ` of a probability distribution `p`
on a finite state space, measured with Boltzmann constant `k`
(the convention `0 * log 0 = 0` is automatic since `Real.log 0 = 0`). -/
noncomputable def entropy (k : ℝ) {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  -k * ∑ i, p i * Real.log (p i)

/-- The state of one unknown bit: the uniform distribution on two states. -/
noncomputable def bitUniform : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- The state of an erased bit: the deterministic distribution concentrated on state `0`. -/
noncomputable def bitErased : Fin 2 → ℝ := ![1, 0]

/-- The entropy of one unknown bit is `k log 2`. -/
theorem entropy_bitUniform (k : ℝ) : entropy k bitUniform = k * Real.log 2 := by
  simp [entropy, bitUniform, Fin.sum_univ_two]
  ring

/-- The entropy of an erased (deterministic) bit is zero. -/
theorem entropy_bitErased (k : ℝ) : entropy k bitErased = 0 := by
  simp [entropy, bitErased, Fin.sum_univ_two]

/--
**Landauer's principle.**

A logically irreversible erasure takes one bit from the unknown state `bitUniform`
(entropy `k log 2`) to the erased state `bitErased` (entropy `0`).  If the erasure is
carried out in contact with a heat bath at absolute temperature `T > 0`, into which an
amount of heat `Q` is dissipated, the bath's entropy increases by `Q / T`, and the second
law of thermodynamics says the total entropy of system plus bath cannot decrease:

  `0 ≤ Q / T + (S_final - S_initial)`.

Then the dissipated heat is at least `k T log 2`.
-/
theorem landauer_principle (k T Q : ℝ) (hT : 0 < T)
    (hSecondLaw : 0 ≤ Q / T + (entropy k bitErased - entropy k bitUniform)) :
    k * T * Real.log 2 ≤ Q := by
  rw [entropy_bitErased, entropy_bitUniform] at hSecondLaw
  have h : k * Real.log 2 ≤ Q / T := by linarith
  calc k * T * Real.log 2 = (k * Real.log 2) * T := by ring
    _ ≤ (Q / T) * T := by nlinarith
    _ = Q := by field_simp

#print axioms Phys.landauer_principle

end Phys

