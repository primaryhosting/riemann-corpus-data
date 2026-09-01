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

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- Bit flip on a qubit index. -/
def bitFlip (i : Fin 2) : Fin 2 := i + 1

/-- The Bell basis state `β_{m n}` as an amplitude function on two qubits:
`β_{m n} = (|0, n⟩ + (-1)^m |1, n ⊕ 1⟩)/√2`. -/
noncomputable def bell (m n : Fin 2) : Fin 2 → Fin 2 → ℂ := fun i j =>
  if i = 0 then (if j = n then (1 / (Real.sqrt 2 : ℝ) : ℂ) else 0)
  else (if j = bitFlip n then ((-1 : ℂ) ^ (m : ℕ) / ((Real.sqrt 2 : ℝ) : ℂ)) else 0)

/-- The three–qubit input state of the teleportation protocol:
the unknown qubit `psi` tensored with the Bell pair `(|00⟩ + |11⟩)/√2`. -/
noncomputable def teleportInput (psi : Fin 2 → ℂ) : Fin 2 → Fin 2 → Fin 2 → ℂ :=
  fun i j k => psi i * (if j = k then (1 / (Real.sqrt 2 : ℝ) : ℂ) else 0)

/-- Bob's (unnormalized) qubit after Alice measures qubits 1,2 in the Bell basis
and obtains the outcome `(m, n)`. -/
noncomputable def bobState (psi : Fin 2 → ℂ) (m n : Fin 2) : Fin 2 → ℂ := fun k =>
  ∑ i : Fin 2, ∑ j : Fin 2, (starRingEnd ℂ) (bell m n i j) * teleportInput psi i j k

/-- Pauli `X` acting on a qubit amplitude vector. -/
def pauliX (v : Fin 2 → ℂ) : Fin 2 → ℂ := fun k => v (bitFlip k)

/-- Pauli `Z` acting on a qubit amplitude vector. -/
def pauliZ (v : Fin 2 → ℂ) : Fin 2 → ℂ := fun k => (-1 : ℂ) ^ (k : ℕ) * v k

/-- Bob's correction unitary `Z^m X^n` for the measurement outcome `(m, n)`. -/
def correction (m n : Fin 2) (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  (if m = 1 then pauliZ else id) ((if n = 1 then pauliX else id) v)

/-- **Teleportation identity.** For every measurement outcome `(m, n)`, applying the
correction `Z^m X^n` to Bob's post-measurement state (renormalized by the factor `2`,
i.e. `1/‖·‖` for the outcome probability `1/4`) returns exactly the input qubit `psi`. -/
theorem teleportation_identity (psi : Fin 2 → ℂ) (m n : Fin 2) :
    correction m n (fun k => 2 * bobState psi m n k) = psi := by
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  funext k
  fin_cases m <;> fin_cases n <;> fin_cases k <;>
    simp [correction, bobState, bell, teleportInput, pauliX, pauliZ, bitFlip,
      Fin.sum_univ_two] <;>
    field_simp <;>
    rw [sq, hsq]

end QC

