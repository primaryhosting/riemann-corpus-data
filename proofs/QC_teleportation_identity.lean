/-
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
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

namespace QC

open Complex Finset

/-- The scalar `1/√2`, the normalization constant of the Bell states. -/
noncomputable def invSqrt2 : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma invSqrt2_sq : invSqrt2 * invSqrt2 = 1 / 2 := by
  have h : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = (2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [invSqrt2, ← mul_inv, h]
  norm_num

lemma conj_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2, ← Complex.ofReal_inv]

/-- The sign `(-1)^(a·i)` appearing in the Bell states and in the Pauli `Z` correction. -/
def sgn (a i : Bool) : ℂ := if a && i then -1 else 1

/-- The four Bell states `B a b`, indexed by two classical bits `a` (phase) and `b` (parity):
`B a b i j = (-1)^(a·i)/√2` if `j = i ⊕ b`, and `0` otherwise.
Thus `B false false = (|00⟩+|11⟩)/√2`, `B false true = (|01⟩+|10⟩)/√2`,
`B true false = (|00⟩-|11⟩)/√2`, `B true true = (|01⟩-|10⟩)/√2`. -/
noncomputable def bell (a b i j : Bool) : ℂ := if j = xor i b then invSqrt2 * sgn a i else 0

/-- The four Bell states form an orthonormal basis of the two-qubit space, so the Bell
measurement used in the protocol is a genuine projective measurement. -/
lemma bell_orthonormal (a b a' b' : Bool) :
    ∑ i : Bool, ∑ j : Bool, (starRingEnd ℂ) (bell a b i j) * bell a' b' i j =
      if a = a' ∧ b = b' then 1 else 0 := by
  have h2 : invSqrt2 * invSqrt2 = 1 / 2 := invSqrt2_sq
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp [bell, sgn, conj_invSqrt2, h2] <;>
    ring_nf

/-- The initial three-qubit state `|ψ⟩ ⊗ |Φ⁺⟩`: Alice holds qubits 1 and 2, Bob holds qubit 3. -/
noncomputable def inputState (psi : Bool → ℂ) (i j k : Bool) : ℂ :=
  psi i * bell false false j k

/-- Bob's (normalized) state after Alice measures qubits 1,2 in the Bell basis and obtains the
outcome `(a, b)`. The amplitude of each outcome is `1/2`, so the projection is rescaled by `2`. -/
noncomputable def postMeasure (psi : Bool → ℂ) (a b : Bool) (k : Bool) : ℂ :=
  2 * ∑ i : Bool, ∑ j : Bool, (starRingEnd ℂ) (bell a b i j) * inputState psi i j k

/-- Bob's correction, applying the Pauli operator `Z^a X^b` to his qubit. -/
noncomputable def correct (a b : Bool) (phi : Bool → ℂ) (k : Bool) : ℂ :=
  sgn a k * phi (xor k b)

/-- **Teleportation identity.** For every input qubit state `ψ` and every Bell-measurement
outcome `(a, b)`, applying the Pauli correction `Z^a X^b` to Bob's post-measurement state
returns exactly the input state `ψ`. -/
theorem teleportation_identity (psi : Bool → ℂ) (a b k : Bool) :
    correct a b (postMeasure psi a b) k = psi k := by
  have h2 : invSqrt2 * invSqrt2 = 1 / 2 := invSqrt2_sq
  cases a <;> cases b <;> cases k <;>
    simp [correct, postMeasure, inputState, bell, sgn, conj_invSqrt2,
      Bool.xor_comm, mul_comm, mul_left_comm, mul_assoc] <;>
    ring_nf <;>
    rw [show invSqrt2 ^ 2 = invSqrt2 * invSqrt2 from (sq invSqrt2), h2] <;>
    ring

end QC

