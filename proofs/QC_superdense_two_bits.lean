import Mathlib

/-!
# Superdense Two Bits
Category: Quantum Computing
Target: QC.superdense_two_bits
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

set_option grind.warning false

namespace QC

/-- A two-qubit pure state is a vector of amplitudes indexed by the computational
basis `|ij⟩`, `i j : Fin 2`. -/
abbrev TwoQubit : Type := Fin 2 × Fin 2 → ℂ

/-- The Bell state `Φ⁺ = (|00⟩ + |11⟩)/√2`, shared by Alice (first qubit) and Bob
(second qubit) before the protocol starts. -/
noncomputable def bell : TwoQubit :=
  fun p => if p.1 = p.2 then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0

/-- Action of a one-qubit gate `M` on the *first* tensor factor, i.e. `M ⊗ I`.
This is exactly the set of operations Alice can perform locally on her qubit. -/
noncomputable def applyFirst (M : Matrix (Fin 2) (Fin 2) ℂ) (v : TwoQubit) : TwoQubit :=
  fun p => ∑ k : Fin 2, M p.1 k * v (k, p.2)

/-- The Pauli `X` (bit flip) gate. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The Pauli `Z` (phase flip) gate. -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- Alice's encoding gate for the two classical bits `m = (a, b)`: she applies `Z`
iff `a = 1` and then `X` iff `b = 1`, i.e. the gate `X^b Z^a`. -/
noncomputable def encodeOp (m : Fin 2 × Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  (if m.2 = 1 then pauliX else 1) * (if m.1 = 1 then pauliZ else 1)

/-- Superdense coding: to send the two classical bits `m = (a, b)`, Alice applies
`X^b Z^a` to her half of the shared Bell pair and sends that single qubit to Bob.
`encode m` is the resulting two-qubit state held by Bob. -/
noncomputable def encode (m : Fin 2 × Fin 2) : TwoQubit := applyFirst (encodeOp m) bell

private theorem sqrt_two_inv_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ ≠ 0 := by
  simp

/-- **Superdense coding transmits two classical bits.**
The four states Bob ends up holding, one for each of the four possible two-bit
messages, are pairwise distinct: the encoding
`m ↦ (X^{m.2} Z^{m.1} ⊗ I) Φ⁺` is injective on the four messages, so Bob can
recover both classical bits from the single qubit he receives. -/
theorem superdense_two_bits : Function.Injective encode := by
  have hs := sqrt_two_inv_ne_zero
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h00 := congrFun h (0, 0)
  have h11 := congrFun h (1, 1)
  have h01 := congrFun h (0, 1)
  clear h
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  all_goals (try (simp [encode, applyFirst, encodeOp, bell, Fin.sum_univ_two, Matrix.mul_apply,
      pauliX, pauliZ] at h00))
  all_goals (try (simp [encode, applyFirst, encodeOp, bell, Fin.sum_univ_two, Matrix.mul_apply,
      pauliX, pauliZ] at h11))
  all_goals (try (simp [encode, applyFirst, encodeOp, bell, Fin.sum_univ_two, Matrix.mul_apply,
      pauliX, pauliZ] at h01))
  all_goals (try rfl)
  all_goals
    (apply hs
     first
       | linear_combination h11 / 2
       | linear_combination -h11 / 2
       | linear_combination h01 / 2
       | linear_combination -h01 / 2)

end QC

