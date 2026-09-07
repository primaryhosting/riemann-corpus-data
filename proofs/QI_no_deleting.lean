import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Formalization notes.

We model a single qubit as `EuclideanSpace ℂ (Fin 2)` and a pair of qubits as
`EuclideanSpace ℂ (Fin 2 × Fin 2)`, with `QI.tens a b` the product (tensor) state
`(i, j) ↦ a i * b j`.

The no-deleting theorem states that there is no unitary `U` on the two-qubit system
which maps `ψ ⊗ ψ` to `ψ ⊗ |0⟩` for every (unknown) unit vector `ψ`; i.e. no unitary
can delete one of two identical copies of an arbitrary state.

The proof: a unitary preserves inner products, and `⟪ψ ⊗ ψ, φ ⊗ φ⟫ = ⟪ψ, φ⟫ ^ 2`
while `⟪ψ ⊗ |0⟩, φ ⊗ |0⟩⟫ = ⟪ψ, φ⟫`, so we would need `c ^ 2 = c` for the overlap `c`
of any two unit vectors. Taking `ψ = |0⟩` and `φ = (3/5) |0⟩ + (4/5) |1⟩` gives
`c = 3/5`, and `9/25 ≠ 3/5`.
-/

open scoped InnerProductSpace

namespace QI

/-- The product (tensor) state of two qubits, `(i, j) ↦ a i * b j`. -/
noncomputable def tens (a b : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2 × Fin 2) :=
  (WithLp.equiv 2 _).symm fun p => a p.1 * b p.2

/-- The computational basis state `|0⟩`. -/
noncomputable def ket0 : EuclideanSpace ℂ (Fin 2) := (WithLp.equiv 2 _).symm ![1, 0]

/-- The unit vector `(3/5) |0⟩ + (4/5) |1⟩`. -/
noncomputable def ketPhi : EuclideanSpace ℂ (Fin 2) := (WithLp.equiv 2 _).symm ![3 / 5, 4 / 5]

lemma inner_tens (a b c d : EuclideanSpace ℂ (Fin 2)) :
    ⟪tens a b, tens c d⟫_ℂ = ⟪a, c⟫_ℂ * ⟪b, d⟫_ℂ := by
  simp [tens, PiLp.inner_apply, RCLike.inner_apply, Fintype.sum_prod_type, Fin.sum_univ_succ]
  ring

lemma norm_ket0 : ‖ket0‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [ket0, Fin.sum_univ_succ]

lemma norm_ketPhi : ‖ketPhi‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [ketPhi, Fin.sum_univ_succ, Complex.norm_def, Complex.normSq]

lemma inner_ket0_ket0 : ⟪ket0, ket0⟫_ℂ = 1 := by
  rw [PiLp.inner_apply]
  norm_num [ket0, RCLike.inner_apply, Fin.sum_univ_succ]

lemma inner_ket0_ketPhi : ⟪ket0, ketPhi⟫_ℂ = 3 / 5 := by
  rw [PiLp.inner_apply]
  norm_num [ket0, ketPhi, RCLike.inner_apply, Fin.sum_univ_succ]

/-- **No-deleting theorem.** There is no unitary operator on two qubits that deletes one of
two identical copies of an unknown quantum state: no unitary `U` satisfies
`U (ψ ⊗ ψ) = ψ ⊗ |0⟩` for every unit vector `ψ`. -/
theorem no_deleting :
    ¬ ∃ U : EuclideanSpace ℂ (Fin 2 × Fin 2) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2 × Fin 2),
      ∀ ψ : EuclideanSpace ℂ (Fin 2), ‖ψ‖ = 1 → U (tens ψ ψ) = tens ψ ket0 := by
  rintro ⟨U, hU⟩
  have key : ⟪tens ket0 ket0, tens ketPhi ketPhi⟫_ℂ
      = ⟪tens ket0 ket0, tens ketPhi ket0⟫_ℂ := by
    have h0 := hU ket0 norm_ket0
    have h1 := hU ketPhi norm_ketPhi
    calc ⟪tens ket0 ket0, tens ketPhi ketPhi⟫_ℂ
        = ⟪U (tens ket0 ket0), U (tens ketPhi ketPhi)⟫_ℂ := (U.inner_map_map _ _).symm
      _ = ⟪tens ket0 ket0, tens ketPhi ket0⟫_ℂ := by rw [h0, h1]
  rw [inner_tens, inner_tens, inner_ket0_ket0, inner_ket0_ketPhi] at key
  norm_num at key

end QI

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

