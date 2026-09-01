import Mathlib

/-!
# The no-cloning theorem

We model a single qubit by `Qubit := EuclideanSpace ℂ (Fin 2)` and the two-qubit
space `H ⊗ H` by `TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)`, with the tensor
product of vectors given coordinatewise by `Qubit.tens`.

A *unitary* operator on the two-qubit space is a surjective linear isometry, i.e. a
term of type `TwoQubit ≃ₗᵢ[ℂ] TwoQubit`.

The main result `QC.no_cloning` states that for every "blank" vector `blank` and every
unitary `U` there is a state `ψ` (a unit vector) with `U (ψ ⊗ blank) ≠ ψ ⊗ ψ`.
-/

namespace QC

/-- The state space of one qubit. -/
abbrev Qubit := EuclideanSpace ℂ (Fin 2)

/-- The state space of two qubits, i.e. `Qubit ⊗ Qubit`. -/
abbrev TwoQubit := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product `|ψ⟩ ⊗ |φ⟩` of two qubit states. -/
noncomputable def tens (ψ φ : Qubit) : TwoQubit :=
  WithLp.toLp 2 (fun p : Fin 2 × Fin 2 => ψ.ofLp p.1 * φ.ofLp p.2)

@[simp] lemma tens_apply (ψ φ : Qubit) (p : Fin 2 × Fin 2) :
    (tens ψ φ).ofLp p = ψ.ofLp p.1 * φ.ofLp p.2 := rfl

lemma tens_add_left (ψ ψ' φ : Qubit) : tens (ψ + ψ') φ = tens ψ φ + tens ψ' φ := by
  ext p
  simp [tens, add_mul]

lemma tens_smul_left (c : ℂ) (ψ φ : Qubit) : tens (c • ψ) φ = c • tens ψ φ := by
  ext p
  simp [tens, mul_assoc]

/-- The computational basis state `|0⟩`. -/
noncomputable def e0 : Qubit := EuclideanSpace.single 0 1

/-- The computational basis state `|1⟩`. -/
noncomputable def e1 : Qubit := EuclideanSpace.single 1 1

lemma norm_e0 : ‖e0‖ = 1 := by simp [e0]

lemma norm_e1 : ‖e1‖ = 1 := by simp [e1]

lemma norm_e0_add_e1 : ‖e0 + e1‖ = Real.sqrt 2 := by
  rw [EuclideanSpace.norm_eq]
  norm_num [e0, e1, Fin.sum_univ_two, EuclideanSpace.single_apply]

/-- The uniform superposition `(|0⟩ + |1⟩)/√2`. -/
noncomputable def plus : Qubit := ((Real.sqrt 2 : ℂ))⁻¹ • (e0 + e1)

lemma norm_plus : ‖plus‖ = 1 := by
  rw [plus, norm_smul, norm_e0_add_e1]
  simp [abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- **No-cloning theorem**: there is no unitary `U` on `H ⊗ H` which, for a fixed blank
state `blank`, maps `|ψ⟩ ⊗ |blank⟩` to `|ψ⟩ ⊗ |ψ⟩` for every state `|ψ⟩`. -/
theorem no_cloning (blank : Qubit) :
    ¬ ∃ U : TwoQubit ≃ₗᵢ[ℂ] TwoQubit, ∀ ψ : Qubit, ‖ψ‖ = 1 → U (tens ψ blank) = tens ψ ψ := by
  rintro ⟨U, h⟩
  have h0 := h e0 norm_e0
  have h1 := h e1 norm_e1
  have hp := h plus norm_plus
  -- expand the left-hand side by linearity
  have hlin : U (tens plus blank)
      = ((Real.sqrt 2 : ℂ))⁻¹ • (tens e0 e0 + tens e1 e1) := by
    rw [plus, tens_smul_left, tens_add_left, map_smul, map_add, h0, h1]
  rw [hp] at hlin
  -- compare the coordinate `(0, 1)`
  have hco := congrArg (fun x : TwoQubit => x.ofLp (0, 1)) hlin
  simp only [tens_apply, PiLp.smul_apply, smul_eq_mul] at hco
  rw [plus] at hco
  simp only [PiLp.smul_apply, PiLp.add_apply, smul_eq_mul, e0, e1,
    EuclideanSpace.single_apply] at hco
  norm_num at hco

#print axioms QC.no_cloning

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

