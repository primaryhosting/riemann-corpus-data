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

open scoped TensorProduct

/-- A single qubit space `ℂ²`, with its standard inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit space `ℂ² ⊗ ℂ²`, with the inner product determined by
`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`. -/
abbrev TwoQubit : Type := Qubit ⊗[ℂ] Qubit

/-- The computational basis states `|0⟩` and `|1⟩` of a qubit. -/
noncomputable def ket (i : Fin 2) : Qubit := EuclideanSpace.single i 1

lemma inner_ket (i j : Fin 2) :
    inner ℂ (ket i) (ket j) = if i = j then (1 : ℂ) else 0 := by
  simp [ket, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

/-- Restatement of `inner_smul_left` for `TwoQubit`, phrased with the scalar action that
elaboration picks for the tensor product (so that `simp` can use it). -/
lemma inner_smul_left' (r : ℂ) (x y : TwoQubit) :
    inner ℂ (r • x) y = (starRingEnd ℂ) r * inner ℂ x y := inner_smul_left x y r

/-- Restatement of `inner_smul_right` for `TwoQubit`. -/
lemma inner_smul_right' (r : ℂ) (x y : TwoQubit) :
    inner ℂ x (r • y) = r * inner ℂ x y := inner_smul_right x y r

/-- The four Bell states
`Φ⁺ = (|00⟩+|11⟩)/√2`, `Φ⁻ = (|00⟩-|11⟩)/√2`,
`Ψ⁺ = (|01⟩+|10⟩)/√2`, `Ψ⁻ = (|01⟩-|10⟩)/√2`. -/
noncomputable def bell : Fin 4 → TwoQubit
  | 0 => ((Real.sqrt 2)⁻¹ : ℂ) • (ket 0 ⊗ₜ[ℂ] ket 0 + ket 1 ⊗ₜ[ℂ] ket 1)
  | 1 => ((Real.sqrt 2)⁻¹ : ℂ) • (ket 0 ⊗ₜ[ℂ] ket 0 - ket 1 ⊗ₜ[ℂ] ket 1)
  | 2 => ((Real.sqrt 2)⁻¹ : ℂ) • (ket 0 ⊗ₜ[ℂ] ket 1 + ket 1 ⊗ₜ[ℂ] ket 0)
  | 3 => ((Real.sqrt 2)⁻¹ : ℂ) • (ket 0 ⊗ₜ[ℂ] ket 1 - ket 1 ⊗ₜ[ℂ] ket 0)

lemma inner_bell (i j : Fin 4) :
    inner ℂ (bell i) (bell j) = if i = j then (1 : ℂ) else 0 := by
  have hsq2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hsq2; simp at hsq2
  fin_cases i <;> fin_cases j <;>
    simp only [bell, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left', inner_smul_right', TensorProduct.inner_tmul, inner_ket,
      Complex.conj_ofReal, map_inv₀] <;>
    norm_num <;>
    field_simp <;>
    simp only [hsq2] <;>
    ring

lemma finrank_twoQubit : Module.finrank ℂ TwoQubit = 4 := by
  simp [Module.finrank_tensorProduct]

/-- **The four Bell states form an orthonormal basis of `ℂ² ⊗ ℂ²`.** -/
theorem bell_orthonormal :
    Orthonormal ℂ bell ∧ Submodule.span ℂ (Set.range bell) = ⊤ := by
  have ho : Orthonormal ℂ bell := orthonormal_iff_ite.2 inner_bell
  refine ⟨ho, ?_⟩
  have hcard : Fintype.card (Fin 4) = Module.finrank ℂ TwoQubit := by
    simp
  have := (basisOfOrthonormalOfCardEqFinrank ho hcard).span_eq
  rwa [coe_basisOfOrthonormalOfCardEqFinrank] at this

/-- The orthonormal basis of `ℂ² ⊗ ℂ²` given by the four Bell states. -/
noncomputable def bellBasis : OrthonormalBasis (Fin 4) ℂ TwoQubit :=
  (basisOfOrthonormalOfCardEqFinrank bell_orthonormal.1
      (by simp)).toOrthonormalBasis
    (by rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact bell_orthonormal.1)

@[simp] lemma coe_bellBasis : ⇑bellBasis = bell := by
  simp [bellBasis, Module.Basis.coe_toOrthonormalBasis, coe_basisOfOrthonormalOfCardEqFinrank]

end QC

#print axioms QC.bell_orthonormal
#print axioms QC.coe_bellBasis

