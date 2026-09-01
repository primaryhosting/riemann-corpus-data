import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QC

/-- The one-qubit state space `ℂ²`, a finite-dimensional complex Hilbert space. -/
abbrev H : Type := EuclideanSpace ℂ (Fin 2)

/-- The two-qubit state space `ℂ² ⊗ ℂ²`, realised as `ℂ^(Fin 2 × Fin 2)`. -/
abbrev HH : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor product `x ⊗ y` of two vectors of `H`, viewed inside `HH`. -/
def tens (x y : H) : HH := WithLp.toLp 2 (fun p : Fin 2 × Fin 2 => x.ofLp p.1 * y.ofLp p.2)

@[simp] lemma tens_apply (x y : H) (p : Fin 2 × Fin 2) :
    (tens x y).ofLp p = x.ofLp p.1 * y.ofLp p.2 := rfl

/-- The inner product of tensors factors as the product of the inner products. -/
lemma inner_tens (x y z w : H) :
    ⟪tens x y, tens z w⟫_ℂ = ⟪x, z⟫_ℂ * ⟪y, w⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, tens_apply, Fintype.sum_prod_type,
    map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The "blank" state `|0⟩`. -/
noncomputable def e0 : H := EuclideanSpace.single 0 (1 : ℂ)

/-- A second unit vector, `(3/5)|0⟩ + (4/5)|1⟩`. -/
noncomputable def psi : H := WithLp.toLp 2 ![(3 / 5 : ℂ), (4 / 5 : ℂ)]

lemma inner_e0_e0 : ⟪e0, e0⟫_ℂ = 1 := by
  simp [e0]

lemma inner_e0_psi : ⟪e0, psi⟫_ℂ = 3 / 5 := by
  simp [e0, psi, PiLp.inner_apply, RCLike.inner_apply, EuclideanSpace.single_apply]

lemma norm_e0 : ‖e0‖ = 1 := by
  simp [e0, EuclideanSpace.norm_single]

lemma norm_psi : ‖psi‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  simp [psi, Fin.sum_univ_two]
  norm_num

/-- **No-cloning theorem.**  There is no unitary `U` on `H ⊗ H` with
`U (|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` for every state (unit vector) `|ψ⟩`. -/
theorem no_cloning :
    ¬ ∃ U : HH ≃ₗᵢ[ℂ] HH, ∀ x : H, ‖x‖ = 1 → U (tens x e0) = tens x x := by
  rintro ⟨U, hU⟩
  have key : ⟪tens e0 e0, tens psi e0⟫_ℂ = ⟪tens e0 e0, tens psi psi⟫_ℂ := by
    calc ⟪tens e0 e0, tens psi e0⟫_ℂ
        = ⟪U (tens e0 e0), U (tens psi e0)⟫_ℂ := (U.inner_map_map _ _).symm
      _ = ⟪tens e0 e0, tens psi psi⟫_ℂ := by
          rw [hU e0 norm_e0, hU psi norm_psi]
  rw [inner_tens, inner_tens, inner_e0_e0, inner_e0_psi] at key
  norm_num at key

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

