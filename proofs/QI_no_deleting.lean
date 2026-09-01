/-
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# No Deleting
Category: Frontier Qi
Target: QI.no_deleting
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

namespace QI

open scoped TensorProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `IsDeleter U blank` says that the linear isometry `U` of the two-copy space `H ⊗ H`
deletes one of two identical copies of an *arbitrary* (unknown) pure state `u`, replacing
it by the fixed "blank" state `blank`. -/
def IsDeleter (U : H ⊗[ℂ] H →ₗᵢ[ℂ] H ⊗[ℂ] H) (blank : H) : Prop :=
  ∀ u : H, ‖u‖ = 1 → U (u ⊗ₜ[ℂ] u) = u ⊗ₜ[ℂ] blank

/-- The blank state of a deleter is a unit vector (provided some unit vector exists). -/
theorem norm_blank_eq_one {U : H ⊗[ℂ] H →ₗᵢ[ℂ] H ⊗[ℂ] H} {blank : H}
    (hU : IsDeleter U blank) {u : H} (hu : ‖u‖ = 1) : ‖blank‖ = 1 := by
  have h : ‖U (u ⊗ₜ[ℂ] u)‖ = ‖u ⊗ₜ[ℂ] blank‖ := by rw [hU u hu]
  rw [U.norm_map] at h
  simpa [TensorProduct.norm_tmul, hu, eq_comm] using h

/-- **Key lemma.** If a deleter exists, then the overlap of any two unit states is an
idempotent complex number: `⟪u, v⟫ ^ 2 = ⟪u, v⟫`, hence is `0` or `1`. -/
theorem inner_sq_eq_inner_of_isDeleter {U : H ⊗[ℂ] H →ₗᵢ[ℂ] H ⊗[ℂ] H} {blank : H}
    (hU : IsDeleter U blank) {u v : H} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (inner ℂ u v) ^ 2 = inner ℂ u v := by
  have hb : ‖blank‖ = 1 := norm_blank_eq_one hU hu
  have hbb : (inner ℂ blank blank : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hb]; norm_num
  have h1 : (inner ℂ (U (u ⊗ₜ[ℂ] u)) (U (v ⊗ₜ[ℂ] v)) : ℂ)
      = inner ℂ (u ⊗ₜ[ℂ] u) (v ⊗ₜ[ℂ] v) := U.inner_map_map _ _
  rw [hU u hu, hU v hv, TensorProduct.inner_tmul, TensorProduct.inner_tmul, hbb] at h1
  rw [sq]
  exact h1.symm.trans (mul_one _)

/-- In a space of dimension at least two there are unit vectors with overlap `3/5`. -/
theorem exists_unit_pair_inner_eq (hdim : (2 : Cardinal) ≤ Module.rank ℂ H) :
    ∃ u v : H, ‖u‖ = 1 ∧ ‖v‖ = 1 ∧ inner ℂ u v = (3 / 5 : ℂ) := by
  obtain ⟨f, hf⟩ :=
    exists_linearIndependent_of_le_rank (R := ℂ) (M := H) (n := 2) (by exact_mod_cast hdim)
  set e : Fin 2 → H := InnerProductSpace.gramSchmidtNormed ℂ f with he
  have ho : Orthonormal ℂ e := InnerProductSpace.gramSchmidtNormed_orthonormal hf
  have key : ∀ i j : Fin 2, (inner ℂ (e i) (e j) : ℂ) = if i = j then (1 : ℂ) else 0 :=
    orthonormal_iff_ite.mp ho
  refine ⟨e 0, (3 / 5 : ℂ) • e 0 + (4 / 5 : ℂ) • e 1, ho.1 0, ?_, ?_⟩
  · have hself : (inner ℂ ((3 / 5 : ℂ) • e 0 + (4 / 5 : ℂ) • e 1)
        ((3 / 5 : ℂ) • e 0 + (4 / 5 : ℂ) • e 1) : ℂ) = 1 := by
      simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, key,
        map_div₀, Complex.conj_ofNat]
      norm_num
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at hself
    have : ‖(3 / 5 : ℂ) • e 0 + (4 / 5 : ℂ) • e 1‖ ^ 2 = 1 := by exact_mod_cast hself
    nlinarith [norm_nonneg ((3 / 5 : ℂ) • e 0 + (4 / 5 : ℂ) • e 1)]
  · simp only [inner_add_right, inner_smul_right, key]
    norm_num

/-- **No-deleting theorem.**  In any complex inner product space of dimension at least two
there is no linear isometry (in particular, no unitary) of the two-copy space `H ⊗ H` that
maps `u ⊗ u` to `u ⊗ blank` for every unit vector `u` and a fixed blank state: an unknown
quantum state cannot be deleted. -/
theorem no_deleting (hdim : (2 : Cardinal) ≤ Module.rank ℂ H) :
    ¬ ∃ (U : H ⊗[ℂ] H →ₗᵢ[ℂ] H ⊗[ℂ] H) (blank : H), IsDeleter U blank := by
  rintro ⟨U, blank, hU⟩
  obtain ⟨u, v, hu, hv, hinner⟩ := exists_unit_pair_inner_eq (H := H) hdim
  have h := inner_sq_eq_inner_of_isDeleter hU hu hv
  rw [hinner] at h
  norm_num at h

end QI

