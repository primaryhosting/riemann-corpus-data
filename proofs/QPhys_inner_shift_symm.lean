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
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value of an observable `A` in the state `ψ`, i.e. the real part of
`⟪ψ, A ψ⟫` (which is automatically real for a symmetric `A` and a unit vector `ψ`). -/
noncomputable def expectation (A : H →ₗ[ℂ] H) (ψ : H) : ℝ := (⟪ψ, A ψ⟫_ℂ).re

/-- The uncertainty (standard deviation) of an observable `A` in the state `ψ`:
`Δ A = ‖(A - ⟨A⟩) ψ‖`. -/
noncomputable def uncertainty (A : H →ₗ[ℂ] H) (ψ : H) : ℝ :=
  ‖A ψ - (expectation A ψ : ℂ) • ψ‖

/-- For a symmetric operator `A`, a real scalar `a` and any vectors `ψ, v`,
`⟪A ψ - a • ψ, v⟫ = ⟪ψ, A v - a • v⟫`. -/
lemma inner_shift_symm {A : H →ₗ[ℂ] H} (hA : ∀ u v : H, ⟪A u, v⟫_ℂ = ⟪u, A v⟫_ℂ)
    (a : ℝ) (ψ v : H) :
    ⟪A ψ - (a : ℂ) • ψ, v⟫_ℂ = ⟪ψ, A v - (a : ℂ) • v⟫_ℂ := by
  rw [inner_sub_left, inner_sub_right, hA, inner_smul_left, inner_smul_right]
  simp [Complex.conj_ofReal]

/-- Version of the uncertainty relation with arbitrary real reference points `a`, `b`
in place of the expectation values. -/
lemma heisenberg_uncertainty_shift (X P : H →ₗ[ℂ] H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (ψ : H) (hψ : ‖ψ‖ = 1) (ℏ a b : ℝ)
    (hcomm : X (P ψ) - P (X ψ) = (Complex.I * ℏ) • ψ) :
    ℏ / 2 ≤ ‖X ψ - (a : ℂ) • ψ‖ * ‖P ψ - (b : ℂ) • ψ‖ := by
  obtain ⟨u, hu⟩ : ∃ u : H, u = X ψ - (a : ℂ) • ψ := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : H, v = P ψ - (b : ℂ) • ψ := ⟨_, rfl⟩
  have h1 : ⟪u, v⟫_ℂ = ⟪ψ, X v - (a : ℂ) • v⟫_ℂ := by rw [hu]; exact inner_shift_symm hX a ψ v
  have h2 : ⟪v, u⟫_ℂ = ⟪ψ, P u - (b : ℂ) • u⟫_ℂ := by rw [hv]; exact inner_shift_symm hP b ψ u
  have h3 : (X v - (a : ℂ) • v) - (P u - (b : ℂ) • u) = (Complex.I * ℏ) • ψ := by
    rw [← hcomm, hu, hv, map_sub, map_smul, map_sub, map_smul]
    module
  have h4 : ⟪ψ, ψ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  have hkey : ⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ = Complex.I * ℏ := by
    have h5 : ⟪ψ, (X v - (a : ℂ) • v) - (P u - (b : ℂ) • u)⟫_ℂ
        = ⟪ψ, X v - (a : ℂ) • v⟫_ℂ - ⟪ψ, P u - (b : ℂ) • u⟫_ℂ := inner_sub_right _ _ _
    rw [h1, h2, ← h5, h3, inner_smul_right, h4, mul_one]
  have hconj : ⟪v, u⟫_ℂ = (starRingEnd ℂ) ⟪u, v⟫_ℂ := (inner_conj_symm (𝕜 := ℂ) v u).symm
  have habs : |ℏ| ≤ 2 * (‖u‖ * ‖v‖) := by
    have h6 : ‖⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ‖ = |ℏ| := by
      rw [hkey]
      simp
    have h7 : ‖⟪u, v⟫_ℂ - ⟪v, u⟫_ℂ‖ ≤ ‖⟪u, v⟫_ℂ‖ + ‖⟪v, u⟫_ℂ‖ := norm_sub_le _ _
    have h8 : ‖⟪v, u⟫_ℂ‖ = ‖⟪u, v⟫_ℂ‖ := by rw [hconj, RCLike.norm_conj]
    have h9 : ‖⟪u, v⟫_ℂ‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
    rw [h6] at h7
    linarith
  have h10 : ℏ ≤ |ℏ| := le_abs_self ℏ
  rw [← hu, ← hv]
  linarith

/-- **Heisenberg uncertainty principle.**  If `X` and `P` are symmetric operators on a
complex inner product space, `ψ` is a normalized state, and the canonical commutation
relation `[X, P] ψ = i ℏ ψ` holds, then `Δx · Δp ≥ ℏ / 2`. -/
theorem heisenberg_uncertainty (X P : H →ₗ[ℂ] H)
    (hX : ∀ u v : H, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : H, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (ψ : H) (hψ : ‖ψ‖ = 1) (ℏ : ℝ)
    (hcomm : X (P ψ) - P (X ψ) = (Complex.I * ℏ) • ψ) :
    uncertainty X ψ * uncertainty P ψ ≥ ℏ / 2 :=
  heisenberg_uncertainty_shift X P hX hP ψ hψ ℏ (expectation X ψ) (expectation P ψ) hcomm

end QPhys

