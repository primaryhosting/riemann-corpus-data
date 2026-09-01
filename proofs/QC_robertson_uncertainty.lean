import Mathlib

/-!
# Robertson Uncertainty
Category: Quantum Computing
Target: QC.robertson_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The expectation value of a symmetric operator in a unit state is real. -/
lemma expectation_conj (A : H →ₗ[ℂ] H) (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ) (ψ : H) :
    (starRingEnd ℂ) ⟪ψ, A ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := by
  rw [← inner_conj_symm (𝕜 := ℂ) (x := ψ) (y := A ψ)]
  simp [hA ψ ψ]

/-- The inner product of the two centered vectors. -/
lemma inner_centered (A B : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    ⟪A ψ - ⟪ψ, A ψ⟫_ℂ • ψ, B ψ - ⟪ψ, B ψ⟫_ℂ • ψ⟫_ℂ
      = ⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, A ψ⟫_ℂ * ⟪ψ, B ψ⟫_ℂ := by
  have hnorm : ⟪ψ, ψ⟫_ℂ = 1 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ψ
    rw [this, hψ]
    norm_num
  have hAself : (starRingEnd ℂ) ⟪ψ, A ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := expectation_conj A hA ψ
  have hAψψ : ⟪A ψ, ψ⟫_ℂ = ⟪ψ, A ψ⟫_ℂ := hA ψ ψ
  have hAB : ⟪A ψ, B ψ⟫_ℂ = ⟪ψ, A (B ψ)⟫_ℂ := hA ψ (B ψ)
  simp only [inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right]
  rw [hAB, hAψψ, hnorm, hAself]
  ring

/-- **Robertson uncertainty relation.**  For symmetric (self-adjoint) operators `A`, `B`
on a complex inner product space and a unit vector `ψ`, the product of the standard
deviations `ΔA = ‖(A - ⟨A⟩)ψ‖` and `ΔB = ‖(B - ⟨B⟩)ψ‖` is at least
`½ |⟨ψ, [A,B] ψ⟩|`. -/
theorem robertson_uncertainty (A B : H →ₗ[ℂ] H)
    (hA : ∀ x y : H, ⟪A x, y⟫_ℂ = ⟪x, A y⟫_ℂ)
    (hB : ∀ x y : H, ⟪B x, y⟫_ℂ = ⟪x, B y⟫_ℂ)
    (ψ : H) (hψ : ‖ψ‖ = 1) :
    ‖A ψ - ⟪ψ, A ψ⟫_ℂ • ψ‖ * ‖B ψ - ⟪ψ, B ψ⟫_ℂ • ψ‖
      ≥ (1 / 2) * ‖⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ‖ := by
  set f : H := A ψ - ⟪ψ, A ψ⟫_ℂ • ψ with hf
  set g : H := B ψ - ⟪ψ, B ψ⟫_ℂ • ψ with hg
  have h1 : ⟪f, g⟫_ℂ = ⟪ψ, A (B ψ)⟫_ℂ - ⟪ψ, A ψ⟫_ℂ * ⟪ψ, B ψ⟫_ℂ :=
    inner_centered A B hA ψ hψ
  have h2 : ⟪g, f⟫_ℂ = ⟪ψ, B (A ψ)⟫_ℂ - ⟪ψ, B ψ⟫_ℂ * ⟪ψ, A ψ⟫_ℂ :=
    inner_centered B A hB ψ hψ
  have hcomm : ⟪ψ, A (B ψ) - B (A ψ)⟫_ℂ = ⟪f, g⟫_ℂ - ⟪g, f⟫_ℂ := by
    rw [inner_sub_right, h1, h2]; ring
  have hconj : ⟪g, f⟫_ℂ = (starRingEnd ℂ) ⟪f, g⟫_ℂ := (inner_conj_symm (𝕜 := ℂ) g f).symm
  have hbound : ‖⟪f, g⟫_ℂ - ⟪g, f⟫_ℂ‖ ≤ 2 * ‖⟪f, g⟫_ℂ‖ := by
    rw [hconj]
    calc ‖⟪f, g⟫_ℂ - (starRingEnd ℂ) ⟪f, g⟫_ℂ‖
        ≤ ‖⟪f, g⟫_ℂ‖ + ‖(starRingEnd ℂ) ⟪f, g⟫_ℂ‖ := norm_sub_le _ _
      _ = 2 * ‖⟪f, g⟫_ℂ‖ := by rw [RCLike.norm_conj]; ring
  have hcs : ‖⟪f, g⟫_ℂ‖ ≤ ‖f‖ * ‖g‖ := norm_inner_le_norm (𝕜 := ℂ) f g
  rw [ge_iff_le, hcomm]
  linarith
end QC

