/-!
# Chsh Tsirelson
Category: Quantum Computing
Target: QC.chsh_tsirelson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace QC

/-- The square of the CHSH operator: `S² = 4 + [A₁, A₀] [B₀, B₁]`. -/
theorem chsh_sq {R : Type*} [Ring R] [StarRing R] {A₀ A₁ B₀ B₁ : R}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) * (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) =
      4 + (A₁ * A₀ - A₀ * A₁) * (B₀ * B₁ - B₁ * B₀) := by
  have hA₀ : A₀ * A₀ = 1 := by have := T.A₀_inv; rwa [sq] at this
  have hA₁ : A₁ * A₁ = 1 := by have := T.A₁_inv; rwa [sq] at this
  have hB₀ : B₀ * B₀ = 1 := by have := T.B₀_inv; rwa [sq] at this
  have hB₁ : B₁ * B₁ = 1 := by have := T.B₁_inv; rwa [sq] at this
  have c₁ := T.A₀B₀_commutes
  have c₂ := T.A₀B₁_commutes
  have c₃ := T.A₁B₀_commutes
  have c₄ := T.A₁B₁_commutes
  grind

/-- The CHSH operator is self-adjoint. -/
theorem chsh_isSelfAdjoint {R : Type*} [Ring R] [StarRing R] {A₀ A₁ B₀ B₁ : R}
    (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    star (A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁) = A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ := by
  simp only [star_add, star_sub, star_mul, T.A₀_sa, T.A₁_sa, T.B₀_sa, T.B₁_sa,
    ← T.A₀B₀_commutes, ← T.A₀B₁_commutes, ← T.A₁B₀_commutes, ← T.A₁B₁_commutes]

/-- A self-adjoint involution in a C*-algebra has norm at most one. -/
theorem norm_le_one_of_sa_involution {A : Type*} [NormedRing A] [NormOneClass A] [StarRing A]
    [CStarRing A] {a : A} (h_sa : star a = a) (h_inv : a ^ 2 = 1) : ‖a‖ ≤ 1 := by
  have h : ‖a‖ * ‖a‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, h_sa, ← sq, h_inv, norm_one]
  nlinarith [norm_nonneg a]

/-- **Tsirelson's bound.** In a C*-algebra, the CHSH operator
`A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁` built from a CHSH tuple (four self-adjoint involutions, with the
`Aᵢ` commuting with the `Bⱼ`) has operator norm at most `2√2`. -/
theorem chsh_tsirelson {A : Type*} [NormedRing A] [NormOneClass A] [StarRing A] [CStarRing A]
    {A₀ A₁ B₀ B₁ : A} (T : IsCHSHTuple A₀ A₁ B₀ B₁) :
    ‖A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁‖ ≤ 2 * √2 := by
  set S : A := A₀ * B₀ + A₀ * B₁ + A₁ * B₀ - A₁ * B₁ with hS
  have hA₀ : ‖A₀‖ ≤ 1 := norm_le_one_of_sa_involution T.A₀_sa T.A₀_inv
  have hA₁ : ‖A₁‖ ≤ 1 := norm_le_one_of_sa_involution T.A₁_sa T.A₁_inv
  have hB₀ : ‖B₀‖ ≤ 1 := norm_le_one_of_sa_involution T.B₀_sa T.B₀_inv
  have hB₁ : ‖B₁‖ ≤ 1 := norm_le_one_of_sa_involution T.B₁_sa T.B₁_inv
  -- the commutators have norm at most 2
  have hcommA : ‖A₁ * A₀ - A₀ * A₁‖ ≤ 2 := by
    calc ‖A₁ * A₀ - A₀ * A₁‖ ≤ ‖A₁ * A₀‖ + ‖A₀ * A₁‖ := norm_sub_le _ _
      _ ≤ ‖A₁‖ * ‖A₀‖ + ‖A₀‖ * ‖A₁‖ := by gcongr <;> exact norm_mul_le _ _
      _ ≤ 1 * 1 + 1 * 1 := by
          gcongr <;> first | positivity | assumption
      _ = 2 := by norm_num
  have hcommB : ‖B₀ * B₁ - B₁ * B₀‖ ≤ 2 := by
    calc ‖B₀ * B₁ - B₁ * B₀‖ ≤ ‖B₀ * B₁‖ + ‖B₁ * B₀‖ := norm_sub_le _ _
      _ ≤ ‖B₀‖ * ‖B₁‖ + ‖B₁‖ * ‖B₀‖ := by gcongr <;> exact norm_mul_le _ _
      _ ≤ 1 * 1 + 1 * 1 := by
          gcongr <;> first | positivity | assumption
      _ = 2 := by norm_num
  have hsq : ‖S‖ * ‖S‖ ≤ 8 := by
    have h1 : ‖S‖ * ‖S‖ = ‖S * S‖ := by
      rw [← CStarRing.norm_star_mul_self, chsh_isSelfAdjoint T]
    rw [h1, hS, chsh_sq T]
    calc ‖(4 : A) + (A₁ * A₀ - A₀ * A₁) * (B₀ * B₁ - B₁ * B₀)‖
        ≤ ‖(4 : A)‖ + ‖(A₁ * A₀ - A₀ * A₁) * (B₀ * B₁ - B₁ * B₀)‖ := norm_add_le _ _
      _ ≤ 4 + ‖A₁ * A₀ - A₀ * A₁‖ * ‖B₀ * B₁ - B₁ * B₀‖ := by
          gcongr
          · have : ‖(4 : A)‖ ≤ 4 * ‖(1 : A)‖ := by
              simpa using norm_nsmul_le (α := A) 4 1
            simpa using this
          · exact norm_mul_le _ _
      _ ≤ 4 + 2 * 2 := by gcongr <;> positivity
      _ = 8 := by norm_num
  have h2 : (0 : ℝ) ≤ 2 * √2 := by positivity
  nlinarith [norm_nonneg S, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0),
    Real.sqrt_nonneg 2]

end QC

