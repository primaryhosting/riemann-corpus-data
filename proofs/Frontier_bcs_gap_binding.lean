import Mathlib

/-!
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Frontier

/-- The BCS gap functional: the integral
`∫_0^ω dξ / √(ξ² + Δ²)` appearing in the (zero-temperature, constant density of states,
Debye-cutoff `ω`) BCS gap equation `1 = λ ∫_0^ω dξ / √(ξ² + Δ²)`. -/
noncomputable def bcsGapIntegral (Δ ω : ℝ) : ℝ :=
  ∫ ξ in (0 : ℝ)..ω, 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)

/-- `ξ ↦ arsinh (ξ / Δ)` is an antiderivative of the BCS kernel `ξ ↦ 1 / √(ξ² + Δ²)`. -/
theorem hasDerivAt_arsinh_div (Δ : ℝ) (hΔ : 0 < Δ) (x : ℝ) :
    HasDerivAt (fun ξ : ℝ => Real.arsinh (ξ / Δ)) (1 / Real.sqrt (x ^ 2 + Δ ^ 2)) x := by
  have h : HasDerivAt (fun ξ : ℝ => ξ / Δ) (1 / Δ) x := by
    simpa [div_eq_mul_inv, one_div] using (hasDerivAt_id x).div_const Δ
  have h2 := h.arsinh
  have hkey : Real.sqrt (1 + (x / Δ) ^ 2) = Real.sqrt (x ^ 2 + Δ ^ 2) / Δ := by
    rw [eq_div_iff (ne_of_gt hΔ)]
    rw [show Δ = Real.sqrt (Δ ^ 2) by rw [Real.sqrt_sq hΔ.le], ← Real.sqrt_mul (by positivity)]
    · rw [Real.sqrt_sq hΔ.le]
      congr 1
      field_simp
      ring
  have hs : 0 < Real.sqrt (x ^ 2 + Δ ^ 2) := Real.sqrt_pos.2 (by positivity)
  convert h2 using 1
  rw [hkey, smul_eq_mul]
  field_simp

/-- The BCS kernel is continuous when `Δ > 0`. -/
theorem continuous_bcsKernel (Δ : ℝ) (hΔ : 0 < Δ) :
    Continuous fun ξ : ℝ => 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2) := by
  apply Continuous.div continuous_const
  · exact (Real.continuous_sqrt.comp (by continuity))
  · intro x
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))

/-- Closed form of the BCS gap integral: `∫_0^ω dξ / √(ξ² + Δ²) = arsinh (ω / Δ)`. -/
theorem bcsGapIntegral_eq_arsinh (Δ ω : ℝ) (hΔ : 0 < Δ) :
    bcsGapIntegral Δ ω = Real.arsinh (ω / Δ) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun ξ : ℝ => Real.arsinh (ξ / Δ))
    (f' := fun ξ : ℝ => 1 / Real.sqrt (ξ ^ 2 + Δ ^ 2)) (a := 0) (b := ω)
    (fun x _ => hasDerivAt_arsinh_div Δ hΔ x)
    ((continuous_bcsKernel Δ hΔ).intervalIntegrable 0 ω)
  simpa [bcsGapIntegral] using h

/-- **BCS gap binding (Cooper pairing).**

For every attractive coupling `lam > 0` and every positive cutoff `ω`, the BCS gap equation
`lam * ∫_0^ω dξ / √(ξ² + Δ²) = 1` has a strictly positive (in particular nonzero) solution,
namely the standard BCS gap `Δ = ω / sinh (1 / lam)`. -/
theorem bcs_gap_binding (lam ω : ℝ) (hlam : 0 < lam) (hω : 0 < ω) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ = ω / Real.sinh (1 / lam) ∧ lam * bcsGapIntegral Δ ω = 1 := by
  have hs : 0 < Real.sinh (1 / lam) :=
    Mathlib.Meta.Positivity.sinh_pos_of_pos (by positivity)
  refine ⟨ω / Real.sinh (1 / lam), by positivity, rfl, ?_⟩
  rw [bcsGapIntegral_eq_arsinh _ _ (by positivity)]
  have : ω / (ω / Real.sinh (1 / lam)) = Real.sinh (1 / lam) := by
    field_simp
  rw [this, Real.arsinh_sinh]
  field_simp

end Frontier

