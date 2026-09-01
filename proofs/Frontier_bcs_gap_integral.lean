/-
# Bcs Gap Binding
Category: Frontier Physics
Target: Frontier.bcs_gap_binding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

/-- The BCS "gap integral" `∫₀^ω dξ / √(ξ² + Δ²)` evaluates to `arsinh (ω / Δ)`. -/
theorem bcs_gap_integral (ω Δ : ℝ) (hΔ : 0 < Δ) :
    (∫ ξ in (0 : ℝ)..ω, (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹) = Real.arsinh (ω / Δ) := by
  have hsqrt : ∀ ξ : ℝ, Real.sqrt (1 + (ξ / Δ) ^ 2) = Real.sqrt (ξ ^ 2 + Δ ^ 2) / Δ := by
    intro ξ
    have h : (1 : ℝ) + (ξ / Δ) ^ 2 = (ξ ^ 2 + Δ ^ 2) / Δ ^ 2 := by field_simp; ring
    rw [h, Real.sqrt_div (by positivity), Real.sqrt_sq hΔ.le]
  have hderiv : ∀ ξ ∈ Set.uIcc (0 : ℝ) ω,
      HasDerivAt (fun t : ℝ => Real.arsinh (t / Δ)) ((Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹) ξ := by
    intro ξ _
    have h1 : HasDerivAt (fun t : ℝ => t / Δ) (1 / Δ) ξ := by
      simpa using (hasDerivAt_id ξ).div_const Δ
    have h2 := (Real.hasDerivAt_arsinh (ξ / Δ)).comp ξ h1
    have h3 : HasDerivAt (fun t : ℝ => Real.arsinh (t / Δ))
        ((Real.sqrt (1 + (ξ / Δ) ^ 2))⁻¹ * Δ⁻¹) ξ := by
      simpa [Function.comp_def, one_div] using h2
    have key : (Real.sqrt (1 + (ξ / Δ) ^ 2))⁻¹ * Δ⁻¹ = (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹ := by
      rw [hsqrt ξ]
      have hne : Real.sqrt (ξ ^ 2 + Δ ^ 2) ≠ 0 := by positivity
      field_simp
    rwa [key] at h3
  have hcont : Continuous fun ξ : ℝ => (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹ :=
    Continuous.inv₀ (by fun_prop) (fun x => by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 ω)]
  simp

/-- **BCS gap equation / Cooper pairing.**

For any attractive coupling `g > 0` and any positive cutoff `ω`, the BCS gap equation
`g · ∫₀^ω dξ / √(ξ² + Δ²) = 1` has a *nonzero* (indeed strictly positive) solution `Δ`,
namely `Δ = ω / sinh (1 / g)`.  Thus an arbitrarily weak attraction binds a Cooper pair. -/
theorem bcs_gap_binding (g ω : ℝ) (hg : 0 < g) (hω : 0 < ω) :
    ∃ Δ : ℝ, 0 < Δ ∧ g * ∫ ξ in (0 : ℝ)..ω, (Real.sqrt (ξ ^ 2 + Δ ^ 2))⁻¹ = 1 := by
  have hs : 0 < Real.sinh (1 / g) := by positivity
  refine ⟨ω / Real.sinh (1 / g), by positivity, ?_⟩
  rw [bcs_gap_integral ω _ (by positivity)]
  have hdd : ω / (ω / Real.sinh (1 / g)) = Real.sinh (1 / g) := by
    field_simp
  rw [hdd, Real.arsinh_sinh]
  field_simp

end Frontier

