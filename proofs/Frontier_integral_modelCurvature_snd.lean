/-
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Tknn Chern Hall
Category: Frontier Physics
Target: Frontier.tknn_chern_hall
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The Berry-curvature flux of a curvature field `F` over the Brillouin torus
`[0, 2π] × [0, 2π]`, written as an iterated integral in the two quasi-momenta. -/
noncomputable def berryFlux (F : ℝ × ℝ → ℝ) : ℝ :=
  ∫ k₁ in (0 : ℝ)..(2 * Real.pi), ∫ k₂ in (0 : ℝ)..(2 * Real.pi), F (k₁, k₂)

/-- The (first) Chern number of a Bloch band, i.e. its Berry-curvature flux over the
Brillouin torus normalised by `2π`. -/
noncomputable def chernNumber (F : ℝ × ℝ → ℝ) : ℝ :=
  berryFlux F / (2 * Real.pi)

/-- The TKNN (Kubo) transverse conductance of a filled band with Berry curvature `F`:
the normalised Berry-curvature flux times the conductance quantum `e² / h`. -/
noncomputable def hallConductance (e h : ℝ) (F : ℝ × ℝ → ℝ) : ℝ :=
  (e ^ 2 / h) * chernNumber F

/-- Base-case Bloch band: a Berry curvature on the Brillouin torus consisting of a uniform
part carrying `n` quanta of flux plus a zero-mean periodic modulation. -/
noncomputable def modelCurvature (n : ℤ) (k : ℝ × ℝ) : ℝ :=
  (n : ℝ) / (2 * Real.pi) + Real.cos k.1 * Real.sin k.2

/-- The inner (`k₂`) integral of the model Berry curvature: the modulation averages out,
leaving `n` for every `k₁`. -/
theorem integral_modelCurvature_snd (n : ℤ) (k₁ : ℝ) :
    (∫ k₂ in (0 : ℝ)..(2 * Real.pi), modelCurvature n (k₁, k₂)) = (n : ℝ) := by
  have hsin : (∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.sin k₂) = 0 := by
    simp [integral_sin]
  have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  have h₁ : IntervalIntegrable (fun _ : ℝ => (n : ℝ) / (2 * Real.pi)) MeasureTheory.volume
      0 (2 * Real.pi) := intervalIntegrable_const
  have h₂ : IntervalIntegrable (fun k₂ : ℝ => Real.cos k₁ * Real.sin k₂)
      MeasureTheory.volume 0 (2 * Real.pi) :=
    (intervalIntegral.intervalIntegrable_sin).const_mul _
  calc (∫ k₂ in (0 : ℝ)..(2 * Real.pi), modelCurvature n (k₁, k₂))
      = (∫ _ in (0 : ℝ)..(2 * Real.pi), (n : ℝ) / (2 * Real.pi))
        + ∫ k₂ in (0 : ℝ)..(2 * Real.pi), Real.cos k₁ * Real.sin k₂ := by
        rw [show (fun k₂ : ℝ => modelCurvature n (k₁, k₂))
              = (fun _ : ℝ => (n : ℝ) / (2 * Real.pi))
                + (fun k₂ : ℝ => Real.cos k₁ * Real.sin k₂) from rfl]
        exact intervalIntegral.integral_add h₁ h₂
    _ = (n : ℝ) := by
        rw [intervalIntegral.integral_const_mul, hsin, intervalIntegral.integral_const]
        simp only [smul_eq_mul, sub_zero]
        field_simp
        ring

/-- Key intermediate lemma: the Berry-curvature flux of the model band over the Brillouin
torus is quantised, equal to `2π n`. -/
theorem berryFlux_modelCurvature (n : ℤ) :
    berryFlux (modelCurvature n) = 2 * Real.pi * (n : ℝ) := by
  unfold berryFlux
  simp only [integral_modelCurvature_snd n]
  simp [mul_comm]

/-- The Chern number of the model band is the integer `n`. -/
theorem chernNumber_modelCurvature (n : ℤ) :
    chernNumber (modelCurvature n) = (n : ℝ) := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  unfold chernNumber
  rw [berryFlux_modelCurvature]
  field_simp

/-- **TKNN theorem (base case).** For the model Bloch band with Berry curvature
`modelCurvature n`, the integer-quantum-Hall transverse conductance obtained from the
Kubo/TKNN formula equals the Chern number `n` times the conductance quantum `e² / h`;
in particular it is an integer multiple of `e² / h`. -/
theorem tknn_chern_hall (e h : ℝ) (n : ℤ) :
    hallConductance e h (modelCurvature n) = (n : ℝ) * (e ^ 2 / h) ∧
      chernNumber (modelCurvature n) = (n : ℝ) := by
  refine ⟨?_, chernNumber_modelCurvature n⟩
  unfold hallConductance
  rw [chernNumber_modelCurvature]
  ring

end Frontier

