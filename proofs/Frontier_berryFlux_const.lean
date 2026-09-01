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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The (first) Chern number of a Bloch band with Berry curvature `F` on the Brillouin-zone
torus `[0, 2π] × [0, 2π]`: the integral of the Berry curvature divided by `2π`. -/
noncomputable def chernNumber (F : ℝ → ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ kx in (0:ℝ)..(2 * Real.pi), ∫ ky in (0:ℝ)..(2 * Real.pi), F kx ky

/-- The TKNN (Thouless–Kohmoto–Nightingale–den Nijs) Hall conductance of a filled Bloch band
with Berry curvature `F`, in terms of the conductance quantum `e² / h`. -/
noncomputable def hallConductance (e h : ℝ) (F : ℝ → ℝ → ℝ) : ℝ :=
  (e ^ 2 / h) * chernNumber F

/-- The total Berry flux of a constant Berry curvature `n / (2π)` through the Brillouin-zone
torus equals `2π n`. -/
lemma berryFlux_const (n : ℤ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ kx ky : ℝ, F kx ky = (n : ℝ) / (2 * Real.pi)) :
    (∫ kx in (0:ℝ)..(2 * Real.pi), ∫ ky in (0:ℝ)..(2 * Real.pi), F kx ky)
      = 2 * Real.pi * (n : ℝ) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hinner : ∀ kx : ℝ,
      (∫ ky in (0:ℝ)..(2 * Real.pi), F kx ky) = (n : ℝ) := by
    intro kx
    simp only [hF]
    rw [intervalIntegral.integral_const, smul_eq_mul]
    field_simp
    ring
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (n : ℝ))
    (fun kx _ => hinner kx), intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Quantization: if the total Berry flux through the Brillouin zone is `2π n` for an integer `n`,
then the Chern number is `n` and the Hall conductance is the integer multiple `n · e² / h`
of the conductance quantum. -/
lemma tknn_of_flux (e h : ℝ) (n : ℤ) (F : ℝ → ℝ → ℝ)
    (hflux : (∫ kx in (0:ℝ)..(2 * Real.pi), ∫ ky in (0:ℝ)..(2 * Real.pi), F kx ky)
      = 2 * Real.pi * (n : ℝ)) :
    chernNumber F = (n : ℝ) ∧ hallConductance e h F = (n : ℝ) * (e ^ 2 / h) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hchern : chernNumber F = (n : ℝ) := by
    unfold chernNumber
    rw [hflux]
    field_simp
  exact ⟨hchern, by unfold hallConductance; rw [hchern]; ring⟩

/-- **TKNN / integer quantum Hall effect (base case).**

For a Bloch band whose Berry curvature over the Brillouin zone is the constant `n / (2π)`
(so that the total Berry flux through the torus is `2π n`), the first Chern number equals the
integer `n`, and the Hall conductance is exactly `n · e² / h`, i.e. an integer multiple of the
conductance quantum. -/
theorem tknn_chern_hall (e h : ℝ) (n : ℤ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ kx ky : ℝ, F kx ky = (n : ℝ) / (2 * Real.pi)) :
    chernNumber F = (n : ℝ) ∧ hallConductance e h F = (n : ℝ) * (e ^ 2 / h) :=
  tknn_of_flux e h n F (berryFlux_const n F hF)

/-- A genuinely non-constant Berry curvature also carrying total flux `2π n`:
`F kx ky = (n / 2π) (1 + cos kx · cos ky)`.  The modulation integrates away over the torus. -/
lemma berryFlux_cos_modulated (n : ℤ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ kx ky : ℝ, F kx ky = ((n : ℝ) / (2 * Real.pi)) * (1 + Real.cos kx * Real.cos ky)) :
    (∫ kx in (0:ℝ)..(2 * Real.pi), ∫ ky in (0:ℝ)..(2 * Real.pi), F kx ky)
      = 2 * Real.pi * (n : ℝ) := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hinner : ∀ kx : ℝ, (∫ ky in (0:ℝ)..(2 * Real.pi), F kx ky) = (n : ℝ) := by
    intro kx
    simp only [hF]
    have hint : IntervalIntegrable (fun ky : ℝ => Real.cos kx * Real.cos ky)
        MeasureTheory.volume 0 (2 * Real.pi) :=
      (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      intervalIntegrable_const hint, intervalIntegral.integral_const_mul, integral_cos]
    simp
  rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (n : ℝ))
    (fun kx _ => hinner kx), intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- **TKNN for a non-constant Berry curvature.**  With the modulated curvature
`F kx ky = (n / 2π)(1 + cos kx · cos ky)` the Chern number is still the integer `n`
and the Hall conductance is still exactly `n · e² / h`. -/
theorem tknn_chern_hall_cos_modulated (e h : ℝ) (n : ℤ) (F : ℝ → ℝ → ℝ)
    (hF : ∀ kx ky : ℝ, F kx ky = ((n : ℝ) / (2 * Real.pi)) * (1 + Real.cos kx * Real.cos ky)) :
    chernNumber F = (n : ℝ) ∧ hallConductance e h F = (n : ℝ) * (e ^ 2 / h) :=
  tknn_of_flux e h n F (berryFlux_cos_modulated n F hF)

end Frontier

#print axioms Frontier.tknn_chern_hall
#print axioms Frontier.tknn_chern_hall_cos_modulated

