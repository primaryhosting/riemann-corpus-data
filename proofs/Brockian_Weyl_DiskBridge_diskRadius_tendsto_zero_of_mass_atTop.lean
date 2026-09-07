/-
  Brockian/WeylDiskBridge.lean — glue between the finite-`b` Disk radius formula
  and the Dichotomy radius map.

  Imports Disk + Dichotomy only (does not edit either's core proofs).

  ## What is proved

    * `diskRadius` — the classical `1/(2 |Im λ| · ∫₀ᵇ |φ|²)` as a function of `b`.
    * `diskRadius_eq_weylRadius` — equals `Dichotomy.weylRadius |Im λ| I`.
    * `diskRadius_tendsto_zero_of_mass_atTop` — if the mass tends to `+∞` then
        the Disk radius tends to 0.
    * `diskRadius_tendsto_zero_of_limitPointRadius` — if mass is unbounded and
        monotone (always for continuous φ), radius → 0.

  Verification: AXLE @ lean-4.32.0; axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylDichotomy

open Filter Topology MeasureTheory intervalIntegral
open Brockian.Weyl.Dichotomy

namespace Brockian.Weyl.DiskBridge

/-- The classical Weyl radius as a function of the endpoint `b`. -/
noncomputable def diskRadius (lam : ℂ) (φ : ℝ → ℂ) (b : ℝ) : ℝ :=
  1 / (2 * |lam.im| * ∫ x in 0..b, ‖φ x‖ ^ 2)

/-- Disk radius is exactly the Dichotomy radius shape with `c = |Im λ|`. -/
theorem diskRadius_eq_weylRadius (lam : ℂ) (φ : ℝ → ℂ) :
    diskRadius lam φ =
      weylRadius |lam.im| (fun b => ∫ x in 0..b, ‖φ x‖ ^ 2) := by
  funext b
  rfl

/-- **Mass diverges ⇒ Disk radius → 0.** Requires `Im λ ≠ 0`. -/
theorem diskRadius_tendsto_zero_of_mass_atTop {lam : ℂ} (hlam : lam.im ≠ 0)
    {φ : ℝ → ℂ}
    (hI : Tendsto (fun b : ℝ => ∫ x in 0..b, ‖φ x‖ ^ 2) atTop atTop) :
    Tendsto (diskRadius lam φ) atTop (nhds 0) := by
  rw [diskRadius_eq_weylRadius]
  exact radius_tendsto_zero_of_atTop (abs_pos.mpr hlam) hI

/-- Continuous φ ⇒ mass map is monotone (nonnegative integrand). -/
theorem mass_monotone {φ : ℝ → ℂ} (hφ : Continuous φ) :
    Monotone (fun b => ∫ x in 0..b, ‖φ x‖ ^ 2) := by
  intro a b hab
  have hfc : Continuous (fun x => ‖φ x‖ ^ 2) := hφ.norm.pow 2
  have h1 : IntervalIntegrable (fun x => ‖φ x‖ ^ 2) volume 0 a :=
    hfc.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x => ‖φ x‖ ^ 2) volume a b :=
    hfc.intervalIntegrable _ _
  have hadd := integral_add_adjacent_intervals h1 h2
  have hnn : 0 ≤ ∫ x in a..b, ‖φ x‖ ^ 2 :=
    integral_nonneg hab fun _ _ => sq_nonneg _
  linarith [hadd, hnn]

/-- **Limit-point radius ⇒ Disk radius → 0** (for continuous φ, `Im λ ≠ 0`). -/
theorem diskRadius_tendsto_zero_of_limitPointRadius {lam : ℂ} (hlam : lam.im ≠ 0)
    {φ : ℝ → ℂ} (hφ : Continuous φ)
    (h : IsLimitPointRadius (fun b => ∫ x in 0..b, ‖φ x‖ ^ 2)) :
    Tendsto (diskRadius lam φ) atTop (nhds 0) := by
  rw [diskRadius_eq_weylRadius]
  exact limitPointRadius_radius_tendsto_zero (abs_pos.mpr hlam) (mass_monotone hφ) h

end Brockian.Weyl.DiskBridge
