/-
# Rung Glue Constant Upgrade
Category: A Assembly
Target: Zeta23Scaffold.rung_glue_constant_upgrade
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Zeta23Scaffold

/-- Abbreviation for the eventual lower bound statement
`∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (c - ε) * n T ≤ s T`. -/
def EventualBound (c : ℝ) (n s : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ T0 : ℝ, ∀ T ≥ T0, (c - ε) * n T ≤ s T

/-- (a) The `(2*(31/36) - 1 - ε)`-bound is literally the `(13/18 - ε)`-bound. -/
theorem rung1318_of_bridge (n s : ℝ → ℝ)
    (H : ∀ ε > 0, ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - ε) * n T ≤ s T) :
    EventualBound (13 / 18) n s := by
  intro ε hε
  obtain ⟨T0, hT0⟩ := H ε hε
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have hc : (2 * (31 / 36) - 1 - ε : ℝ) = 13 / 18 - ε := by norm_num
  rwa [hc] at h

/-- (b) The `(13/18 - ε)`-bound dominates the `(2/3 - ε)`-bound, for a nonnegative
comparison sequence `n`. -/
theorem rung1318_implies_two_thirds (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : EventualBound (13 / 18) n s) :
    EventualBound (2 / 3) n s := by
  intro ε hε
  obtain ⟨T0, hT0⟩ := H ε hε
  refine ⟨T0, fun T hT => ?_⟩
  have h := hT0 T hT
  have hmono : (2 / 3 - ε) * n T ≤ (13 / 18 - ε) * n T := by
    have : (2 / 3 - ε) ≤ (13 / 18 - ε) := by norm_num
    exact mul_le_mul_of_nonneg_right this (hn T)
  linarith

/-- **Rung glue constant upgrade.**  For any nonnegative comparison sequence `n`,
the `(2*(31/36) - 1 - ε)`-bound yields both the `(13/18 - ε)`-bound and the
`(2/3 - ε)`-bound. -/
theorem rung_glue_constant_upgrade (n s : ℝ → ℝ) (hn : ∀ T, 0 ≤ n T)
    (H : ∀ ε > 0, ∃ T0 : ℝ, ∀ T ≥ T0, (2 * (31 / 36) - 1 - ε) * n T ≤ s T) :
    (∀ ε > 0, ∃ T0 : ℝ, ∀ T ≥ T0, (13 / 18 - ε) * n T ≤ s T) ∧
      (∀ ε > 0, ∃ T0 : ℝ, ∀ T ≥ T0, (2 / 3 - ε) * n T ≤ s T) := by
  have h1 : EventualBound (13 / 18) n s := rung1318_of_bridge n s H
  exact ⟨h1, rung1318_implies_two_thirds n s hn h1⟩

end Zeta23Scaffold

