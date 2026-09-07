/-
# Cycle Gap Vanishes
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_gap_vanishes
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

namespace Frontier.Spectral

/-- `2 * π / n → 0` as `n → ∞`. -/
theorem tendsto_two_pi_div_atTop :
    Filter.Tendsto (fun n : ℕ => 2 * Real.pi / n) Filter.atTop (nhds 0) := by
  simpa using
    (Filter.Tendsto.const_div_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) (2 * Real.pi))

/-- The Fiedler value of the cycle `C n` tends to `0`, so the cycle family has no
uniform spectral gap. -/
theorem cycle_gap_vanishes :
    Filter.Tendsto (fun n : ℕ => 2 - 2 * Real.cos (2 * Real.pi / n))
      Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ => Real.cos (2 * Real.pi / n)) Filter.atTop
      (nhds (Real.cos 0)) :=
    (Real.continuous_cos.tendsto 0).comp tendsto_two_pi_div_atTop
  rw [Real.cos_zero] at h
  have := (tendsto_const_nhds (x := (2 : ℝ)) (f := Filter.atTop (α := ℕ))).sub
    (h.const_mul (2 : ℝ))
  simpa using this

end Frontier.Spectral

