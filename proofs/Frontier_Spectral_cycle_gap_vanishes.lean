import Mathlib

/-!
# Cycle Gap Vanishes
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_gap_vanishes
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

namespace Frontier.Spectral

/-- The Fiedler value of the cycle graph `C n`. -/
noncomputable def g (n : ℕ) : ℝ := 2 - 2 * Real.cos (2 * Real.pi / n)

/-- The Fiedler value of the cycle `C n` tends to `0` as `n → ∞`:
the cycle family has no uniform spectral gap. -/
theorem cycle_gap_vanishes :
    Filter.Tendsto g Filter.atTop (nhds 0) := by
  have harg : Filter.Tendsto (fun n : ℕ => 2 * Real.pi / n) Filter.atTop (nhds 0) := by
    simpa using
      (Filter.Tendsto.const_div_atTop
        (tendsto_natCast_atTop_atTop (R := ℝ)) (2 * Real.pi))
  have hcos : Filter.Tendsto (fun n : ℕ => Real.cos (2 * Real.pi / n))
      Filter.atTop (nhds 1) := by
    simpa using (Real.continuous_cos.tendsto 0).comp harg
  have := (tendsto_const_nhds (x := (2 : ℝ)) (f := Filter.atTop (α := ℕ))).sub
    (hcos.const_mul (2 : ℝ))
  simpa [g] using this

end Frontier.Spectral

