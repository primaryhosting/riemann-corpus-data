import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
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

open Filter Topology

namespace Brockian.EquidistributionBVReduction

/-- **Total over main tendsto.**

In the bounded-variation reduction of an equidistribution estimate one splits a `total`
quantity into a diverging `main` term plus an error term which is controlled uniformly
(e.g. by the total variation of the test function).  Under those two hypotheses the ratio
`total / main` tends to `1`.

This is the statement that was previously assumed as a named hypothesis; it is proved here,
so it may be discharged and the surrounding result made unconditional. -/
theorem total_over_main_tendsto {total main : ℕ → ℝ} {C : ℝ}
    (hmain : Tendsto main atTop atTop)
    (hbound : ∀ n, |total n - main n| ≤ C) :
    Tendsto (fun n => total n / main n) atTop (𝓝 1) := by
  have hpos : ∀ᶠ n in atTop, (0 : ℝ) < main n := hmain.eventually_gt_atTop 0
  -- the relative error is squeezed to zero by `C / main n`
  have hC : Tendsto (fun n => C / main n) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds hmain
  have h0 : Tendsto (fun n => (total n - main n) / main n) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hC
    filter_upwards [hpos] with n hn
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
    gcongr
    exact hbound n
  have h1 := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).add h0
  rw [add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [hpos] with n hn
  field_simp
  ring

/-- A typical instance of the reduction: if the partial sums of `f` agree with `c * n`
up to a uniformly bounded error and `c > 0`, then the normalized sums tend to `1`. -/
theorem sum_div_linear_tendsto_one {f : ℕ → ℝ} {c C : ℝ} (hc : 0 < c)
    (hbound : ∀ n, |(∑ k ∈ Finset.range n, f k) - c * n| ≤ C) :
    Tendsto (fun n => (∑ k ∈ Finset.range n, f k) / (c * n)) atTop (𝓝 1) := by
  refine total_over_main_tendsto (C := C) ?_ hbound
  exact Filter.Tendsto.const_mul_atTop hc tendsto_natCast_atTop_atTop

end Brockian.EquidistributionBVReduction

#print axioms Brockian.EquidistributionBVReduction.total_over_main_tendsto
#print axioms Brockian.EquidistributionBVReduction.sum_div_linear_tendsto_one

