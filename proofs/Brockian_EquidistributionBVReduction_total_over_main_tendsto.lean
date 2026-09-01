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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Total Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.total_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Filter Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- **Total over main tendsto.**

In an equidistribution / Bombieri–Vinogradov style reduction one splits a total
count into a *main term* and an *error term*, `total = main + err`, and shows that
the error is negligible compared with the main term, i.e. `err / main → 0`.
The conclusion is that the total is asymptotic to the main term:
`total / main → 1`.

The main term is only required to be eventually nonvanishing. -/
theorem total_over_main_tendsto {total main err : ℕ → ℝ}
    (hsplit : ∀ n, total n = main n + err n)
    (hmain : ∀ᶠ n in atTop, main n ≠ 0)
    (herr : Tendsto (fun n => err n / main n) atTop (𝓝 0)) :
    Tendsto (fun n => total n / main n) atTop (𝓝 1) := by
  have hlim : Tendsto (fun n => 1 + err n / main n) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add herr
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hmain] with n hn
  rw [hsplit n, add_div, div_self hn]

end EquidistributionBVReduction
end Brockian

