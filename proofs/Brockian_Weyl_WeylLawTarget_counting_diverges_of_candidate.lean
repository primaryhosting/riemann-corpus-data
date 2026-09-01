import Brockian.Weyl.WeylLawTarget
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
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a candidate spectrum `mu : ℕ → ℝ`:
`counting mu t` is the number of indices `n` with `mu n ≤ t`. -/
noncomputable def counting (mu : ℕ → ℝ) (t : ℝ) : ℕ := {n : ℕ | mu n ≤ t}.ncard

/-- For a candidate spectrum tending to infinity, each sublevel set is finite. -/
theorem finite_sublevel {mu : ℕ → ℝ} (htop : Filter.Tendsto mu Filter.atTop Filter.atTop)
    (t : ℝ) : {n : ℕ | mu n ≤ t}.Finite := by
  have h : ∀ᶠ n in Filter.atTop, t < mu n :=
    htop.eventually (Filter.eventually_gt_atTop t)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h
  refine Set.Finite.subset (Set.finite_Iio N) ?_
  intro n hn
  by_contra hlt
  exact absurd (hN n (le_of_not_gt hlt)) (not_lt.2 hn)

/-- Beyond the maximum of the first `K` candidate eigenvalues, the counting function is `≥ K`. -/
theorem le_counting_of_ge {mu : ℕ → ℝ} (htop : Filter.Tendsto mu Filter.atTop Filter.atTop)
    (K : ℕ) : ∀ᶠ t in Filter.atTop, K ≤ counting mu t := by
  obtain ⟨M, hM⟩ := Finset.exists_le ((Finset.range K).image mu)
  filter_upwards [Filter.eventually_ge_atTop M] with t ht
  have hsub : (Finset.range K : Set ℕ) ⊆ {n : ℕ | mu n ≤ t} := by
    intro n hn
    have hle : mu n ≤ M := hM (mu n) (Finset.mem_image_of_mem mu (by simpa using hn))
    exact hle.trans ht
  have hcard := Set.ncard_le_ncard hsub (finite_sublevel htop t)
  simpa [counting, Set.ncard_coe_finset] using hcard

/-- **Weyl law target (open discharge).** If a candidate spectrum `mu : ℕ → ℝ` tends to
infinity, then its eigenvalue counting function `t ↦ #{n | mu n ≤ t}` diverges to infinity. -/
theorem counting_diverges_of_candidate {mu : ℕ → ℝ}
    (htop : Filter.Tendsto mu Filter.atTop Filter.atTop) :
    Filter.Tendsto (counting mu) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop.2 fun K => le_counting_of_ge htop K

end Brockian.Weyl.WeylLawTarget

