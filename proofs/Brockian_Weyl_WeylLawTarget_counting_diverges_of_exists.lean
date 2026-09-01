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
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The Weyl counting function of a spectrum `S ⊆ ℝ`: the number of spectral points
that are `≤ lam`. -/
noncomputable def counting (S : Set ℝ) (lam : ℝ) : ℕ := (S ∩ Set.Iic lam).ncard

/-- A discrete spectrum with infinitely many points has a divergent counting function:
`counting S lam → ∞` as `lam → ∞`.

The hypothesis `hdisc` says the spectrum is locally finite from below (each spectral
window `(-∞, lam]` contains only finitely many points), and `hex` says there are
infinitely many spectral points. -/
theorem counting_diverges_of_exists (S : Set ℝ)
    (hdisc : ∀ lam : ℝ, (S ∩ Set.Iic lam).Finite)
    (hex : S.Infinite) :
    Filter.Tendsto (counting S) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun n => ?_
  obtain ⟨T, hTS, hTcard⟩ := hex.exists_subset_card_eq n
  obtain ⟨M, hM⟩ := T.exists_le
  refine ⟨M, fun lam hlam => ?_⟩
  have hsub : (T : Set ℝ) ⊆ S ∩ Set.Iic lam := by
    intro x hx
    exact ⟨hTS hx, le_trans (hM x hx) hlam⟩
  have hle := Set.ncard_le_ncard hsub (hdisc lam)
  simpa [counting, hTcard] using hle

end Brockian.Weyl.WeylLawTarget

