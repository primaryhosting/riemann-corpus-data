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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical

namespace Brockian.Weyl.WeylLawTarget

/-- The spectral counting function of an eigenvalue sequence `mu : ℕ → ℝ`:
`counting mu t` is the number of indices `n` whose eigenvalue `mu n` is at most `t`.
This is the function `N(t)` appearing in Weyl's law. -/
noncomputable def counting (mu : ℕ → ℝ) (t : ℝ) : ℕ := {n : ℕ | mu n ≤ t}.ncard

/-- The counting function is monotone in the spectral parameter, provided the spectrum
is locally finite. -/
theorem counting_mono (mu : ℕ → ℝ) (hloc : ∀ t : ℝ, {n : ℕ | mu n ≤ t}.Finite) :
    Monotone (counting mu) := fun _ _ hst =>
  Set.ncard_le_ncard (fun _ hn => le_trans hn hst) (hloc _)

/-- **Divergence of the spectral counting function.**
If the spectrum of `mu` is locally finite and, for every `N`, there *exists* a spectral
parameter at which at least `N` eigenvalues have been counted, then the counting function
diverges to `+∞`. -/
theorem counting_diverges_of_exists (mu : ℕ → ℝ)
    (hloc : ∀ t : ℝ, {n : ℕ | mu n ≤ t}.Finite)
    (hex : ∀ N : ℕ, ∃ t : ℝ, N ≤ counting mu t) :
    Filter.Tendsto (counting mu) Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_atTop.2 fun N => ?_
  obtain ⟨t, ht⟩ := hex N
  exact ⟨t, fun s hs => le_trans ht (counting_mono mu hloc hs)⟩

/-- A sufficient condition showing the hypotheses above are satisfiable: if the eigenvalue
sequence itself tends to `+∞`, then the spectrum is locally finite and the counting
function diverges. -/
theorem counting_diverges_of_tendsto (mu : ℕ → ℝ)
    (hmu : Filter.Tendsto mu Filter.atTop Filter.atTop) :
    Filter.Tendsto (counting mu) Filter.atTop Filter.atTop := by
  have hloc : ∀ t : ℝ, {n : ℕ | mu n ≤ t}.Finite := by
    intro t
    obtain ⟨M, hM⟩ := (Filter.tendsto_atTop.1 hmu (t + 1)).exists_forall_of_atTop
    refine Set.Finite.subset (Set.finite_Iio M) fun n hn => ?_
    by_contra hnM
    have := hM n (not_lt.1 hnM)
    simp only [Set.mem_setOf_eq] at hn
    linarith
  refine counting_diverges_of_exists mu hloc fun N => ?_
  obtain ⟨t, ht⟩ := (Set.finite_Iio N).image mu |>.bddAbove
  refine ⟨t, ?_⟩
  have hsub : (Set.Iio N : Set ℕ) ⊆ {n : ℕ | mu n ≤ t} := fun n hn =>
    ht ⟨n, hn, rfl⟩
  have hcard := Set.ncard_le_ncard hsub (hloc t)
  have hIio : (Set.Iio N : Set ℕ).ncard = N := by
    simp [Set.ncard_eq_toFinset_card', Set.toFinset_Iio]
  rwa [hIio] at hcard

end Brockian.Weyl.WeylLawTarget

