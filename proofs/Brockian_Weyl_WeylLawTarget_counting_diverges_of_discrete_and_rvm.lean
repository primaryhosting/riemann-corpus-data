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
# Counting Diverges Of Discrete And Rvm
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_rvm
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Brockian.Weyl.WeylLawTarget

open Filter

/-- The eigenvalue counting function of a spectral sequence `mu : ℕ → ℝ`:
`countingFunction mu lam` is the number of indices `n` with `mu n ≤ lam`
(counted with multiplicity, i.e. as indices).  If that index set is infinite
the value is `0` by the convention of `Set.ncard`. -/
noncomputable def countingFunction (mu : ℕ → ℝ) (lam : ℝ) : ℕ :=
  {n : ℕ | mu n ≤ lam}.ncard

/-- Discreteness of the spectrum: every sublevel set of the spectral sequence is finite. -/
def DiscreteSpectrum (mu : ℕ → ℝ) : Prop :=
  ∀ lam : ℝ, {n : ℕ | mu n ≤ lam}.Finite

/-- The Rayleigh–Ritz variational-minimax (RVM) property of a spectral sequence:
the minimax values are nondecreasing in the index. -/
def RVM (mu : ℕ → ℝ) : Prop := Monotone mu

/-- If the spectrum is discrete (all sublevel sets of the eigenvalue sequence are finite)
and the eigenvalues are given by the nondecreasing variational minimax (RVM) sequence,
then the eigenvalue counting function diverges to `+∞`. -/
theorem counting_diverges_of_discrete_and_rvm
    (mu : ℕ → ℝ) (hdiscrete : DiscreteSpectrum mu) (hrvm : RVM mu) :
    Tendsto (countingFunction mu) atTop atTop := by
  refine tendsto_atTop.2 fun K => ?_
  filter_upwards [eventually_ge_atTop (mu K)] with lam hlam
  have hsub : Finset.range (K + 1) ⊆ (hdiscrete lam).toFinset := by
    intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    exact le_trans (hrvm (Nat.lt_succ_iff.mp hn)) hlam
  have hcard : K + 1 ≤ (hdiscrete lam).toFinset.card := by
    simpa using Finset.card_le_card hsub
  have : countingFunction mu lam = (hdiscrete lam).toFinset.card :=
    Set.ncard_eq_toFinset_card _ (hdiscrete lam)
  omega

end Brockian.Weyl.WeylLawTarget


