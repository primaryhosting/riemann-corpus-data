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
# Config Count Over Main Tendsto
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.configCount_over_main_tendsto
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Classical
open Filter Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- The set of *configurations* of level `N` occurring in a Bombieri–Vinogradov style
reduction: pairs `(q, a)` consisting of a modulus `1 ≤ q ≤ N` together with a residue
class `a` modulo `q`. -/
def configSet (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 N).biUnion fun q => {q} ×ˢ Finset.range q

/-- The number of configurations of level `N`. -/
def configCount (N : ℕ) : ℕ := (configSet N).card

/-- The main term for the number of configurations of level `N`, namely `N ^ 2 / 2`. -/
noncomputable def mainTerm (N : ℕ) : ℝ := (N : ℝ) ^ 2 / 2

/-- The configuration count of level `N` is the Gauss sum `∑_{q ≤ N} q`. -/
theorem configCount_eq_sum (N : ℕ) : configCount N = ∑ q ∈ Finset.Icc 1 N, q := by
  unfold configCount configSet
  rw [Finset.card_biUnion]
  · simp
  · intro x _ y _ hxy
    simp only [Finset.disjoint_left, Finset.mem_product, Finset.mem_singleton, Finset.mem_range]
    rintro ⟨a, b⟩ ⟨rfl, -⟩ ⟨h, -⟩
    exact hxy h

/-- Closed form: `2 * configCount N = N * (N + 1)`. -/
theorem two_mul_configCount (N : ℕ) : 2 * configCount N = N * (N + 1) := by
  rw [configCount_eq_sum]
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.mul_add, ih]
    ring

/-- For `N ≥ 1` the ratio of the configuration count to the main term is `1 + 1 / N`. -/
theorem configCount_div_mainTerm (N : ℕ) (hN : 1 ≤ N) :
    (configCount N : ℝ) / mainTerm N = 1 + 1 / (N : ℝ) := by
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h : (2 : ℝ) * configCount N = (N : ℝ) * (N + 1) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (two_mul_configCount N)
  unfold mainTerm
  field_simp
  nlinarith [h]

/-- **Config count over main term tends to one.**
The number of Bombieri–Vinogradov configurations of level `N`, divided by the main
term `N ^ 2 / 2`, tends to `1` as `N → ∞`. -/
theorem configCount_over_main_tendsto :
    Tendsto (fun N : ℕ => (configCount N : ℝ) / mainTerm N) atTop (𝓝 1) := by
  have h : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).add
      tendsto_one_div_atTop_nhds_zero_nat
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  exact (configCount_div_mainTerm N hN).symm

end EquidistributionBVReduction
end Brockian

