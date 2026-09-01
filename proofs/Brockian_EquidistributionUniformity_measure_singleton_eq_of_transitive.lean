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
# Equidistribution from transitive symmetry

If a group `G` acts transitively on a finite set `X` and `μ` is a `G`-invariant probability
measure on `X`, then `μ` is the uniform measure: every singleton has measure `1 / |X|`.

The main result is `Brockian.EquidistributionUniformity.sing_uniform_of_transitive`.
-/

open MeasureTheory
open scoped ENNReal

namespace Brockian.EquidistributionUniformity

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
variable {G : Type*} [Group G] [MulAction G X]

omit [MeasurableSingletonClass X] in
/-- Under a transitive action by measure-preserving transformations, all singletons have the
same measure. -/
theorem measure_singleton_eq_of_transitive (μ : Measure X) [SMulInvariantMeasure G X μ]
    (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x y : X) : μ {x} = μ {y} := by
  obtain ⟨g, hg⟩ := htrans x y
  have hpre : (fun z => g • z) ⁻¹' ({y} : Set X) = {x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact MulAction.injective g (h.trans hg.symm)
    · rintro rfl
      exact hg
  calc μ {x} = μ ((fun z => g • z) ⁻¹' ({y} : Set X)) := by rw [hpre]
    _ = μ {y} := measure_preimage_smul μ g _

/-- The total mass of a probability measure on a finite space is the sum of the masses of the
singletons. -/
theorem sum_measure_singleton_eq_one [Fintype X] (μ : Measure X) [IsProbabilityMeasure μ] :
    ∑ y : X, μ {y} = 1 := by
  rw [MeasureTheory.sum_measure_singleton]
  simp

/-- **Uniformity from transitivity.** A `G`-invariant probability measure on a finite set with a
transitive `G`-action assigns mass `1 / |X|` to each singleton. -/
theorem sing_uniform_of_transitive [Fintype X] (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G X μ] (htrans : ∀ x y : X, ∃ g : G, g • x = y) (x : X) :
    μ {x} = 1 / (Fintype.card X : ℝ≥0∞) := by
  have hsum : ∑ y : X, μ {y} = 1 := sum_measure_singleton_eq_one μ
  have hconst : ∑ y : X, μ {y} = (Fintype.card X : ℝ≥0∞) * μ {x} := by
    rw [Finset.sum_congr rfl fun y _ => measure_singleton_eq_of_transitive (G := G) μ htrans y x]
    simp [Finset.card_univ]
  haveI : Nonempty X := ⟨x⟩
  have hcard : (Fintype.card X : ℝ≥0∞) ≠ 0 := by
    simp [Fintype.card_ne_zero (α := X)]
  have hcard' : (Fintype.card X : ℝ≥0∞) ≠ ⊤ := by simp
  have h : (Fintype.card X : ℝ≥0∞) * μ {x} = 1 := by rw [← hconst, hsum]
  exact (ENNReal.eq_div_iff hcard hcard').mpr h

/-- Version of `sing_uniform_of_transitive` stated with Mathlib's `IsPretransitive` typeclass. -/
theorem sing_uniform_of_isPretransitive [Fintype X] [MulAction.IsPretransitive G X]
    (μ : Measure X) [IsProbabilityMeasure μ] [SMulInvariantMeasure G X μ] (x : X) :
    μ {x} = 1 / (Fintype.card X : ℝ≥0∞) :=
  sing_uniform_of_transitive (G := G) μ (fun x y => MulAction.exists_smul_eq G x y) x

/-- A `G`-invariant probability measure on a finite set with transitive `G`-action is exactly the
normalized counting measure. -/
theorem eq_inv_card_smul_count_of_transitive [Fintype X] (μ : Measure X) [IsProbabilityMeasure μ]
    [SMulInvariantMeasure G X μ] (htrans : ∀ x y : X, ∃ g : G, g • x = y) :
    μ = (Fintype.card X : ℝ≥0∞)⁻¹ • Measure.count := by
  refine Measure.ext_of_singleton fun x => ?_
  rw [sing_uniform_of_transitive (G := G) μ htrans x]
  simp [Measure.smul_apply, one_div]

end Brockian.EquidistributionUniformity

