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

/-
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Equidistribution Of BV Uniform
Category: Brockian (Literature Discharge)
Target: Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open MeasureTheory Filter Topology Set

namespace Brockian
namespace EquidistributionBVReduction

/-- The indicator function of the ray `(-∞, a)`, viewed as a real valued function on `ℝ`.
Restricted to `[0,1]` this is the indicator of the interval `[0, a)`. -/
noncomputable def indicatorIio (a : ℝ) : ℝ → ℝ := fun t => if t < a then 1 else 0

/-- The indicator of a ray is a function of bounded variation on `[0,1]`
(it is the negative of a monotone function). -/
theorem boundedVariationOn_indicatorIio (a : ℝ) :
    BoundedVariationOn (indicatorIio a) (Set.Icc 0 1) := by
  have hmono : MonotoneOn (fun t : ℝ => -(indicatorIio a t)) (Set.Icc 0 1) := by
    intro p _ q _ hpq
    simp only [indicatorIio]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · linarith
    · push_neg at h1; linarith
    · exact le_rfl
  have hle := hmono.eVariationOn_le (a := (0 : ℝ)) (b := 1) (by norm_num) (by norm_num)
  have hEq : eVariationOn (fun t : ℝ => -(indicatorIio a t)) (Set.Icc 0 1)
      = eVariationOn (indicatorIio a) (Set.Icc 0 1) := by
    unfold eVariationOn
    simp [edist_neg_neg]
  rw [Set.inter_eq_left.2 (fun t ht => ht), hEq] at hle
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

/-- The integral of the indicator of `[0, a)` over `[0,1]` is `a`, for `a ∈ [0,1]`. -/
theorem integral_indicatorIio {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ∫ t in (0 : ℝ)..1, indicatorIio a t = a := by
  obtain ⟨h0, h1⟩ := ha
  rw [intervalIntegral.integral_of_le (by norm_num)]
  rw [show (fun t : ℝ => indicatorIio a t)
      = Set.indicator (Set.Iio a) (fun _ => (1 : ℝ)) from by
    funext t; simp [indicatorIio, Set.indicator_apply]]
  rw [MeasureTheory.integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  have hset : Set.Iio a ∩ Set.Ioc (0 : ℝ) 1 = Set.Ioo 0 a := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
    exact ⟨fun ⟨h, h2, _⟩ => ⟨h2, h⟩, fun ⟨h2, h3⟩ => ⟨h3, h2, h3.le.trans h1⟩⟩
  rw [hset]
  simp [h0]

/-- Sums of the indicator of `[0, a)` along a sequence count the terms that are `< a`. -/
theorem sum_indicatorIio (x : ℕ → ℝ) (a : ℝ) (N : ℕ) :
    ∑ n ∈ Finset.range N, indicatorIio a (x n)
      = (({n ∈ Finset.range N | x n < a} : Finset ℕ).card : ℝ) := by
  classical
  simp [indicatorIio, Finset.sum_boole (p := fun n => x n < a) (s := Finset.range N) (R := ℝ)]

/-- **Equidistribution from the bounded-variation criterion.**

If the Birkhoff averages of a sequence `x : ℕ → ℝ` converge to the integral over `[0,1]`
for *every* function of bounded variation on `[0,1]`, then the sequence is equidistributed
in `[0,1]`: for every `a ∈ [0,1]`, the proportion of the first `N` terms lying in `[0, a)`
tends to `a`.

The named hypothesis is discharged by testing the assumption against the (bounded variation)
indicator functions of the intervals `[0, a)`. -/
theorem equidistribution_of_BV_uniform (x : ℕ → ℝ)
    (hBV : ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc 0 1) →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (x n)) / (N : ℝ)) atTop
        (𝓝 (∫ t in (0 : ℝ)..1, f t))) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun N : ℕ => (({n ∈ Finset.range N | x n < a} : Finset ℕ).card : ℝ) / (N : ℝ))
        atTop (𝓝 a) := by
  classical
  intro a ha
  have h := hBV (indicatorIio a) (boundedVariationOn_indicatorIio a)
  rw [integral_indicatorIio ha] at h
  simpa [sum_indicatorIio x a] using h

end EquidistributionBVReduction
end Brockian

