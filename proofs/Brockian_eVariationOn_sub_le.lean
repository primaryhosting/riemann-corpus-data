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
# Reduction of equidistribution mod 1 to test functions of bounded variation

This file contains an unconditional proof that a sequence `x : ℕ → ℝ` whose Cesàro averages
against every test function of bounded variation on `[0,1]` converge to the corresponding
integral is uniformly distributed (equidistributed) mod `1`.

The main statement is `Brockian.EquidistributionBVReduction.equidistribution_of_BV_uniform`.
It is deduced from the formally stronger
`Brockian.EquidistributionBVReduction.equidistribution_of_monotone_uniform`, where only
monotone test functions are used.

All auxiliary facts are proved here, with no assumed black boxes; in particular the
subadditivity of the (extended) variation with respect to differences of functions,
the bounded variation of indicator functions of intervals, and the relevant integrals.
-/

open Filter Set MeasureTheory
open scoped Topology ENNReal

namespace Brockian
namespace EquidistributionBVReduction

/-! ## Bounded variation of a step function -/

/-- Subadditivity of the extended variation for a difference of two real valued functions. -/
theorem eVariationOn_sub_le {α : Type*} [LinearOrder α] (f g : α → ℝ) (s : Set α) :
    eVariationOn (fun t => f t - g t) s ≤ eVariationOn f s + eVariationOn g s := by
  refine iSup_le ?_
  rintro ⟨n, u, hu, us⟩
  have key : ∀ i, edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i))
      ≤ edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i)) := by
    intro i
    simp only [edist_dist, Real.dist_eq]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |f (u (i + 1)) - g (u (i + 1)) - (f (u i) - g (u i))|
        = |(f (u (i + 1)) - f (u i)) + -(g (u (i + 1)) - g (u i))| := by ring_nf
      _ ≤ |f (u (i + 1)) - f (u i)| + |-(g (u (i + 1)) - g (u i))| := abs_add_le _ _
      _ = |f (u (i + 1)) - f (u i)| + |g (u (i + 1)) - g (u i)| := by rw [abs_neg]
  calc (∑ i ∈ Finset.range n, edist (f (u (i + 1)) - g (u (i + 1))) (f (u i) - g (u i)))
      ≤ ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))
          + ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le f n hu us) (eVariationOn.sum_le g n hu us)

/-- The right-continuous unit step function jumping at `c`. -/
noncomputable def step (c : ℝ) : ℝ → ℝ := fun t => if c ≤ t then 1 else 0

theorem monotone_step (c : ℝ) : Monotone (step c) := by
  intro p q hpq
  unfold step
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (h1.trans hpq) h2
  · norm_num
  · exact le_rfl

theorem eVariationOn_step_le (c : ℝ) : eVariationOn (step c) (Set.Icc (0:ℝ) 1) ≤ 1 := by
  have h := MonotoneOn.eVariationOn_le ((monotone_step c).monotoneOn (Set.Icc (0:ℝ) 1))
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  rw [Set.inter_self] at h
  refine h.trans ?_
  have hle : step c 1 - step c 0 ≤ 1 := by
    unfold step; split_ifs <;> norm_num
  calc ENNReal.ofReal (step c 1 - step c 0) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal hle
    _ = 1 := by simp

/-- The indicator function of `Set.Ico a b` agrees on `[0,1]` with a difference of two
monotone step functions. -/
theorem indicator_Ico_eqOn (a b : ℝ) (hab : a ≤ b) :
    Set.EqOn (Set.indicator (Set.Ico a b) (fun _ => (1:ℝ)))
      (fun t => step a t - step b t) (Set.Icc (0:ℝ) 1) := by
  intro t _
  rcases lt_or_ge t a with h | h
  · have h' : t < b := lt_of_lt_of_le h hab
    simp [step, not_le.2 h, not_le.2 h']
  · rcases lt_or_ge t b with h2 | h2
    · simp [step, h, h2, not_le.2 h2]
    · simp [step, h, h2, not_lt.2 h2]

theorem boundedVariationOn_indicator_Ico (a b : ℝ) (hab : a ≤ b) :
    BoundedVariationOn (Set.indicator (Set.Ico a b) (fun _ => (1:ℝ))) (Set.Icc (0:ℝ) 1) := by
  have heq := eVariationOn.eq_of_eqOn (indicator_Ico_eqOn a b hab)
  have hle : eVariationOn (fun t => step a t - step b t) (Set.Icc (0:ℝ) 1) ≤ 1 + 1 :=
    (eVariationOn_sub_le (step a) (step b) _).trans
      (add_le_add (eVariationOn_step_le a) (eVariationOn_step_le b))
  refine ne_of_lt ?_
  rw [heq]
  exact lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨by simp, by simp⟩)

/-! ## The integral of the indicator -/

theorem integral_indicator_Ico (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    ∫ t in (0:ℝ)..1, Set.indicator (Set.Ico a b) (fun _ => (1:ℝ)) t = b - a := by
  rw [intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_indicator measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico]
  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
  have h1 : volume (Set.Ico a b ∩ Set.Ioc (0:ℝ) 1) = ENNReal.ofReal (b - a) := by
    refine le_antisymm ?_ ?_
    · refine le_trans (measure_mono (t := Set.Icc a b) ?_) ?_
      · rintro t ⟨⟨h1, h2⟩, -⟩
        exact ⟨h1, h2.le⟩
      · simp [Real.volume_Icc]
    · refine le_trans ?_ (measure_mono (s := Set.Ioo a b) ?_)
      · simp [Real.volume_Ioo]
      · rintro t ⟨h1, h2⟩
        exact ⟨⟨h1.le, h2⟩, lt_of_le_of_lt ha h1, h2.le.trans hb⟩
  simp only [MeasureTheory.Measure.real, Measure.restrict_apply_univ, h1,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a)]

theorem integral_step (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) : ∫ t in (0:ℝ)..1, step c t = 1 - c := by
  have hst : step c = Set.indicator (Set.Ici c) (fun _ => (1:ℝ)) := by
    funext t; simp [step, Set.indicator_apply, Set.mem_Ici]
  rw [hst, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  simp only [MeasureTheory.integral_const, smul_eq_mul, mul_one]
  have h1 : volume (Set.Ici c ∩ Set.Ioc (0:ℝ) 1) = ENNReal.ofReal (1 - c) := by
    refine le_antisymm ?_ ?_
    · refine le_trans (measure_mono (t := Set.Icc c 1) ?_) ?_
      · rintro t ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
      · simp [Real.volume_Icc]
    · refine le_trans ?_ (measure_mono (s := Set.Ioo c 1) ?_)
      · simp [Real.volume_Ioo]
      · rintro t ⟨h1, h2⟩
        exact ⟨h1.le, lt_of_le_of_lt hc h1, h2.le⟩
  simp only [MeasureTheory.Measure.real, Measure.restrict_apply_univ, h1,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - c)]

/-! ## Equidistribution -/

/-- A sequence `x : ℕ → ℝ` is *equidistributed mod 1* if, for every subinterval `[a,b) ⊆ [0,1]`,
the proportion of the first `N` fractional parts `Int.fract (x n)` lying in `[a, b)` converges
to the length `b - a`. -/
def EquidistributedMod1 (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / N)
      atTop (𝓝 (b - a))

/-- The hypothesis that the Cesàro averages of `x` against every test function of bounded
variation on `[0,1]` converge to the integral of the test function. -/
def BVTestConvergence (x : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0:ℝ) 1) →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N)
      atTop (𝓝 (∫ t in (0:ℝ)..1, f t))

theorem sum_indicator_eq_card (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, Set.indicator (Set.Ico a b) (fun _ => (1:ℝ)) (Int.fract (x n)))
      = (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) := by
  classical
  simp only [Set.indicator_apply]
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
  simp

/-- The (formally weaker) hypothesis that the Cesàro averages of `x` against every test function
that is monotone on `[0,1]` converge to the integral of the test function. -/
def MonotoneTestConvergence (x : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℝ, MonotoneOn f (Set.Icc (0:ℝ) 1) →
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N)
      atTop (𝓝 (∫ t in (0:ℝ)..1, f t))

theorem boundedVariationOn_of_monotoneOn {f : ℝ → ℝ} (hf : MonotoneOn f (Set.Icc (0:ℝ) 1)) :
    BoundedVariationOn f (Set.Icc (0:ℝ) 1) := by
  have h := MonotoneOn.eVariationOn_le hf
    (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
  rw [Set.inter_self] at h
  exact ne_of_lt (lt_of_le_of_lt h ENNReal.ofReal_lt_top)

/-- A monotone test function hypothesis already forces equidistribution mod `1`. -/
theorem equidistribution_of_monotone_uniform (x : ℕ → ℝ) (h : MonotoneTestConvergence x) :
    EquidistributedMod1 x := by
  intro a b ha hab hb
  have hA := h (step a) ((monotone_step a).monotoneOn _)
  have hB := h (step b) ((monotone_step b).monotoneOn _)
  rw [integral_step a ha (hab.trans hb)] at hA
  rw [integral_step b (ha.trans hab) hb] at hB
  have hsub := hA.sub hB
  have hfract : ∀ n : ℕ, Int.fract (x n) ∈ Set.Icc (0:ℝ) 1 := fun n =>
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hfun : (fun N : ℕ => (∑ n ∈ Finset.range N, step a (Int.fract (x n))) / N
        - (∑ n ∈ Finset.range N, step b (Int.fract (x n))) / N)
      = fun N : ℕ =>
        (((Finset.range N).filter fun n => Int.fract (x n) ∈ Set.Ico a b).card : ℝ) / N := by
    funext N
    rw [div_sub_div_same, ← Finset.sum_sub_distrib, ← sum_indicator_eq_card x a b N]
    refine congrArg (· / (N : ℝ)) (Finset.sum_congr rfl fun n _ => ?_)
    exact (indicator_Ico_eqOn a b hab (hfract n)).symm
  rw [hfun] at hsub
  have hval : 1 - a - (1 - b) = b - a := by ring
  rwa [hval] at hsub

/-- **Reduction of equidistribution to bounded variation test functions.**
If the Cesàro averages of a sequence against every function of bounded variation on `[0,1]`
converge to the corresponding integral, then the sequence is equidistributed mod `1`. -/
theorem equidistribution_of_BV_uniform (x : ℕ → ℝ) (h : BVTestConvergence x) :
    EquidistributedMod1 x :=
  equidistribution_of_monotone_uniform x fun f hf => h f (boundedVariationOn_of_monotoneOn hf)

/-- Sanity check: the notion of equidistribution above is not vacuous; the constant sequence
`0` is not equidistributed mod `1`. -/
theorem not_equidistributedMod1_const_zero : ¬ EquidistributedMod1 (fun _ => (0:ℝ)) := by
  intro h
  have hlim := h (1/2) 1 (by norm_num) (by norm_num) le_rfl
  have hz : (fun N : ℕ =>
      (((Finset.range N).filter
        fun n => Int.fract ((fun _ => (0:ℝ)) n) ∈ Set.Ico (1/2:ℝ) 1).card : ℝ) / N)
      = fun _ : ℕ => (0:ℝ) := by
    funext N
    simp [Set.mem_Ico]
  rw [hz] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  norm_num at this

end EquidistributionBVReduction
end Brockian

