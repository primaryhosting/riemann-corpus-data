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

/-!
# Ham–Sandwich: statement and the one-dimensional base case

The Ham–Sandwich theorem states that any `n` finite (Borel) measures on `ℝⁿ` can be
simultaneously bisected by a single affine hyperplane.  Here "bisected by the hyperplane
`{x | ⟪v, x⟫ = c}`" is taken in the usual measure-theoretic sense, which is the correct
formulation for measures that may have atoms: each of the two *open* half-spaces carries at
most half of the total mass (equivalently, each *closed* half-space carries at least half).

This file gives the formal statement `HamSandwichProperty n` in arbitrary dimension and a
complete, axiom-clean proof of the base case `n = 1` (`Frontier.ham_sandwich`), where the
hyperplane is a point and bisection is the existence of a median.
-/

namespace Frontier

open MeasureTheory Set Filter

/-- The hyperplane `{x | ⟪v, x⟫ = c}` bisects the measure `μ`: both open half-spaces
determined by it carry at most half of the total mass of `μ`. -/
def BisectedBy {n : ℕ} (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)))
    (v : EuclideanSpace ℝ (Fin n)) (c : ℝ) : Prop :=
  μ {x | inner ℝ v x < c} ≤ μ Set.univ / 2 ∧ μ {x | c < inner ℝ v x} ≤ μ Set.univ / 2

/-- The Ham–Sandwich property in dimension `n`: any `n` finite measures on `ℝⁿ` are
simultaneously bisected by one affine hyperplane `{x | ⟪v, x⟫ = c}` with `v ≠ 0`. -/
def HamSandwichProperty (n : ℕ) : Prop :=
  ∀ μ : Fin n → MeasureTheory.Measure (EuclideanSpace ℝ (Fin n)),
    (∀ i, MeasureTheory.IsFiniteMeasure (μ i)) →
      ∃ v : EuclideanSpace ℝ (Fin n), ∃ c : ℝ, v ≠ 0 ∧ ∀ i, BisectedBy (μ i) v c

/-- Every finite Borel measure on `ℝ` has a median: a point `c` such that both `Iio c` and
`Ioi c` carry at most half of the total mass. -/
theorem exists_median (μ : MeasureTheory.Measure ℝ) [MeasureTheory.IsFiniteMeasure μ] :
    ∃ c : ℝ, μ (Set.Iio c) ≤ μ Set.univ / 2 ∧ μ (Set.Ioi c) ≤ μ Set.univ / 2 := by
  set m := μ Set.univ with hm
  rcases eq_or_lt_of_le (zero_le m) with h0 | hpos
  · refine ⟨0, ?_, ?_⟩ <;>
    · refine le_trans (measure_mono (Set.subset_univ _)) ?_
      rw [← hm, ← h0]; simp
  have hhalf : 0 < m / 2 := ENNReal.div_pos (ne_of_gt hpos) (by norm_num)
  set S : Set ℝ := {t : ℝ | m / 2 ≤ μ (Set.Iic t)} with hS
  have hne : S.Nonempty := by
    have h1 := MeasureTheory.tendsto_measure_Iic_atTop μ
    have h2 : m / 2 < m := ENNReal.half_lt_self (ne_of_gt hpos) (measure_ne_top _ _)
    obtain ⟨t, ht⟩ := (h1.eventually (eventually_gt_nhds h2)).exists
    exact ⟨t, le_of_lt ht⟩
  have hbdd : BddBelow S := by
    have hi : (⋂ t : ℝ, Set.Iic t) = (∅ : Set ℝ) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_forall]
      exact ⟨x - 1, by linarith⟩
    have h1 := MeasureTheory.tendsto_measure_iInter_atBot (μ := μ) (s := fun t : ℝ => Set.Iic t)
      (fun _ => nullMeasurableSet_Iic) (fun _ _ hab => Set.Iic_subset_Iic.2 hab)
      ⟨0, measure_ne_top _ _⟩
    rw [hi] at h1
    simp only [measure_empty] at h1
    obtain ⟨t, ht⟩ := (h1.eventually (eventually_lt_nhds hhalf)).exists
    refine ⟨t, fun s hs => ?_⟩
    by_contra hcon
    push_neg at hcon
    exact absurd (hs.trans (measure_mono (Set.Iic_subset_Iic.2 hcon.le))) (not_le.2 ht)
  have key : ∀ s : ℝ, s ∈ S → μ (Set.Ioi s) ≤ m / 2 := by
    intro s hs
    have h : μ (Set.Iic s) + μ (Set.Ioi s) = m := by
      rw [← measure_union (by simp [Set.disjoint_left]) measurableSet_Ioi, Set.Iic_union_Ioi]
    have h2 : m / 2 + μ (Set.Ioi s) ≤ m / 2 + m / 2 := by
      calc m / 2 + μ (Set.Ioi s) ≤ μ (Set.Iic s) + μ (Set.Ioi s) := by gcongr; exact hs
        _ = m := h
        _ = m / 2 + m / 2 := (ENNReal.add_halves m).symm
    exact (ENNReal.add_le_add_iff_left (by finiteness)).1 h2
  have hstep : ∀ a b : ℕ, a ≤ b → (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
    intro a b hab
    have hab' : ((a : ℝ) + 1) ≤ ((b : ℝ) + 1) := by
      have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.2 hab
      linarith
    exact one_div_le_one_div_of_le (by positivity) hab'
  refine ⟨sInf S, ?_, ?_⟩
  · have hsub : Set.Iio (sInf S) ⊆ ⋃ n : ℕ, Set.Iic (sInf S - 1 / ((n : ℝ) + 1)) := by
      intro x hx
      simp only [Set.mem_Iio] at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < sInf S - x by linarith)
      exact Set.mem_iUnion.2 ⟨n, by simp only [Set.mem_Iic]; linarith⟩
    refine le_trans (measure_mono hsub) ?_
    have hmono : Monotone (fun n : ℕ => Set.Iic (sInf S - 1 / ((n : ℝ) + 1))) := by
      intro a b hab
      exact Set.Iic_subset_Iic.2 (by have := hstep a b hab; linarith)
    rw [hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    have hlt : sInf S - 1 / ((n : ℝ) + 1) < sInf S := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    have hnot : sInf S - 1 / ((n : ℝ) + 1) ∉ S := fun hmem =>
      absurd (csInf_le hbdd hmem) (not_le.2 hlt)
    simp only [hS, Set.mem_setOf_eq, not_le] at hnot
    exact hnot.le
  · have hsub : Set.Ioi (sInf S) ⊆ ⋃ n : ℕ, Set.Ici (sInf S + 1 / ((n : ℝ) + 1)) := by
      intro x hx
      simp only [Set.mem_Ioi] at hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < x - sInf S by linarith)
      exact Set.mem_iUnion.2 ⟨n, by simp only [Set.mem_Ici]; linarith⟩
    refine le_trans (measure_mono hsub) ?_
    have hmono : Monotone (fun n : ℕ => Set.Ici (sInf S + 1 / ((n : ℝ) + 1))) := by
      intro a b hab
      exact Set.Ici_subset_Ici.2 (by have := hstep a b hab; linarith)
    rw [hmono.measure_iUnion]
    refine iSup_le fun n => ?_
    obtain ⟨s, hsS, hs⟩ := Real.lt_sInf_add_pos hne (show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity)
    refine le_trans (measure_mono ?_) (key s hsS)
    intro x hx
    simp only [Set.mem_Ici] at hx
    simp only [Set.mem_Ioi]
    linarith

/-- **Ham–Sandwich, base case `n = 1`.**  A single finite measure on the line `ℝ¹` is bisected
by a hyperplane (i.e. by a point): there is a nonzero direction `v` and a level `c` such that
each of the two open half-lines `{x | ⟪v, x⟫ < c}` and `{x | c < ⟪v, x⟫}` carries at most half
of the total mass. -/
theorem ham_sandwich : HamSandwichProperty 1 := by
  intro μ hμ
  haveI := hμ 0
  set f : EuclideanSpace ℝ (Fin 1) → ℝ := fun x => x 0 with hf
  have hmeas : Measurable f := by fun_prop
  set ν : MeasureTheory.Measure ℝ := (μ 0).map f with hν
  haveI : MeasureTheory.IsFiniteMeasure ν := by rw [hν]; infer_instance
  obtain ⟨c, hlt, hgt⟩ := exists_median ν
  refine ⟨EuclideanSpace.single 0 (1 : ℝ), c, by simp, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have hinner : ∀ x : EuclideanSpace ℝ (Fin 1),
      inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x = f x := by
    intro x; simp [hf, EuclideanSpace.inner_single_left]
  have huniv : ν Set.univ = μ 0 Set.univ := by
    rw [hν, MeasureTheory.Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ]
  constructor
  · have : {x : EuclideanSpace ℝ (Fin 1) | inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x < c}
        = f ⁻¹' (Set.Iio c) := by
      ext x; simp [hinner x, Set.mem_Iio]
    rw [this, ← MeasureTheory.Measure.map_apply hmeas measurableSet_Iio, ← hν, ← huniv]
    exact hlt
  · have : {x : EuclideanSpace ℝ (Fin 1) | c < inner ℝ (EuclideanSpace.single 0 (1 : ℝ)) x}
        = f ⁻¹' (Set.Ioi c) := by
      ext x; simp [hinner x, Set.mem_Ioi]
    rw [this, ← MeasureTheory.Measure.map_apply hmeas measurableSet_Ioi, ← hν, ← huniv]
    exact hgt

end Frontier

