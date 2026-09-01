/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory Metric

/-- **Quantization counting, finite form.** If `U x`, for `x` ranging over a finite set `T`,
are pairwise disjoint measurable sets each of measure at least `ε`, then `card T * ε` is at
most the total mass. -/
theorem finset_card_mul_le_measure_univ
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (ε : ENNReal)
    (T : Finset X) (U : X → Set X)
    (hmeas : ∀ x ∈ T, MeasurableSet (U x))
    (hdisj : (T : Set X).PairwiseDisjoint U)
    (hε : ∀ x ∈ T, ε ≤ μ (U x)) :
    (T.card : ENNReal) * ε ≤ μ Set.univ := by
  have h1 : μ (⋃ x ∈ T, U x) = ∑ x ∈ T, μ (U x) :=
    measure_biUnion_finset hdisj hmeas
  calc (T.card : ENNReal) * ε = ∑ _x ∈ T, ε := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ T, μ (U x) := Finset.sum_le_sum hε
    _ = μ (⋃ x ∈ T, U x) := h1.symm
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)

/-- **Separation.** Any finite set of points in a metric space admits a positive radius `r`
such that the `r`-balls around distinct points of the set are disjoint. -/
theorem exists_radius_pairwiseDisjoint_ball
    {X : Type*} [MetricSpace X] (T : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (T : Set X).PairwiseDisjoint (fun x => ball x r) := by
  classical
  set P : Finset (X × X) := (T ×ˢ T).filter (fun p => p.1 ≠ p.2) with hP
  by_cases hPe : P.Nonempty
  · set m : ℝ := P.inf' hPe (fun p => dist p.1 p.2) with hm
    have hmpos : 0 < m := by
      rw [hm, Finset.lt_inf'_iff]
      intro p hp
      have : p.1 ≠ p.2 := by
        have := (Finset.mem_filter.mp (hP ▸ hp)).2
        simpa using this
      exact dist_pos.mpr this
    refine ⟨m / 2, by positivity, ?_⟩
    intro x hx y hy hxy
    have hxT : x ∈ T := hx
    have hyT : y ∈ T := hy
    have hmem : (x, y) ∈ P := by
      rw [hP, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hxT, hyT⟩, hxy⟩
    have hle : m ≤ dist x y := by
      have := Finset.inf'_le (f := fun p : X × X => dist p.1 p.2) hmem
      simpa [hm] using this
    have : m / 2 + m / 2 ≤ dist x y := by linarith
    exact ball_disjoint_ball this
  · refine ⟨1, one_pos, ?_⟩
    intro x hx y hy hxy
    exact absurd ⟨(x, y), by
      rw [hP, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hx, hy⟩, hxy⟩⟩ hPe

/-- **Uhlenbeck bubbling: finiteness and quantization of the bubble set.**

Let `μ` be the (defect / curvature) energy measure of total energy at most `E < ∞` on
Euclidean `4`-space, arising as the limit of the Yang–Mills energy densities
`|F_{A_n}|² dvol` of a sequence of connections with uniformly bounded energy.
Let `S` be the *bubbling set*: the set of points at which at least the quantum of energy
`ε = 8π²` (the energy of a single instanton) concentrates in every ball around the point.

Then `S` is finite, and the number of bubbles obeys the quantization bound
`(#S) · 8π² ≤ E`; in particular `#S ≤ E / (8π²)`. -/
theorem uhlenbeck_bubbling
    (μ : Measure (EuclideanSpace ℝ (Fin 4))) (E : ENNReal)
    (hE : μ Set.univ ≤ E) (hEfin : E ≠ ⊤)
    (S : Set (EuclideanSpace ℝ (Fin 4)))
    (hS : ∀ x ∈ S, ∀ r : ℝ, 0 < r → ENNReal.ofReal (8 * π ^ 2) ≤ μ (ball x r)) :
    S.Finite ∧ (S.ncard : ENNReal) * ENNReal.ofReal (8 * π ^ 2) ≤ E := by
  classical
  set ε : ENNReal := ENNReal.ofReal (8 * π ^ 2) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef, ENNReal.ofReal_pos]
    have := Real.pi_pos
    positivity
  have hεne : ε ≠ 0 := hεpos.ne'
  have hεtop : ε ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the key bound for finite subsets
  have key : ∀ T : Finset (EuclideanSpace ℝ (Fin 4)), (T : Set _) ⊆ S →
      (T.card : ENNReal) * ε ≤ E := by
    intro T hT
    obtain ⟨r, hr, hdisj⟩ := exists_radius_pairwiseDisjoint_ball T
    refine le_trans ?_ hE
    refine finset_card_mul_le_measure_univ μ ε T (fun x => ball x r) ?_ hdisj ?_
    · intro x _
      exact measurableSet_ball
    · intro x hx
      exact hS x (hT hx) r hr
  have hfin : S.Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨n, hn⟩ : ∃ n : ℕ, E < (n : ENNReal) * ε := by
      have hdivne : E / ε ≠ ⊤ := by
        rw [ENNReal.div_eq_top]
        push_neg
        exact ⟨fun h => absurd h hεne, fun _ => hEfin⟩
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hdivne
      refine ⟨n, ?_⟩
      have h2 : ε * (E / ε) < ε * (n : ENNReal) := ENNReal.mul_lt_mul_right hεne hεtop hn
      rw [ENNReal.mul_div_cancel hεne hεtop] at h2
      rwa [mul_comm] at h2
    obtain ⟨T, hTS, hTcard⟩ := hinf.exists_subset_card_eq n
    have := key T hTS
    rw [hTcard] at this
    exact absurd this (not_le.mpr hn)
  refine ⟨hfin, ?_⟩
  have hkey := key hfin.toFinset (by simp)
  rwa [Set.ncard_eq_toFinset_card S hfin]

