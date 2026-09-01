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

open Filter MeasureTheory Metric

/-! ## Auxiliary lemmas -/

/-- Superadditivity of `liminf` for two `ℝ≥0∞`-valued sequences. -/
theorem liminf_add_le_liminf_add_nat (u v : ℕ → ENNReal) :
    liminf u atTop + liminf v atTop ≤ liminf (fun n => u n + v n) atTop := by
  simp only [Filter.liminf_eq_iSup_iInf_of_nat]
  refine ENNReal.iSup_add_iSup_le ?_
  intro i j
  refine le_trans ?_ (le_iSup _ (max i j))
  refine le_iInf₂ (fun m hm => add_le_add ?_ ?_)
  · exact iInf₂_le m (le_trans (le_max_left i j) hm)
  · exact iInf₂_le m (le_trans (le_max_right i j) hm)

/-- Superadditivity of `liminf` for a finite sum of `ℝ≥0∞`-valued sequences. -/
theorem sum_liminf_le_liminf_sum {ι : Type*} (t : Finset ι) (f : ι → ℕ → ENNReal) :
    ∑ i ∈ t, liminf (fun n => f i n) atTop ≤ liminf (fun n => ∑ i ∈ t, f i n) atTop := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      refine le_trans (add_le_add_left ih _) ?_
      refine le_trans (liminf_add_le_liminf_add_nat _ _) ?_
      refine liminf_le_liminf ?_
      filter_upwards with n
      rw [Finset.sum_insert ha]

/-- A finite set in a metric space can be surrounded by pairwise disjoint balls of a common
positive radius. -/
theorem exists_radius_pairwise_disjoint_ball {X : Type*} [MetricSpace X] {s : Set X}
    (hs : s.Finite) :
    ∃ r > 0, ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (ball x r) (ball y r) := by
  obtain ⟨C, hC, hC2⟩ := hs.relatively_discrete
  set c : ENNReal := min C 1 with hc
  have hcpos : 0 < c := lt_min hC (by norm_num)
  have hcne : c ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  have hcr : 0 < c.toReal := ENNReal.toReal_pos hcpos.ne' hcne
  refine ⟨c.toReal / 2, by linarith, ?_⟩
  intro x hx y hy hxy
  refine Metric.ball_disjoint_ball ?_
  have h1 : c ≤ edist x y := le_trans (min_le_left _ _) (hC2 x hx y hy hxy)
  have h2 : c.toReal ≤ (edist x y).toReal := ENNReal.toReal_mono (edist_ne_top x y) h1
  rw [← dist_edist] at h2
  linarith

/-- **Energy count at concentration points.** If each measure `μ n` has total mass at most `E`
and `t` is a finite set of points at which the energy persistently concentrates with quantum `ε`
(i.e. every ball around such a point carries asymptotic mass at least `ε`), then
`(#t) * ε ≤ E`. -/
theorem card_mul_le_of_concentration {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : ℕ → Measure X) (E ε : ENNReal) (hE : ∀ n, μ n Set.univ ≤ E)
    (t : Finset X)
    (ht : ∀ x ∈ t, ∀ r > (0 : ℝ), ε ≤ liminf (fun n => μ n (ball x r)) atTop) :
    (t.card : ENNReal) * ε ≤ E := by
  classical
  obtain ⟨r, hr, hdisj⟩ := exists_radius_pairwise_disjoint_ball (s := (t : Set X)) t.finite_toSet
  -- for every `n`, the disjoint balls carry total mass at most `E`
  have hsum : ∀ n, ∑ x ∈ t, μ n (ball x r) ≤ E := by
    intro n
    have hbi : μ n (⋃ x ∈ t, ball x r) = ∑ x ∈ t, μ n (ball x r) :=
      measure_biUnion_finset (fun x hx y hy hxy => hdisj x hx y hy hxy)
        (fun x _ => measurableSet_ball)
    calc ∑ x ∈ t, μ n (ball x r) = μ n (⋃ x ∈ t, ball x r) := hbi.symm
      _ ≤ μ n Set.univ := measure_mono (Set.subset_univ _)
      _ ≤ E := hE n
  calc (t.card : ENNReal) * ε = ∑ _x ∈ t, ε := by
          rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ t, liminf (fun n => μ n (ball x r)) atTop :=
          Finset.sum_le_sum (fun x hx => ht x hx r hr)
    _ ≤ liminf (fun n => ∑ x ∈ t, μ n (ball x r)) atTop :=
          sum_liminf_le_liminf_sum t (fun x n => μ n (ball x r))
    _ ≤ liminf (fun _ : ℕ => E) atTop := liminf_le_liminf (by filter_upwards with n using hsum n)
    _ = E := liminf_const E

/-! ## Main result -/

/-- **Uhlenbeck bubbling: finiteness and counting of the blow-up set.**

Let `μ n` be the Yang–Mills energy densities (`|F(A n)|²` measures) of a sequence of connections
on a metric measure space `X`, with uniformly bounded total energy `E < ∞`.  Let `ε > 0` be the
energy quantum (given, e.g., by the `ε`-regularity theorem) and let `S` be the *blow-up set*:
the set of points at which every ball retains asymptotic energy at least `ε`.

Then `S` is finite, and the number of bubbling points is controlled by the energy:
`(#S) * ε ≤ E`.  In particular at most `E / ε` bubbles can form, which is the counting statement
underlying Uhlenbeck's compactness theorem (convergence away from finitely many points). -/
theorem uhlenbeck_bubbling {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ℕ → Measure X) (E ε : ENNReal) (hE : ∀ n, μ n Set.univ ≤ E) (hEtop : E ≠ ⊤)
    (hε : ε ≠ 0) (S : Set X)
    (hS : ∀ x ∈ S, ∀ r > (0 : ℝ), ε ≤ liminf (fun n => μ n (ball x r)) atTop) :
    S.Finite ∧ (S.ncard : ENNReal) * ε ≤ E := by
  classical
  have key : ∀ t : Finset X, (↑t : Set X) ⊆ S → (t.card : ENNReal) * ε ≤ E := by
    intro t ht
    exact card_mul_le_of_concentration μ E ε hE t (fun x hx => hS x (ht hx))
  have hfin : S.Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    -- the singleton case shows `ε ≤ E`, so `ε ≠ ⊤`
    obtain ⟨t1, ht1sub, ht1card⟩ := hinf.exists_subset_card_eq 1
    have hεE : ε ≤ E := by
      have := key t1 ht1sub
      rwa [ht1card, Nat.cast_one, one_mul] at this
    have hεtop : ε ≠ ⊤ := fun h => hEtop (top_le_iff.mp (h ▸ hεE))
    have hdiv : E / ε ≠ ⊤ := (ENNReal.div_lt_top hEtop hε).ne
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hdiv
    obtain ⟨t, htsub, htcard⟩ := hinf.exists_subset_card_eq N
    have h1 : (N : ENNReal) * ε ≤ E := by
      have := key t htsub
      rwa [htcard] at this
    have h2 : (N : ENNReal) ≤ E / ε := (ENNReal.le_div_iff_mul_le (Or.inl hε)
      (Or.inl hεtop)).mpr h1
    exact absurd h2 (not_le.mpr hN)
  refine ⟨hfin, ?_⟩
  have hsub : (↑hfin.toFinset : Set X) ⊆ S := by simp
  have := key hfin.toFinset hsub
  rwa [Set.Finite.card_toFinset, ← Set.Nat.card_coe_set_eq, Set.Nat.card_coe_set_eq,
    Set.ncard_eq_toFinset_card' ] at this

end Frontier

