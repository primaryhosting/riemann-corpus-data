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
# Equidistribution of irrational rotations, and the density of configuration counts

This file proves Weyl's equidistribution theorem for the sequence `n ↦ {n α}` (`α` irrational)
and deduces the unconditional statement `configCount_density_of_BV`: the density of the set of
`n < N` with `{n α} ∈ [a, b)` tends to `b - a`.

The indicator of an interval is the basic example of a function of bounded variation, and the
"BV reduction" is implemented here through the portmanteau theorem: the empirical measures of
the orbit converge weakly to Haar measure (proved via the Fourier/Weyl criterion), hence the
measures of any arc whose boundary is Haar-null converge.
-/

namespace Brockian
namespace EquidistributionBVReduction

open Filter MeasureTheory Set Topology AddCircle
open scoped BigOperators ENNReal NNReal

/-- The point `n • α` of the circle `ℝ / ℤ`. -/
noncomputable def orbitPoint (alpha : ℝ) (n : ℕ) : AddCircle (1 : ℝ) :=
  (((n : ℝ) * alpha : ℝ) : AddCircle (1:ℝ))

/-- The number of `n < N` such that the fractional part of `n * α` lies in `[a, b)`. -/
noncomputable def configCount (alpha a b : ℝ) (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * alpha) ∈ Set.Ico a b).card

/-- The arc of `ℝ / ℤ` given by the image of `[a, b)`. -/
def arc (a b : ℝ) : Set (AddCircle (1 : ℝ)) :=
  (fun x : ℝ => (x : AddCircle (1:ℝ))) '' Set.Ico a b

/-- The empirical measure of the first `N` points of the orbit. -/
noncomputable def empMeasure (alpha : ℝ) (N : ℕ) : Measure (AddCircle (1 : ℝ)) :=
  (N : ℝ≥0∞)⁻¹ • ∑ n ∈ Finset.range N, Measure.dirac (orbitPoint alpha n)

/-! ### Haar measure on the circle of length one -/

lemma haar_eq_volume :
    (haarAddCircle : Measure (AddCircle (1:ℝ))) = (volume : Measure (AddCircle (1:ℝ))) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simp

instance : IsProbabilityMeasure (volume : Measure (AddCircle (1:ℝ))) := by
  rw [← haar_eq_volume]; infer_instance

lemma haar_singleton (x : AddCircle (1:ℝ)) :
    (haarAddCircle : Measure (AddCircle (1:ℝ))) {x} = 0 := by
  rw [haar_eq_volume]
  simpa using AddCircle.volume_closedBall (T := (1:ℝ)) (x := x) 0

/-! ### The Weyl criterion -/

/-- Averages of a nontrivial character along an irrational rotation orbit tend to zero. -/
lemma tendsto_avg_fourier {alpha : ℝ} (hirr : Irrational alpha) {k : ℤ} (hk : k ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier k (orbitPoint alpha n))
      atTop (𝓝 0) := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * alpha) with hz
  have hzn : ∀ n : ℕ, (fourier k (orbitPoint alpha n) : ℂ) = z ^ n := by
    intro n
    rw [orbitPoint, fourier_coe_apply, hz, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hz1 : z ≠ 1 := by
    intro h
    rw [hz, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hpi : (2:ℂ) * Real.pi * Complex.I ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hkm : (k : ℂ) * alpha = m := by
      have : (2 * (Real.pi:ℂ) * Complex.I) * ((k:ℂ) * alpha)
          = (2 * (Real.pi:ℂ) * Complex.I) * m := by
        rw [show (2 * (Real.pi:ℂ) * Complex.I) * ((k:ℂ) * alpha)
            = 2 * (Real.pi:ℂ) * Complex.I * k * alpha by ring, hm]
        ring
      exact mul_left_cancel₀ hpi this
    have hkm' : (k : ℝ) * alpha = m := by exact_mod_cast hkm
    have halpha : alpha = (m : ℝ) / k := by
      field_simp at hkm' ⊢
      linarith [hkm']
    rw [halpha] at hirr
    exact Rat.not_irrational ((m : ℚ)/(k:ℚ))
      (by convert hirr using 2; push_cast; ring)
  have hnorm : ‖z‖ = 1 := by
    rw [hz, Complex.norm_exp]
    simp [Complex.mul_re]
  have hzsub : (0:ℝ) < ‖z - 1‖ := by simpa [sub_eq_zero] using hz1
  simp only [hzn]
  refine squeeze_zero_norm (a := fun N : ℕ => (2 / ‖z - 1‖) / N) (fun N => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat _)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hS : ‖∑ n ∈ Finset.range N, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
    rw [geom_sum_eq hz1 N, norm_div]
    gcongr
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hnorm]
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
  exact (div_le_div_iff_of_pos_right hNpos).mpr hS

/-- The average of `f` over the first `N` points of the orbit. -/
noncomputable def orbitAvg (alpha : ℝ) (f : C(AddCircle (1:ℝ), ℂ)) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (orbitPoint alpha n)

lemma integrable_continuousMap (f : C(AddCircle (1:ℝ), ℂ)) : Integrable f haarAddCircle :=
  (map_continuous f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integral_fourier (k : ℤ) :
    ∫ x, (fourier k x : ℂ) ∂(haarAddCircle : Measure (AddCircle (1:ℝ)))
      = if k = 0 then 1 else 0 := by
  have h0 := congrFun (fourierCoeff_fourier (T := (1:ℝ)) k) 0
  rw [fourierCoeff] at h0
  simp only [neg_zero, fourier_zero, one_smul] at h0
  rw [h0]
  by_cases hk : k = 0 <;> simp [hk, Pi.single_apply, eq_comm]

/-- Weyl's theorem for trigonometric polynomials. -/
lemma tendsto_orbitAvg_of_mem_span {alpha : ℝ} (hirr : Irrational alpha)
    (f : C(AddCircle (1:ℝ), ℂ)) (hf : f ∈ Submodule.span ℂ (Set.range (@fourier 1))) :
    Tendsto (orbitAvg alpha f) atTop (𝓝 (∫ x, f x ∂haarAddCircle)) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [integral_fourier]
      by_cases hk : k = 0
      · subst hk
        have h1 : orbitAvg alpha (fourier 0) =ᶠ[atTop] (fun _ => (1:ℂ)) := by
          filter_upwards [eventually_gt_atTop 0] with N hN
          have hN' : (N:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
          simp [orbitAvg, hN']
        simpa using Tendsto.congr' h1.symm tendsto_const_nhds
      · simpa [if_neg hk, orbitAvg] using tendsto_avg_fourier hirr hk
  | zero =>
      have h : ∀ N, orbitAvg alpha 0 N = 0 := by intro N; simp [orbitAvg]
      simpa using Tendsto.congr (fun N => (h N).symm) (tendsto_const_nhds (x := (0:ℂ)))
  | add x y hx hy ihx ihy =>
      have h : ∀ N, orbitAvg alpha x N + orbitAvg alpha y N = orbitAvg alpha (x + y) N := by
        intro N; simp [orbitAvg, Finset.sum_add_distrib, mul_add]
      have hint : (∫ t, (x + y) t ∂(haarAddCircle : Measure (AddCircle (1:ℝ))))
          = (∫ t, x t ∂(haarAddCircle : Measure (AddCircle (1:ℝ)))) + ∫ t, y t ∂haarAddCircle := by
        simp only [ContinuousMap.add_apply]
        exact integral_add (integrable_continuousMap x) (integrable_continuousMap y)
      rw [hint]
      exact Tendsto.congr h (ihx.add ihy)
  | smul c x hx ihx =>
      have h : ∀ N, c * orbitAvg alpha x N = orbitAvg alpha (c • x) N := by
        intro N; simp [orbitAvg, Finset.mul_sum, mul_left_comm]
      have hint : (∫ t, (c • x) t ∂(haarAddCircle : Measure (AddCircle (1:ℝ))))
          = c * ∫ t, x t ∂(haarAddCircle : Measure (AddCircle (1:ℝ))) := by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact integral_const_mul c _
      rw [hint]
      exact Tendsto.congr h (ihx.const_mul c)

lemma orbitAvg_dist (alpha : ℝ) (f g : C(AddCircle (1:ℝ), ℂ)) (N : ℕ) :
    dist (orbitAvg alpha f N) (orbitAvg alpha g N) ≤ ‖f - g‖ := by
  rw [dist_eq_norm, orbitAvg, orbitAvg, ← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv,
    Complex.norm_natCast]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [norm_nonneg]
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hbound : ‖∑ n ∈ Finset.range N, (f (orbitPoint alpha n) - g (orbitPoint alpha n))‖
      ≤ N * ‖f - g‖ := by
    calc ‖∑ n ∈ Finset.range N, (f (orbitPoint alpha n) - g (orbitPoint alpha n))‖
        ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ := by
          refine norm_sum_le_of_le _ (fun i _ => ?_)
          simpa using ContinuousMap.norm_coe_le_norm (f - g) (orbitPoint alpha i)
      _ = N * ‖f - g‖ := by simp
  calc (N:ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, (f (orbitPoint alpha n) - g (orbitPoint alpha n))‖
      ≤ (N:ℝ)⁻¹ * (N * ‖f - g‖) := by gcongr
    _ = ‖f - g‖ := by field_simp

lemma integral_dist (f g : C(AddCircle (1:ℝ), ℂ)) :
    dist (∫ x, f x ∂(haarAddCircle : Measure (AddCircle (1:ℝ))))
      (∫ x, g x ∂(haarAddCircle : Measure (AddCircle (1:ℝ)))) ≤ ‖f - g‖ := by
  rw [dist_eq_norm, ← integral_sub (integrable_continuousMap f) (integrable_continuousMap g)]
  have h : ∀ x, ‖f x - g x‖ ≤ ‖f - g‖ := by
    intro x
    simpa using ContinuousMap.norm_coe_le_norm (f - g) x
  simpa using norm_integral_le_of_norm_le_const (μ := (haarAddCircle : Measure (AddCircle (1:ℝ))))
    (C := ‖f - g‖) (ae_of_all _ h)

/-- A `3ε` argument: a sequence uniformly approximated by convergent sequences converges. -/
lemma tendsto_of_approx {u : ℕ → ℂ} {L : ℂ}
    (h : ∀ ε > (0:ℝ), ∃ (v : ℕ → ℂ) (M : ℂ), Tendsto v atTop (𝓝 M) ∧
      (∀ n, dist (u n) (v n) ≤ ε) ∧ dist M L ≤ ε) :
    Tendsto u atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨v, M, hv, hd, hML⟩ := h (ε/3) (by linarith)
  rw [Metric.tendsto_atTop] at hv
  obtain ⟨N, hN⟩ := hv (ε/3) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hd n
  have h2 := hN n hn
  calc dist (u n) L ≤ dist (u n) (v n) + dist (v n) M + dist M L := dist_triangle4 _ _ _ _
    _ < ε := by linarith

/-- Weyl's theorem for continuous functions: the orbit averages of a continuous function
converge to its Haar integral. -/
theorem tendsto_avg_continuous {alpha : ℝ} (hirr : Irrational alpha) (f : C(AddCircle (1:ℝ), ℂ)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f (orbitPoint alpha n))
      atTop (𝓝 (∫ x, f x ∂haarAddCircle)) := by
  have hdense : f ∈ closure ((Submodule.span ℂ (Set.range (@fourier 1))) :
      Set C(AddCircle (1:ℝ), ℂ)) := by
    have h := span_fourier_closure_eq_top (T := (1:ℝ))
    have h' : ((Submodule.span ℂ (Set.range (@fourier 1))).topologicalClosure :
        Set C(AddCircle (1:ℝ), ℂ)) = (⊤ : Submodule ℂ C(AddCircle (1:ℝ), ℂ)) := by rw [h]
    rw [Submodule.topologicalClosure_coe] at h'
    rw [h']
    trivial
  refine tendsto_of_approx (u := orbitAvg alpha f) ?_
  intro ε hε
  rw [Metric.mem_closure_iff] at hdense
  obtain ⟨g, hg, hfg⟩ := hdense ε hε
  refine ⟨orbitAvg alpha g, ∫ x, g x ∂haarAddCircle,
    tendsto_orbitAvg_of_mem_span hirr g hg, fun n => ?_, ?_⟩
  · exact le_trans (orbitAvg_dist alpha f g n) (by rw [← dist_eq_norm]; exact hfg.le)
  · exact le_trans (integral_dist g f) (by rw [← dist_eq_norm, dist_comm]; exact hfg.le)

/-! ### Empirical measures -/

instance empMeasure_isProbabilityMeasure (alpha : ℝ) (k : ℕ) :
    IsProbabilityMeasure (empMeasure alpha (k+1)) := by
  constructor
  rw [empMeasure, Measure.smul_apply, Measure.finset_sum_apply]
  simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
    smul_eq_mul]
  rw [ENNReal.inv_mul_cancel] <;> simp

lemma integral_empMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (alpha : ℝ) (N : ℕ) (f : AddCircle (1:ℝ) → E) :
    ∫ x, f x ∂(empMeasure alpha N) = (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, f (orbitPoint alpha n) := by
  rw [empMeasure, integral_smul_measure,
    integral_finset_sum_measure (fun i _ => integrable_dirac (by simp))]
  simp [integral_dirac]

/-- The empirical measures, as probability measures. -/
noncomputable def empProb (alpha : ℝ) (k : ℕ) : ProbabilityMeasure (AddCircle (1:ℝ)) :=
  ⟨empMeasure alpha (k+1), empMeasure_isProbabilityMeasure alpha k⟩

/-- Haar measure as a probability measure. -/
noncomputable def haarProb : ProbabilityMeasure (AddCircle (1:ℝ)) :=
  ⟨haarAddCircle, by infer_instance⟩

/-- The empirical measures converge weakly to Haar measure. -/
theorem tendsto_empProb {alpha : ℝ} (hirr : Irrational alpha) :
    Tendsto (empProb alpha) atTop (𝓝 haarProb) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  set g : C(AddCircle (1:ℝ), ℂ) :=
    ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ with hg
  have hc := tendsto_avg_continuous hirr g
  have hint : (∫ x, g x ∂(haarAddCircle : Measure (AddCircle (1:ℝ))))
      = ((∫ x, f x ∂(haarAddCircle : Measure (AddCircle (1:ℝ))) : ℝ) : ℂ) :=
    integral_complex_ofReal
  rw [hint] at hc
  have hreal : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f (orbitPoint alpha n))
      atTop (𝓝 (∫ x, f x ∂(haarAddCircle : Measure (AddCircle (1:ℝ))))) := by
    refine tendsto_ofReal_iff.mp ?_
    convert hc using 2 with N
    simp only [hg, ContinuousMap.coe_mk]
    push_cast
    ring
  refine (hreal.comp (tendsto_add_atTop_nat 1)).congr (fun k => ?_)
  simp only [Function.comp_apply]
  rw [show ((empProb alpha k : ProbabilityMeasure (AddCircle (1:ℝ))) :
      Measure (AddCircle (1:ℝ))) = empMeasure alpha (k+1) from rfl, integral_empMeasure]
  simp [smul_eq_mul]

/-! ### Arcs -/

/-- Two reals define the same point of `ℝ / ℤ` exactly when they differ by an integer. -/
lemma coe_eq_coe_iff (x y : ℝ) :
    ((x : AddCircle (1:ℝ)) = (y : AddCircle (1:ℝ))) ↔ ∃ k : ℤ, x - y = k := by
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, by simpa [eq_comm] using hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by simp [hk]⟩

lemma mem_arc_iff {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (x : ℝ) :
    ((x : AddCircle (1:ℝ)) ∈ arc a b) ↔ Int.fract x ∈ Set.Ico a b := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hfr : Int.fract y = Int.fract x := by
      rw [Int.fract_eq_fract]
      exact (coe_eq_coe_iff y x).mp hxy
    have hy01 : Int.fract y = y := Int.fract_eq_self.mpr ⟨le_trans ha hy.1, lt_of_lt_of_le hy.2 hb⟩
    rw [← hfr, hy01]
    exact hy
  · intro h
    refine ⟨Int.fract x, h, ?_⟩
    rw [coe_eq_coe_iff]
    exact ⟨-⌊x⌋, by rw [Int.fract]; push_cast; ring⟩

lemma isOpen_image_Ioo (a b : ℝ) :
    IsOpen ((fun x : ℝ => (x : AddCircle (1:ℝ))) '' Set.Ioo a b) :=
  QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo

lemma isClosed_image_Icc (a b : ℝ) :
    IsClosed ((fun x : ℝ => (x : AddCircle (1:ℝ))) '' Set.Icc a b) :=
  (isCompact_Icc.image (by fun_prop)).isClosed

lemma measurableSet_arc (a b : ℝ) : MeasurableSet (arc a b) := by
  rcases le_or_gt b a with h | h
  · simp [arc, Set.Ico_eq_empty (not_lt.mpr h)]
  · have harc : arc a b = insert ((a : ℝ) : AddCircle (1:ℝ))
        ((fun x : ℝ => (x : AddCircle (1:ℝ))) '' Set.Ioo a b) := by
      rw [arc, ← Set.Ioo_insert_left h, Set.image_insert_eq]
    rw [harc]
    exact ((isOpen_image_Ioo a b).measurableSet).insert _

lemma frontier_arc_subset (a b : ℝ) :
    frontier (arc a b) ⊆ {((a : ℝ) : AddCircle (1:ℝ)), ((b : ℝ) : AddCircle (1:ℝ))} := by
  intro z hz
  have h1 : z ∈ closure (arc a b) := hz.1
  have h2 : z ∉ interior (arc a b) := hz.2
  have hcl : closure (arc a b) ⊆ (fun x : ℝ => (x : AddCircle (1:ℝ))) '' Set.Icc a b :=
    closure_minimal (Set.image_mono Set.Ico_subset_Icc_self) (isClosed_image_Icc a b)
  have hint : (fun x : ℝ => (x : AddCircle (1:ℝ))) '' Set.Ioo a b ⊆ interior (arc a b) :=
    interior_maximal (Set.image_mono Set.Ioo_subset_Ico_self) (isOpen_image_Ioo a b)
  obtain ⟨t, ht, rfl⟩ := hcl h1
  rcases eq_or_lt_of_le ht.1 with rfl | hta
  · exact Or.inl rfl
  rcases eq_or_lt_of_le ht.2 with rfl | htb
  · exact Or.inr rfl
  exact absurd (hint ⟨t, ⟨hta, htb⟩, rfl⟩) h2

lemma haar_frontier_arc (a b : ℝ) :
    (haarAddCircle : Measure (AddCircle (1:ℝ))) (frontier (arc a b)) = 0 := by
  refine measure_mono_null (frontier_arc_subset a b) ?_
  rw [Set.insert_eq]
  exact measure_union_null (haar_singleton _) (haar_singleton _)

lemma preimage_arc_inter {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    (QuotientAddGroup.mk ⁻¹' (arc a b)) ∩ Set.Ioc a (a + 1) = Set.Ioo a b ∪ {a + 1} := by
  have hb1 : b ≤ a + 1 := by linarith
  ext x
  constructor
  · rintro ⟨hx1, hx2⟩
    obtain ⟨y, hy, hxy⟩ := hx1
    obtain ⟨k, hk⟩ := (coe_eq_coe_iff y x).mp hxy
    have h1 : (-1 : ℝ) ≤ (k:ℝ) := by linarith [hk, hy.1, hx2.2]
    have h2 : (k:ℝ) < 1 := by linarith [hk, hy.2, hx2.1]
    have hk0 : k = -1 ∨ k = 0 := by
      have h1' : (-1 : ℤ) ≤ k := by exact_mod_cast h1
      have h2' : k < 1 := by exact_mod_cast h2
      omega
    rcases hk0 with rfl | rfl
    · right
      simp only [Set.mem_singleton_iff]
      push_cast at hk
      linarith [hy.1, hx2.2]
    · left
      have hyx : y = x := by push_cast at hk; linarith
      subst hyx
      exact ⟨hx2.1, hy.2⟩
  · rintro (hx | hx)
    · exact ⟨⟨x, ⟨le_of_lt hx.1, hx.2⟩, rfl⟩, hx.1, le_trans (le_of_lt hx.2) hb1⟩
    · simp only [Set.mem_singleton_iff] at hx
      subst hx
      refine ⟨⟨a, ⟨le_refl a, hab⟩, ?_⟩, by linarith, le_refl _⟩
      rw [coe_eq_coe_iff]
      exact ⟨-1, by push_cast; ring⟩

lemma haar_arc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    (haarAddCircle : Measure (AddCircle (1:ℝ))) (arc a b) = ENNReal.ofReal (b - a) := by
  rw [haar_eq_volume]
  rcases eq_or_lt_of_le hab with rfl | h
  · simp [arc]
  rw [AddCircle.add_projection_respects_measure (T := (1:ℝ)) a (measurableSet_arc a b),
    preimage_arc_inter ha h hb]
  have hvol : (volume : Measure ℝ) (Set.Ioo a b ∪ {a + 1}) = volume (Set.Ioo a b) := by
    refine le_antisymm ?_ (measure_mono Set.subset_union_left)
    calc volume (Set.Ioo a b ∪ {a+1}) ≤ volume (Set.Ioo a b) + volume ({a+1} : Set ℝ) :=
          measure_union_le _ _
      _ = volume (Set.Ioo a b) := by simp
  rw [hvol, Real.volume_Ioo]

lemma empMeasure_arc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (alpha : ℝ) (N : ℕ) :
    empMeasure alpha N (arc a b) = (N : ℝ≥0∞)⁻¹ * (configCount alpha a b N : ℝ≥0∞) := by
  rw [empMeasure, Measure.smul_apply, Measure.finset_sum_apply, smul_eq_mul]
  congr 1
  rw [configCount, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.dirac_apply' _ (measurableSet_arc a b)]
  simp only [orbitPoint]
  by_cases h : Int.fract ((i:ℝ) * alpha) ∈ Set.Ico a b
  · rw [if_pos h, Set.indicator_of_mem ((mem_arc_iff ha hb _).mpr h)]
    simp
  · rw [if_neg h, Set.indicator_of_notMem (fun hc => h ((mem_arc_iff ha hb _).mp hc))]

/-! ### Main theorem -/

/-- **Weyl equidistribution / density of configuration counts.**
For irrational `α` and `0 ≤ a ≤ b ≤ 1`, the proportion of `n < N` with `{n α} ∈ [a, b)`
converges to `b - a`.

The statement is unconditional: no equidistribution assumption is taken as a hypothesis.
The equidistribution input is supplied by `tendsto_avg_continuous` (Weyl's criterion together
with density of trigonometric polynomials) and `tendsto_empProb` (weak convergence of the
empirical measures), and the passage from continuous test functions to the indicator of an
interval — the basic bounded-variation test function — is the portmanteau theorem applied to
the arc `arc a b`, whose boundary is Haar-null. -/
theorem configCount_density_of_BV {alpha a b : ℝ} (hirr : Irrational alpha)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (configCount alpha a b N : ℝ) / N) atTop (𝓝 (b - a)) := by
  have hfront : ((haarProb : ProbabilityMeasure (AddCircle (1:ℝ))) : Measure (AddCircle (1:ℝ)))
      (frontier (arc a b)) = 0 := haar_frontier_arc a b
  have hw := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      (tendsto_empProb hirr) hfront
  rw [show ((haarProb : ProbabilityMeasure (AddCircle (1:ℝ))) : Measure (AddCircle (1:ℝ)))
      = haarAddCircle from rfl, haar_arc ha hab hb] at hw
  have hw2 := (ENNReal.tendsto_toReal (by simp)).comp hw
  rw [ENNReal.toReal_ofReal (by linarith)] at hw2
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine hw2.congr (fun k => ?_)
  simp only [Function.comp_apply]
  rw [show ((empProb alpha k : ProbabilityMeasure (AddCircle (1:ℝ))) :
      Measure (AddCircle (1:ℝ))) = empMeasure alpha (k+1) from rfl, empMeasure_arc ha hb]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    div_eq_inv_mul]

end EquidistributionBVReduction
end Brockian

