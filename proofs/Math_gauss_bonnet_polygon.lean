/-
Volume of a wedge of the unit ball of `EuclideanSpace ℝ (Fin 3)` in standard position.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Sector

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- The wedge of the unit ball cut out by the half-spaces with inner normals
`(1,0,0)` and `(cos t, sin t, 0)`. -/
def wedgeStd (t : ℝ) : Set E3 :=
  {x : E3 | ‖x‖ ≤ 1 ∧ 0 < x 0 ∧ 0 < x 0 * Real.cos t + x 1 * Real.sin t}

private def wedgePi (t : ℝ) : Set (Fin 3 → ℝ) :=
  {y | y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 ≤ 1 ∧ 0 < y 0 ∧ 0 < y 0 * Real.cos t + y 1 * Real.sin t}

private def wedgeProd (t : ℝ) : Set (ℝ × (Fin 2 → ℝ)) :=
  {p | p.2 0 ^ 2 + p.2 1 ^ 2 + p.1 ^ 2 ≤ 1 ∧ 0 < p.2 0 ∧
    0 < p.2 0 * Real.cos t + p.2 1 * Real.sin t}

private def wedgeProd2 (t : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {p | p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1 - p.1 ^ 2 ∧ 0 < p.2.1 ∧
    0 < p.2.1 * Real.cos t + p.2.2 * Real.sin t}

theorem measurableSet_wedgeStd (t : ℝ) : MeasurableSet (wedgeStd t) := by
  have : wedgeStd t = {x : E3 | ‖x‖ ≤ 1} ∩
      ({x : E3 | 0 < x 0} ∩ {x : E3 | 0 < x 0 * Real.cos t + x 1 * Real.sin t}) := rfl
  rw [this]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop)))

private theorem measurableSet_wedgeProd2 (t : ℝ) : MeasurableSet (wedgeProd2 t) := by
  have : wedgeProd2 t = {p : ℝ × (ℝ × ℝ) | p.2.1 ^ 2 + p.2.2 ^ 2 ≤ 1 - p.1 ^ 2} ∩
      ({p : ℝ × (ℝ × ℝ) | 0 < p.2.1} ∩
        {p : ℝ × (ℝ × ℝ) | 0 < p.2.1 * Real.cos t + p.2.2 * Real.sin t}) := rfl
  rw [this]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop)))

private theorem toLp_preimage_wedgeStd (t : ℝ) :
    (WithLp.toLp 2) ⁻¹' (wedgeStd t) = wedgePi t := by
  ext y
  have hnorm : ‖(WithLp.toLp 2 y : E3)‖ = Real.sqrt (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := by
    rw [EuclideanSpace.norm_eq]; congr 1; simp [Fin.sum_univ_three]
  simp only [Set.mem_preimage, wedgeStd, wedgePi, Set.mem_setOf_eq, hnorm]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, h3⟩
    nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2),
      Real.sqrt_nonneg (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, h3⟩
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt h1

private theorem prodMap_preimage_wedgeProd2 (t : ℝ) :
    (Prod.map id (MeasurableEquiv.finTwoArrow (α := ℝ))) ⁻¹' (wedgeProd2 t) = wedgeProd t := by
  ext p
  simp only [Set.mem_preimage, wedgeProd2, wedgeProd, Prod.map, Set.mem_setOf_eq,
    MeasurableEquiv.finTwoArrow_apply]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by simp at h1 ⊢; linarith, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by simp at h1 ⊢; linarith, h2, h3⟩

private theorem slice_wedgeProd2 (t z : ℝ) :
    (Prod.mk z ⁻¹' wedgeProd2 t) = planeSector t (Real.sqrt (1 - z ^ 2)) := by
  ext w
  simp only [Set.mem_preimage, wedgeProd2, planeSector, Set.mem_setOf_eq]
  by_cases hz : 1 - z ^ 2 < 0
  · constructor
    · rintro ⟨h1, h2, h3⟩; nlinarith
    · rintro ⟨h1, h2, h3⟩
      rw [Real.sqrt_eq_zero_of_nonpos hz.le] at h1
      exact absurd h1 (by nlinarith)
  · push_neg at hz
    rw [Real.sq_sqrt hz]

private theorem lintegral_slice (c : ℝ) (hc : 0 ≤ c) :
    ∫⁻ z : ℝ, ENNReal.ofReal (c * (Real.sqrt (1 - z ^ 2)) ^ 2) = ENNReal.ofReal (c * (4 / 3)) := by
  have h1 : ∀ z : ℝ, ENNReal.ofReal (c * (Real.sqrt (1 - z ^ 2)) ^ 2)
      = (Icc (-1 : ℝ) 1).indicator (fun z => ENNReal.ofReal (c * (1 - z ^ 2))) z := by
    intro z
    by_cases hz : z ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hz]
      congr 2
      rw [Real.sq_sqrt]
      simp only [mem_Icc] at hz
      nlinarith [hz.1, hz.2]
    · rw [Set.indicator_of_notMem hz]
      simp only [mem_Icc, not_and_or, not_le] at hz
      have hzero : Real.sqrt (1 - z ^ 2) = 0 := by
        apply Real.sqrt_eq_zero_of_nonpos
        rcases hz with h | h <;> nlinarith
      rw [hzero]
      simp
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Icc, ← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      intervalIntegral.integral_const_mul]
    norm_num [intervalIntegral.integral_sub, integral_pow, intervalIntegral.intervalIntegrable_pow]
  · exact (by fun_prop : Continuous fun z : ℝ => c * (1 - z ^ 2)).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
    simp only [mem_Icc] at hz
    have : (0 : ℝ) ≤ 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
    positivity

/-- **Volume of a wedge in standard position.**  For `0 ≤ t ≤ π`, the part of the unit ball of
`ℝ³` where both `x₀ > 0` and `x₀ cos t + x₁ sin t > 0` has volume `2 (π - t) / 3`.
Here `π - t` is the dihedral angle of the wedge. -/
theorem volume_wedgeStd (t : ℝ) (ht0 : 0 ≤ t) (htpi : t ≤ π) :
    volume (wedgeStd t) = ENNReal.ofReal (2 * (π - t) / 3) := by
  have step1 : volume (wedgeStd t) = volume (wedgePi t) := by
    rw [← toLp_preimage_wedgeStd t,
      (PiLp.volume_preserving_toLp (Fin 3)).measure_preimage (measurableSet_wedgeStd t).nullMeasurableSet]
  have step2 : volume (wedgePi t) = volume (wedgeProd t) := by
    have hpre : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2) ⁻¹' (wedgeProd t)
        = wedgePi t := rfl
    rw [← hpre, (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).measure_preimage]
    have : wedgeProd t = (Prod.map id (MeasurableEquiv.finTwoArrow (α := ℝ))) ⁻¹' (wedgeProd2 t) :=
      (prodMap_preimage_wedgeProd2 t).symm
    rw [this]
    exact (((measurableSet_wedgeProd2 t).preimage (by fun_prop))).nullMeasurableSet
  have step3 : volume (wedgeProd t) = volume (wedgeProd2 t) := by
    have hmp : MeasurePreserving (Prod.map id (MeasurableEquiv.finTwoArrow (α := ℝ)))
        (volume : Measure (ℝ × (Fin 2 → ℝ))) (volume : Measure (ℝ × (ℝ × ℝ))) := by
      rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
      exact (MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ)
    rw [← prodMap_preimage_wedgeProd2 t]
    exact hmp.measure_preimage (measurableSet_wedgeProd2 t).nullMeasurableSet
  have step4 : volume (wedgeProd2 t)
      = ∫⁻ z : ℝ, volume (planeSector t (Real.sqrt (1 - z ^ 2))) := by
    rw [Measure.volume_eq_prod, Measure.prod_apply (measurableSet_wedgeProd2 t)]
    exact lintegral_congr fun z => by rw [slice_wedgeProd2 t z]
  rw [step1, step2, step3, step4]
  have hcoef : (0 : ℝ) ≤ (π - t) / 2 := by linarith
  have : ∀ z : ℝ, volume (planeSector t (Real.sqrt (1 - z ^ 2)))
      = ENNReal.ofReal ((π - t) / 2 * (Real.sqrt (1 - z ^ 2)) ^ 2) := fun z =>
    volume_planeSector t ht0 htpi _ (Real.sqrt_nonneg _)
  simp_rw [this]
  rw [lintegral_slice ((π - t) / 2) hcoef]
  congr 1
  ring

end Math

/-
Area of a circular sector of the plane, computed via polar coordinates.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import Mathlib

open MeasureTheory Metric Set Real
open scoped ENNReal

namespace Math

/-- The set of points of the disc of radius `R` lying in the intersection of the two half-planes
`{w | 0 < w.1}` and `{w | 0 < ⟪w, (cos t, sin t)⟫}`.  For `0 ≤ t ≤ π` this is a circular
sector of angle `π - t`. -/
def planeSector (t R : ℝ) : Set (ℝ × ℝ) :=
  {w : ℝ × ℝ | w.1 ^ 2 + w.2 ^ 2 ≤ R ^ 2 ∧ 0 < w.1 ∧ 0 < w.1 * Real.cos t + w.2 * Real.sin t}

theorem measurableSet_planeSector (t R : ℝ) : MeasurableSet (planeSector t R) := by
  have : planeSector t R = {w : ℝ × ℝ | w.1 ^ 2 + w.2 ^ 2 ≤ R ^ 2} ∩
      ({w : ℝ × ℝ | 0 < w.1} ∩ {w : ℝ × ℝ | 0 < w.1 * Real.cos t + w.2 * Real.sin t}) := rfl
  rw [this]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop)))

/-- In polar coordinates, the sector is the product of a radius interval and an angle interval. -/
theorem polar_preimage_planeSector (t : ℝ) (ht0 : 0 ≤ t) (htpi : t ≤ π) (R : ℝ) (hR : 0 ≤ R) :
    (polarCoord.symm ⁻¹' planeSector t R) ∩ polarCoord.target
      = (Ioc (0 : ℝ) R) ×ˢ (Ioo (t - π / 2) (π / 2)) := by
  have hpi := Real.pi_pos
  have htarget : polarCoord.target = (Ioi (0 : ℝ)) ×ˢ (Ioo (-π) π) := rfl
  ext ⟨r, th⟩
  simp only [planeSector, Set.mem_inter_iff, Set.mem_preimage, polarCoord_symm_apply, htarget,
    Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioc, Set.mem_Ioo, Set.mem_Ioi]
  constructor
  · rintro ⟨⟨hnorm, hc1, hc2⟩, hr, hth1, hth2⟩
    have hrpos : 0 < r := hr
    have hcos : 0 < Real.cos th := by nlinarith
    have hc2' : 0 < r * Real.cos (th - t) := by rw [Real.cos_sub]; nlinarith
    have hcos2 : 0 < Real.cos (th - t) := by nlinarith
    have hpyth := Real.sin_sq_add_cos_sq th
    have hupper : th < π / 2 := by
      by_contra hcon
      push_neg at hcon
      have := Real.cos_nonpos_of_pi_div_two_le_of_le hcon (by linarith)
      linarith
    have hlower : -(π / 2) < th := by
      by_contra hcon
      push_neg at hcon
      have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := -th) (by linarith) (by linarith)
      rw [Real.cos_neg] at this
      linarith
    have hr2 : r ^ 2 ≤ R ^ 2 := by nlinarith
    refine ⟨⟨hrpos, by nlinarith⟩, ?_, hupper⟩
    by_contra hcon
    push_neg at hcon
    have := Real.cos_nonpos_of_pi_div_two_le_of_le (x := t - th) (by linarith) (by linarith)
    rw [show t - th = -(th - t) by ring, Real.cos_neg] at this
    linarith
  · rintro ⟨⟨hrpos, hrR⟩, hth1, hth2⟩
    have hcos : 0 < Real.cos th := Real.cos_pos_of_mem_Ioo ⟨by linarith, hth2⟩
    have hcos2 : 0 < Real.cos (th - t) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have hpyth := Real.sin_sq_add_cos_sq th
    have hexp : r * Real.cos (th - t)
        = r * Real.cos th * Real.cos t + r * Real.sin th * Real.sin t := by
      rw [Real.cos_sub]; ring
    have hsq : (r * Real.cos th) ^ 2 + (r * Real.sin th) ^ 2 = r ^ 2 := by nlinarith [hpyth]
    exact ⟨⟨by nlinarith, by positivity, by nlinarith⟩, hrpos, by linarith, by linarith⟩

private theorem lintegral_ofReal_Ioc (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ r in Ioc (0 : ℝ) R, ENNReal.ofReal r = ENNReal.ofReal (R ^ 2 / 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [← intervalIntegral.integral_of_le hR]
    simp [integral_id]
  · exact continuous_id.integrableOn_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using hx.1.le

/-- **Area of a circular sector**: for `0 ≤ t ≤ π`, the sector of the disc of radius `R`
cut out by the two half-planes has area `(π - t)/2 * R ^ 2`. -/
theorem volume_planeSector (t : ℝ) (ht0 : 0 ≤ t) (htpi : t ≤ π) (R : ℝ) (hR : 0 ≤ R) :
    volume (planeSector t R) = ENNReal.ofReal ((π - t) / 2 * R ^ 2) := by
  classical
  have hSmeas : MeasurableSet (planeSector t R) := measurableSet_planeSector t R
  have hpre : MeasurableSet (polarCoord.symm ⁻¹' planeSector t R) :=
    hSmeas.preimage (by fun_prop)
  have h1 : volume (planeSector t R)
      = ∫⁻ p, (planeSector t R).indicator (fun _ => (1 : ℝ≥0∞)) p := by
    rw [lintegral_indicator hSmeas]; simp
  rw [h1, ← lintegral_comp_polarCoord_symm]
  have h2 : ∀ p : ℝ × ℝ,
      ENNReal.ofReal p.1 • (planeSector t R).indicator (fun _ => (1 : ℝ≥0∞))
          (polarCoord.symm p)
        = (polarCoord.symm ⁻¹' planeSector t R).indicator (fun q => ENNReal.ofReal q.1) p := by
    intro p
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases h : polarCoord.symm p ∈ planeSector t R
    · simp [Set.mem_preimage]
    · simp [Set.mem_preimage]
  simp_rw [h2]
  rw [lintegral_indicator hpre, Measure.restrict_restrict hpre,
    polar_preimage_planeSector t ht0 htpi R hR, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have key := lintegral_prod_mul (μ := volume.restrict (Ioc (0 : ℝ) R))
      (ν := volume.restrict (Ioo (t - π / 2) (π / 2))) (f := fun x => ENNReal.ofReal x)
      (g := fun _ => (1 : ℝ≥0∞)) (by fun_prop) (by fun_prop)
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo, one_mul] at key
  rw [key, lintegral_ofReal_Ioc R hR, ← ENNReal.ofReal_mul (by positivity)]
  ring_nf

end Math

/-
The cells cut out of the unit ball of `ℝ³` by three planes through the origin.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Lune

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- The open half-space with inner normal `n`. -/
def cone1 (n : E3) : Set E3 := {x : E3 | 0 < ⟪n, x⟫}

/-- Half of the open unit ball. -/
def cell1 (n : E3) : Set E3 := ball 0 1 ∩ cone1 n

/-- The intersection of the open unit ball with two open half-spaces (a solid lune). -/
def cell2 (n m : E3) : Set E3 := cell1 n ∩ cone1 m

/-- The intersection of the open unit ball with three open half-spaces (a solid triangle). -/
def cell3 (n m p : E3) : Set E3 := cell2 n m ∩ cone1 p

theorem measurableSet_cone1 (n : E3) : MeasurableSet (cone1 n) :=
  measurableSet_lt (by fun_prop) (by fun_prop)

theorem measurableSet_cell1 (n : E3) : MeasurableSet (cell1 n) :=
  measurableSet_ball.inter (measurableSet_cone1 n)

theorem measurableSet_cell2 (n m : E3) : MeasurableSet (cell2 n m) :=
  (measurableSet_cell1 n).inter (measurableSet_cone1 m)

theorem measurableSet_cell3 (n m p : E3) : MeasurableSet (cell3 n m p) :=
  (measurableSet_cell2 n m).inter (measurableSet_cone1 p)

/-- A plane through the origin is a null set. -/
theorem volume_plane_eq_zero (n : E3) (hn : n ≠ 0) : volume {x : E3 | ⟪n, x⟫ = 0} = 0 := by
  have h : {x : E3 | ⟪n, x⟫ = 0}
      = ((LinearMap.ker ((innerSL ℝ n : E3 →L[ℝ] ℝ) : E3 →ₗ[ℝ] ℝ) : Submodule ℝ E3) : Set E3) := by
    ext x; simp [LinearMap.mem_ker]
  rw [h]
  apply Measure.addHaar_submodule
  intro htop
  have hmem : n ∈ (LinearMap.ker ((innerSL ℝ n : E3 →L[ℝ] ℝ) : E3 →ₗ[ℝ] ℝ) : Submodule ℝ E3) :=
    htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker] at hmem
  simp only [ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_self_eq_zero] at hmem
  exact hn hmem

/-- Splitting a set by the sign of a linear functional does not change its volume. -/
theorem volume_split (S : Set E3) (hS : MeasurableSet S) (n : E3) (hn : n ≠ 0) :
    volume S = volume (S ∩ cone1 n) + volume (S ∩ cone1 (-n)) := by
  have hdecomp : S = ((S ∩ cone1 n) ∪ (S ∩ cone1 (-n))) ∪ (S ∩ {x : E3 | ⟪n, x⟫ = 0}) := by
    ext x
    simp only [cone1, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, inner_neg_left]
    constructor
    · intro hx
      rcases lt_trichotomy (0 : ℝ) ⟪n, x⟫ with h | h | h
      · exact Or.inl (Or.inl ⟨hx, h⟩)
      · exact Or.inr ⟨hx, h.symm⟩
      · exact Or.inl (Or.inr ⟨hx, by linarith⟩)
    · rintro ((⟨hx, _⟩ | ⟨hx, _⟩) | ⟨hx, _⟩) <;> exact hx
  have hnull : volume (S ∩ {x : E3 | ⟪n, x⟫ = 0}) = 0 :=
    measure_mono_null Set.inter_subset_right (volume_plane_eq_zero n hn)
  have hdisj : Disjoint (S ∩ cone1 n) (S ∩ cone1 (-n)) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx1⟩ ⟨-, hx2⟩
    simp only [cone1, Set.mem_setOf_eq, inner_neg_left] at hx1 hx2
    linarith
  conv_lhs => rw [hdecomp]
  rw [measure_union_null hnull,
    measure_union hdisj (hS.inter (measurableSet_cone1 (-n)))]

theorem volume_ball_one : volume (ball (0 : E3) 1) = ENNReal.ofReal (π * 4 / 3) := by
  rw [EuclideanSpace.volume_ball_fin_three]
  simp

theorem volume_cell3_lt_top (n m p : E3) : volume (cell3 n m p) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (le_trans (le_trans Set.inter_subset_left
    Set.inter_subset_left) Set.inter_subset_left : cell3 n m p ⊆ ball (0 : E3) 1))
  rw [volume_ball_one]
  exact ENNReal.ofReal_ne_top

theorem volume_cell2_ne_top (n m : E3) : volume (cell2 n m) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (le_trans Set.inter_subset_left
    Set.inter_subset_left : cell2 n m ⊆ ball (0 : E3) 1))
  rw [volume_ball_one]
  exact ENNReal.ofReal_ne_top

/-- The solid lune has the same volume as the corresponding closed wedge. -/
theorem volume_cell2_eq_wedgeGen (n m : E3) : volume (cell2 n m) = volume (wedgeGen n m) := by
  have hsub : cell2 n m ⊆ wedgeGen n m := by
    rintro x ⟨⟨hb, hn⟩, hm⟩
    exact ⟨le_of_lt (by simpa [mem_ball_zero_iff] using hb), hn, hm⟩
  have hsub2 : wedgeGen n m ⊆ cell2 n m ∪ sphere (0 : E3) 1 := by
    rintro x ⟨hb, hn, hm⟩
    rcases eq_or_lt_of_le hb with h | h
    · exact Or.inr (by simp [mem_sphere_zero_iff_norm, h])
    · exact Or.inl ⟨⟨by simpa [mem_ball_zero_iff] using h, hn⟩, hm⟩
  refine le_antisymm (measure_mono hsub) ?_
  calc volume (wedgeGen n m) ≤ volume (cell2 n m ∪ sphere (0 : E3) 1) := measure_mono hsub2
    _ ≤ volume (cell2 n m) + volume (sphere (0 : E3) 1) := measure_union_le _ _
    _ = volume (cell2 n m) := by rw [Measure.addHaar_sphere, add_zero]

/-- **Volume of a solid lune.** -/
theorem volume_cell2 (n m : E3) (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hlt : ⟪n, m⟫ ^ 2 < 1) :
    volume (cell2 n m) = ENNReal.ofReal (2 * (π - angle n m) / 3) := by
  rw [volume_cell2_eq_wedgeGen, volume_wedgeGen n m hn hm hlt]

/-- The cells for the opposite normals are the antipodal images, hence have the same volume. -/
theorem volume_cell3_neg (n m p : E3) :
    volume (cell3 (-n) (-m) (-p)) = volume (cell3 n m p) := by
  have hset : cell3 (-n) (-m) (-p) = Neg.neg ⁻¹' (cell3 n m p) := by
    ext x
    simp only [cell3, cell2, cell1, cone1, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage,
      inner_neg_left, inner_neg_right, mem_ball_zero_iff, norm_neg, neg_neg]
    tauto
  rw [hset, Measure.measure_preimage_neg]

end Math

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
Volume of a general wedge of the unit ball of `ℝ³`, obtained from the standard one by a rotation.

This is an auxiliary file for the Gauss-Bonnet (Girard) theorem for spherical triangles.
-/
import RequestProject.Wedge

open MeasureTheory Metric Set Real InnerProductGeometry
open scoped ENNReal RealInnerProductSpace

namespace Math

/-- The wedge of the closed unit ball cut out by the two half-spaces with inner unit normals
`n` and `m`. -/
def wedgeGen (n m : E3) : Set E3 := {x : E3 | ‖x‖ ≤ 1 ∧ 0 < ⟪n, x⟫ ∧ 0 < ⟪m, x⟫}

theorem measurableSet_wedgeGen (n m : E3) : MeasurableSet (wedgeGen n m) := by
  have : wedgeGen n m = {x : E3 | ‖x‖ ≤ 1} ∩
      ({x : E3 | 0 < ⟪n, x⟫} ∩ {x : E3 | 0 < ⟪m, x⟫}) := rfl
  rw [this]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    ((measurableSet_lt (by fun_prop) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (by fun_prop)))

/-- An orthonormal basis whose first two vectors are two prescribed orthonormal vectors. -/
theorem exists_orthonormalBasis_pair (n u : E3) (hn : ‖n‖ = 1) (hu : ‖u‖ = 1) (h : ⟪n, u⟫ = 0) :
    ∃ b : OrthonormalBasis (Fin 3) ℝ E3, b 0 = n ∧ b 1 = u := by
  have h' : ⟪u, n⟫ = 0 := by rw [real_inner_comm]; exact h
  set v : Fin 3 → E3 := ![n, u, 0] with hv
  have horth : Orthonormal ℝ (Set.restrict ({0, 1} : Set (Fin 3)) v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;>
      simp [Set.restrict, hv, hn, hu, h, h', Subtype.ext_iff]
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b, hb 0 (by simp), hb 1 (by simp)⟩

/-- **Volume of a wedge of the unit ball.**  If `n` and `m` are unit vectors that are not
parallel, the set of points of the unit ball lying in both open half-spaces
`⟪n, x⟫ > 0` and `⟪m, x⟫ > 0` has volume `2 (π - angle n m) / 3`. -/
theorem volume_wedgeGen (n m : E3) (hn : ‖n‖ = 1) (hm : ‖m‖ = 1) (hlt : ⟪n, m⟫ ^ 2 < 1) :
    volume (wedgeGen n m) = ENNReal.ofReal (2 * (π - angle n m) / 3) := by
  set c : ℝ := ⟪n, m⟫ with hc
  set s : ℝ := Real.sqrt (1 - c ^ 2) with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hmn : ⟪m, n⟫ = c := by rw [hc, real_inner_comm]
  have hnormsq : ‖m - c • n‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hn, hm, hmn, Real.norm_eq_abs,
      mul_one, sq_abs]
    ring
  have hnormeq : ‖m - c • n‖ = s := by
    rw [hs, show (1 : ℝ) - c ^ 2 = ‖m - c • n‖ ^ 2 from hnormsq.symm, Real.sqrt_sq (norm_nonneg _)]
  set u : E3 := s⁻¹ • (m - c • n) with hu
  have hnu : ‖u‖ = 1 := by
    rw [hu, norm_smul, hnormeq]
    simp [abs_of_pos hspos, inv_mul_cancel₀ hspos.ne']
  have hortho : ⟪n, u⟫ = 0 := by
    rw [hu, real_inner_smul_right, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hn, ← hc]
    simp
  obtain ⟨b, hb0, hb1⟩ := exists_orthonormalBasis_pair n u hn hnu hortho
  -- the angle `t`
  set t : ℝ := angle n m with ht
  have hcos : Real.cos t = c := by
    rw [ht, angle, hn, hm, ← hc]
    simp only [mul_one, div_one]
    exact Real.cos_arccos (by nlinarith) (by nlinarith)
  have hsin : Real.sin t = s := by
    rw [ht, angle, hn, hm, ← hc]
    simp only [mul_one, div_one]
    rw [Real.sin_arccos, hs]
  have ht0 : 0 ≤ t := by
    rw [ht, angle]; exact Real.arccos_nonneg _
  have htpi : t ≤ π := by
    rw [ht, angle]; exact Real.arccos_le_pi _
  -- `m` in terms of the basis
  have hmb : m = c • b 0 + s • b 1 := by
    rw [hb0, hb1, hu, smul_smul, mul_inv_cancel₀ hspos.ne', one_smul]
    abel
  have hset : wedgeGen n m = b.repr ⁻¹' (wedgeStd t) := by
    ext x
    have h0 : (b.repr x) 0 = ⟪n, x⟫ := by rw [b.repr_apply_apply, hb0]
    have h1 : (b.repr x) 1 = ⟪u, x⟫ := by rw [b.repr_apply_apply, hb1]
    have hmx : ⟪m, x⟫ = c * ⟪n, x⟫ + s * ⟪u, x⟫ := by
      rw [hmb, inner_add_left, real_inner_smul_left, real_inner_smul_left, hb0, hb1]
    simp only [wedgeGen, wedgeStd, Set.mem_setOf_eq, Set.mem_preimage, h0, h1, hcos, hsin,
      LinearIsometryEquiv.norm_map, hmx]
    constructor
    · rintro ⟨ha, hb', hc'⟩
      exact ⟨ha, hb', by linarith [hc']⟩
    · rintro ⟨ha, hb', hc'⟩
      exact ⟨ha, hb', by linarith [hc']⟩
  rw [hset, b.measurePreserving_repr.measure_preimage
    (measurableSet_wedgeStd t).nullMeasurableSet, volume_wedgeStd t ht0 htpi]

end Math

