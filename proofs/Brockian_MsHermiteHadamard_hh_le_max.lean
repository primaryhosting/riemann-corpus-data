import Mathlib
namespace Brockian.MsHermiteHadamard

open MeasureTheory Set

/-- A convex function on `[a,b]` is bounded above by the max of its values at the endpoints. -/
lemma hh_le_max {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ConvexOn ℝ (Set.Icc a b) f)
    {x : ℝ} (hx : x ∈ Set.Icc a b) : f x ≤ max (f a) (f b) := by
  have ha_mem : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab
  have hb_mem : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr hab
  by_cases h : x = a ∨ x = b
  · rcases h with rfl | rfl <;> simp
  · -- x is strictly between a and b
    have hne : x ≠ a := by tauto
    have hne' : x ≠ b := by tauto
    have hxltb : x < b := lt_of_le_of_ne hx.2 hne'
    have haxb : a < x := lt_of_le_of_ne hx.1 (Ne.symm hne)
    -- Write x = s*a + t*b where s = (b-x)/(b-a) and t = (x-a)/(b-a)
    have hba : b - a > 0 := by linarith
    have hbx : b - x > 0 := by linarith
    have hxa : x - a > 0 := by linarith
    set s := (b - x) / (b - a) with hs_def
    set t := (x - a) / (b - a) with ht_def
    have hs_pos : 0 < s := div_pos hbx hba
    have ht_pos : 0 < t := div_pos hxa hba
    have hs_le_one : s ≤ 1 := by rw [div_le_one hba]; linarith [hx.1]
    have ht_le_one : t ≤ 1 := by rw [div_le_one hba]; linarith [hx.2]
    have hst : s + t = 1 := by rw [hs_def, ht_def]; field_simp; ring
    have hx_eq : x = s * a + t * b := by rw [hs_def, ht_def]; field_simp; ring
    have hx_eq' : s • a + t • b = x := by simp [hx_eq, smul_eq_mul]
    have hconv := hf.2 ha_mem hb_mem (le_of_lt hs_pos) (le_of_lt ht_pos) hst
    rw [hx_eq'] at hconv
    -- Now hconv : f(s*a + t*b) ≤ s*f(a) + t*f(b)
    have hle_max : s • f a + t • f b ≤ max (f a) (f b) := by
      have h1 : s • f a + t • f b ≤ s • max (f a) (f b) + t • max (f a) (f b) := by
        apply add_le_add
        · exact smul_le_smul_of_nonneg_left (le_max_left _ _) (le_of_lt hs_pos)
        · exact smul_le_smul_of_nonneg_left (le_max_right _ _) (le_of_lt ht_pos)
      calc s • f a + t • f b ≤ s • max (f a) (f b) + t • max (f a) (f b) := h1
        _ = (s + t) • max (f a) (f b) := by rw [add_smul]
        _ = max (f a) (f b) := by rw [hst]; simp
    linarith

/-- Midpoint convexity: reflecting `x` about the midpoint of `[a,b]`. -/
lemma hh_midpoint {f : ℝ → ℝ} {a b : ℝ} (hf : ConvexOn ℝ (Set.Icc a b) f)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    2 * f ((a + b) / 2) ≤ f x + f (a + b - x) := by
  -- First show that a + b - x is also in [a, b]
  have hx'_mem : a + b - x ∈ Set.Icc a b := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  -- Use convexity with equal weights 1/2 and 1/2
  have hconv := hf.2 hx hx'_mem (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  -- hconv : f(1/2 * x + 1/2 * (a+b-x)) ≤ 1/2 * f(x) + 1/2 * f(a+b-x)
  simp only [smul_eq_mul] at hconv
  calc 2 * f ((a + b) / 2) = 2 * f ((x + (a + b - x)) / 2) := by ring_nf
    _ = 2 * f (1/2 * x + 1/2 * (a + b - x)) := by ring_nf
    _ ≤ 2 * ((1/2) * f x + (1/2) * f (a + b - x)) := by nlinarith
    _ = f x + f (a + b - x) := by ring

/-- A convex function on `[a,b]` is bounded below on `[a,b]`. -/
lemma hh_ge_min {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ConvexOn ℝ (Set.Icc a b) f)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    2 * f ((a + b) / 2) - max (f a) (f b) ≤ f x := by
  have h1 := hh_midpoint hf hx
  have hx' : a + b - x ∈ Set.Icc a b := ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have h2 := hh_le_max hab hf hx'
  linarith

/-- A convex function on `[a,b]` is interval integrable there. -/
lemma hh_integrable {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ConvexOn ℝ (Set.Icc a b) f) :
    IntervalIntegrable f volume a b := by
  have hcont : ContinuousOn f (Set.Ioo a b) := by
    have := hf.continuousOn_interior
    rwa [interior_Icc] at this
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioo a b)) := by
    constructor
    simp [Real.volume_Ioo]
  refine ⟨hcont.aestronglyMeasurable measurableSet_Ioo, ?_⟩
  refine HasFiniteIntegral.of_bounded
    (C := |max (f a) (f b)| + |2 * f ((a + b) / 2) - max (f a) (f b)|) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have h1 := hh_le_max hab.le hf (Ioo_subset_Icc_self hx)
  have h2 := hh_ge_min hab.le hf (Ioo_subset_Icc_self hx)
  have e1 := le_abs_self (max (f a) (f b))
  have e2 := neg_abs_le (2 * f ((a + b) / 2) - max (f a) (f b))
  have e3 := abs_nonneg (max (f a) (f b))
  have e4 := abs_nonneg (2 * f ((a + b) / 2) - max (f a) (f b))
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/-- A convex function lies below the chord joining `(a, f a)` and `(b, f b)`. -/
lemma hh_le_chord {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ConvexOn ℝ (Set.Icc a b) f)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    f x ≤ f a + (x - a) / (b - a) * (f b - f a) := by
  have ha : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr (le_of_lt hab)
  have hb : b ∈ Set.Icc a b := Set.right_mem_Icc.mpr (le_of_lt hab)
  set t : ℝ := (x - a) / (b - a) with ht_def
  have ht_nonneg : 0 ≤ t := div_nonneg (by linarith [hx.1]) (by linarith)
  have ht_le_one : t ≤ 1 := by rw [div_le_one (by linarith : 0 < b - a)]; linarith [hx.2]
  have hba_pos : 0 < b - a := by linarith
  have hx_eq : x = (1 - t) * a + t * b := by
    rw [ht_def]
    field_simp
    ring
  have hconv := hf.2 ha hb (by linarith : 0 ≤ 1 - t) (by linarith : 0 ≤ t) (by ring)
  calc f x = f ((1 - t) * a + t * b) := by rw [hx_eq]
    _ ≤ (1 - t) * f a + t * f b := hconv
    _ = f a + t * (f b - f a) := by ring
    _ = f a + (x - a) / (b - a) * (f b - f a) := by rw [ht_def]

/-- The right-hand Hermite–Hadamard inequality, in unnormalized form. -/
lemma hh_right {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ConvexOn ℝ (Set.Icc a b) f) :
    (∫ x in a..b, f x) ≤ (b - a) * ((f a + f b) / 2) := by
  have hint := hh_integrable hab hf
  have hba : b - a ≠ 0 := by linarith
  set C : ℝ := f a - a * (f b - f a) / (b - a) with hC
  set D : ℝ := (f b - f a) / (b - a) with hD
  have hfun : (fun x : ℝ => f a + (x - a) / (b - a) * (f b - f a)) = fun x : ℝ => C + x * D := by
    funext x
    rw [hC, hD]
    field_simp
    ring
  have hg : IntervalIntegrable (fun x : ℝ => f a + (x - a) / (b - a) * (f b - f a)) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono := intervalIntegral.integral_mono_on hab.le hint hg (fun x hx => hh_le_chord hab hf hx)
  have hcalc : (∫ x in a..b, (f a + (x - a) / (b - a) * (f b - f a)))
      = (b - a) * ((f a + f b) / 2) := by
    rw [hfun, intervalIntegral.integral_add _root_.intervalIntegrable_const
      (intervalIntegral.intervalIntegrable_id.mul_const D)]
    simp [intervalIntegral.integral_mul_const, integral_id, hC, hD]
    field_simp
    ring
  linarith [hcalc ▸ hmono]

/-- The left-hand Hermite–Hadamard inequality, in unnormalized form. -/
lemma hh_left {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hf : ConvexOn ℝ (Set.Icc a b) f) :
    (b - a) * f ((a + b) / 2) ≤ ∫ x in a..b, f x := by
  have hint := hh_integrable hab hf
  have hrefl : (∫ x in a..b, f (a + b - x)) = ∫ x in a..b, f x := by
    simp
  have hint2 : IntervalIntegrable (fun x => f (a + b - x)) volume a b := by
    have := (hint.comp_sub_left (a + b)).symm
    simpa using this
  have hmono : (∫ _x in a..b, 2 * f ((a + b) / 2)) ≤ ∫ x in a..b, (f x + f (a + b - x)) := by
    apply intervalIntegral.integral_mono_on hab.le (by simp) (hint.add hint2)
    intro x hx
    exact hh_midpoint hf hx
  rw [intervalIntegral.integral_add hint hint2, hrefl] at hmono
  simp at hmono
  linarith

/-- The Hermite–Hadamard inequality: for a convex f on [a,b] with a < b,
    f((a+b)/2) ≤ (1/(b−a)) ∫_a^b f ≤ (f a + f b)/2. -/
theorem hermite_hadamard (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) :
    f ((a + b) / 2) ≤ (1 / (b - a)) * ∫ x in a..b, f x ∧
    (1 / (b - a)) * ∫ x in a..b, f x ≤ (f a + f b) / 2 := by
  have hba : (0:ℝ) < b - a := by linarith
  constructor
  · rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hba, mul_comm]
    exact hh_left hab hf
  · rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hba, mul_comm]
    exact hh_right hab hf

end Brockian.MsHermiteHadamard

