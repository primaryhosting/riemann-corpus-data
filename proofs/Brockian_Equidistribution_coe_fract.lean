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
Weyl's criterion for equidistribution modulo one, and its application to the
sequence `n ↦ n • α` for irrational `α`.
-/
import Mathlib

open Filter MeasureTheory Metric Set Submodule
open scoped Topology Real

namespace Brockian.Equidistribution

noncomputable section

/-! ## Definitions -/

/-- A sequence `u : ℕ → ℝ` is *equidistributed modulo one* if for every subinterval
`[a, b) ⊆ [0, 1]` the proportion of the first `N` terms whose fractional part lies in `[a, b)`
tends to `b - a`. -/
def IsEquidistributedMod1 (u : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun k => Int.fract (u k) ∈ Ico a b).card : ℝ) / N)
      atTop (𝓝 (b - a))

/-- The `N`-th normalized Weyl (exponential) sum of frequency `h` of a sequence `u`. -/
def weylSum (u : ℕ → ℝ) (h : ℤ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, Complex.exp (2 * Real.pi * Complex.I * h * u k)

/-! ## Elementary facts about the circle `ℝ / ℤ` -/

lemma coe_fract (x : ℝ) : ((Int.fract x : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  rw [Int.fract]; simp

lemma fract_eq_fract_of_coe_eq {x y : ℝ} (h : (x : UnitAddCircle) = (y : UnitAddCircle)) :
    Int.fract x = Int.fract y := by
  have h2 : Int.fract x ∈ Ico (0 : ℝ) (0 + 1) :=
    mem_Ico.2 ⟨Int.fract_nonneg x, by simpa using Int.fract_lt_one x⟩
  have h3 : Int.fract y ∈ Ico (0 : ℝ) (0 + 1) :=
    mem_Ico.2 ⟨Int.fract_nonneg y, by simpa using Int.fract_lt_one y⟩
  rw [← AddCircle.coe_eq_coe_iff_of_mem_Ico h2 h3, coe_fract, coe_fract]
  exact h

lemma norm_coe_le_abs (t : ℝ) : ‖(t : UnitAddCircle)‖ ≤ |t| := by
  rw [UnitAddCircle.norm_eq]
  rcases lt_or_ge |t| (1 / 2) with h | h
  · have : round t = 0 := by
      rw [round_eq_zero_iff]
      cases abs_lt.1 h; constructor <;> linarith
    simp [this]
  · exact le_trans (abs_sub_round t) h

lemma exists_repr (c : ℝ) (z : UnitAddCircle) :
    ∃ x : ℝ, |x - c| ≤ 1 / 2 ∧ (x : UnitAddCircle) = z := by
  obtain ⟨y, rfl⟩ := Quotient.exists_rep z
  refine ⟨y - round (y - c), ?_, ?_⟩
  · have := abs_sub_round (y - c); convert this using 2; ring
  · rw [AddCircle.coe_sub]; simp

lemma dist_coe_coe (x c : ℝ) :
    dist ((x : UnitAddCircle)) ((c : UnitAddCircle)) = ‖((x - c : ℝ) : UnitAddCircle)‖ := by
  rw [dist_eq_norm, AddCircle.coe_sub]

/-- The half-open arc corresponding to `[a, b) ⊆ ℝ`. -/
def arc (a b : ℝ) : Set UnitAddCircle := (fun t : ℝ => (t : UnitAddCircle)) '' (Ico a b)

lemma mem_arc_iff {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (x : ℝ) :
    (x : UnitAddCircle) ∈ arc a b ↔ Int.fract x ∈ Ico a b := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hy1 : Int.fract y = y := Int.fract_eq_self.2 ⟨le_trans ha hy.1, lt_of_lt_of_le hy.2 hb⟩
    have h2 := fract_eq_fract_of_coe_eq hyx
    rw [hy1] at h2
    rwa [h2] at hy
  · intro hx
    exact ⟨Int.fract x, hx, coe_fract x⟩

lemma arc_subset_closedBall (a b : ℝ) :
    arc a b ⊆ closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [mem_closedBall, dist_coe_coe]
  refine le_trans (norm_coe_le_abs _) ?_
  rw [abs_le]
  constructor <;> [linarith [hy.1]; linarith [hy.2]]

lemma ball_subset_arc (a b : ℝ) :
    ball (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) ⊆ arc a b := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := exists_repr ((a + b) / 2) z
  rw [mem_ball, dist_coe_coe] at hz
  have heq : ‖((x - (a + b) / 2 : ℝ) : UnitAddCircle)‖ = |x - (a + b) / 2| := by
    rw [AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero]
    simpa using hx
  rw [heq, abs_lt] at hz
  exact ⟨x, mem_Ico.2 ⟨by linarith [hz.1], by linarith [hz.2]⟩, rfl⟩

/-! ## Averages of continuous functions -/

lemma integrable_of_continuous (f : C(UnitAddCircle, ℂ)) : Integrable f volume :=
  (map_continuous f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integrable_of_continuous_real (f : C(UnitAddCircle, ℝ)) : Integrable f volume :=
  (map_continuous f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma integral_fourier (n : ℤ) :
    ∫ z : UnitAddCircle, fourier n z = if n = 0 then 1 else 0 := by
  rw [← AddCircle.intervalIntegral_preimage 1 0]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, if_false]
    have hc : (2 * (Real.pi : ℂ) * Complex.I * n) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have hfe : ∀ x : ℝ, (fourier n ((x : ℝ) : UnitAddCircle))
        = Complex.exp ((2 * (Real.pi : ℂ) * Complex.I * n) * x) := by
      intro x; rw [fourier_coe_apply]; push_cast; ring_nf
    simp_rw [hfe]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * n * ((0 : ℝ) + 1 : ℝ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨n, by push_cast; ring⟩
    rw [h1]
    simp

variable (u : ℕ → ℝ)

/-- The Cesàro average of `f` along the sequence `u` viewed on the circle. -/
def avg (f : UnitAddCircle → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, f ((u k : ℝ) : UnitAddCircle)

/-- The real-valued Cesàro average. -/
def avgReal (f : UnitAddCircle → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, f ((u k : ℝ) : UnitAddCircle)

lemma avg_fourier (hweyl : ∀ h : ℤ, h ≠ 0 → Tendsto (weylSum u h) atTop (𝓝 0)) (n : ℤ) :
    Tendsto (avg u (fourier n)) atTop (𝓝 (∫ z : UnitAddCircle, fourier n z)) := by
  rw [integral_fourier]
  by_cases hn : n = 0
  · subst hn
    rw [if_pos rfl]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    simp only [avg, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ hN']
  · simp only [hn, if_false]
    have hrw : avg u (fourier n) = weylSum u n := by
      funext N
      simp only [avg, weylSum, fourier_coe_apply]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring_nf
    rw [hrw]
    exact hweyl n hn

lemma avg_span (hweyl : ∀ h : ℤ, h ≠ 0 → Tendsto (weylSum u h) atTop (𝓝 0))
    (f : C(UnitAddCircle, ℂ)) (hf : f ∈ span ℂ (range (fourier (T := 1)))) :
    Tendsto (avg u f) atTop (𝓝 (∫ z : UnitAddCircle, f z)) := by
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨n, rfl⟩ := hx; exact avg_fourier u hweyl n
  | zero =>
      have h1 : avg u ⇑(0 : C(UnitAddCircle, ℂ)) = fun _ => (0 : ℂ) := by
        funext N; simp [avg]
      rw [h1]; simp
  | add x y hx hy ihx ihy =>
      have hint : ∫ z : UnitAddCircle, (x + y) z = (∫ z, x z) + ∫ z, y z := by
        simpa using integral_add (integrable_of_continuous x) (integrable_of_continuous y)
      have h1 : avg u ⇑(x + y) = fun N => avg u ⇑x N + avg u ⇑y N := by
        funext N
        simp only [avg, ContinuousMap.coe_add, Pi.add_apply, Finset.sum_add_distrib, mul_add]
      rw [hint, h1]
      exact ihx.add ihy
  | smul c x hx ihx =>
      have hint : ∫ z : UnitAddCircle, (c • x) z = c * ∫ z, x z := by
        simp only [ContinuousMap.smul_apply, smul_eq_mul]
        exact MeasureTheory.integral_const_mul c _
      have h1 : avg u ⇑(c • x) = fun N => c * avg u ⇑x N := by
        funext N
        simp only [avg, ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        ring
      rw [hint, h1]
      exact ihx.const_mul c

lemma avg_continuous (hweyl : ∀ h : ℤ, h ≠ 0 → Tendsto (weylSum u h) atTop (𝓝 0))
    (f : C(UnitAddCircle, ℂ)) :
    Tendsto (avg u f) atTop (𝓝 (∫ z : UnitAddCircle, f z)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η := ε / 4 with hη
  have hηpos : 0 < η := by positivity
  have hmem : f ∈ closure ((span ℂ (range (fourier (T := 1)))) : Set C(UnitAddCircle, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.1 hmem η hηpos
  have hbound : ∀ z : UnitAddCircle, ‖f z - g z‖ ≤ η := by
    intro z
    have h1 : ‖(f - g) z‖ ≤ ‖f - g‖ := ContinuousMap.norm_coe_le_norm (f - g) z
    have h2 : ‖f - g‖ < η := by rwa [dist_eq_norm] at hfg
    simpa [ContinuousMap.sub_apply] using h1.trans h2.le
  have havg : ∀ N : ℕ, 0 < N → dist (avg u f N) (avg u g N) ≤ η := by
    intro N hN
    have hsum : ‖∑ k ∈ Finset.range N,
        (f ((u k : ℝ) : UnitAddCircle) - g ((u k : ℝ) : UnitAddCircle))‖ ≤ N * η := by
      refine le_trans (norm_sum_le _ _) ?_
      calc ∑ k ∈ Finset.range N, ‖f ((u k : ℝ) : UnitAddCircle) - g ((u k : ℝ) : UnitAddCircle)‖
          ≤ ∑ _k ∈ Finset.range N, η := Finset.sum_le_sum fun k _ => hbound _
        _ = N * η := by simp
    have hrw : avg u f N - avg u g N = (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N,
        (f ((u k : ℝ) : UnitAddCircle) - g ((u k : ℝ) : UnitAddCircle)) := by
      simp only [avg, Finset.sum_sub_distrib, mul_sub]
    rw [dist_eq_norm, hrw, norm_mul, norm_inv, Complex.norm_natCast]
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    calc (N : ℝ)⁻¹ * ‖∑ k ∈ Finset.range N,
            (f ((u k : ℝ) : UnitAddCircle) - g ((u k : ℝ) : UnitAddCircle))‖
        ≤ (N : ℝ)⁻¹ * (N * η) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = η := by field_simp
  have hint : dist (∫ z : UnitAddCircle, f z) (∫ z : UnitAddCircle, g z) ≤ η := by
    rw [dist_eq_norm, ← integral_sub (integrable_of_continuous f) (integrable_of_continuous g)]
    have := norm_integral_le_of_norm_le_const (μ := (volume : Measure UnitAddCircle))
      (f := fun z => f z - g z) (C := η) (Filter.Eventually.of_forall hbound)
    simpa [measureReal_def, UnitAddCircle.measure_univ] using this
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (avg_span u hweyl g hg) η hηpos
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have h1 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have h2 : 0 < N := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ _) hN)
  calc dist (avg u f N) (∫ z : UnitAddCircle, f z)
      ≤ dist (avg u f N) (avg u g N) + dist (avg u g N) (∫ z : UnitAddCircle, g z)
        + dist (∫ z : UnitAddCircle, g z) (∫ z : UnitAddCircle, f z) := dist_triangle4 _ _ _ _
    _ ≤ η + η + η := by
        gcongr
        · exact havg N h2
        · exact (hN₀ N h1).le
        · rw [dist_comm]; exact hint
    _ < ε := by rw [hη]; linarith

lemma avgReal_continuous (hweyl : ∀ h : ℤ, h ≠ 0 → Tendsto (weylSum u h) atTop (𝓝 0))
    (f : C(UnitAddCircle, ℝ)) :
    Tendsto (avgReal u f) atTop (𝓝 (∫ z : UnitAddCircle, f z)) := by
  set F : C(UnitAddCircle, ℂ) :=
    ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp (map_continuous f)⟩ with hF
  have h1 : avg u ⇑F = fun N => ((avgReal u f N : ℝ) : ℂ) := by
    funext N
    simp only [avg, avgReal, hF, ContinuousMap.coe_mk]
    push_cast
    ring
  have h2 : (∫ z : UnitAddCircle, F z) = ((∫ z : UnitAddCircle, f z : ℝ) : ℂ) := by
    simp only [hF, ContinuousMap.coe_mk]
    exact integral_ofReal
  have h3 := avg_continuous u hweyl F
  rw [h2, h1] at h3
  exact tendsto_ofReal_iff.1 h3

/-! ## Continuous approximations of arc indicators -/

/-- The continuous "ramp" on the circle which equals `1` on the closed ball of radius `s - δ`
around `p`, vanishes outside the ball of radius `s`, and interpolates linearly in between. -/
def rampAt (p : UnitAddCircle) (s δ : ℝ) : C(UnitAddCircle, ℝ) :=
  ⟨fun z => min 1 (max 0 ((s - dist z p) / δ)), by fun_prop⟩

lemma rampAt_nonneg (p : UnitAddCircle) (s δ : ℝ) (z : UnitAddCircle) : 0 ≤ rampAt p s δ z :=
  le_min zero_le_one (le_max_left _ _)

lemma rampAt_le_one (p : UnitAddCircle) (s δ : ℝ) (z : UnitAddCircle) : rampAt p s δ z ≤ 1 :=
  min_le_left _ _

lemma rampAt_eq_one {p : UnitAddCircle} {s δ : ℝ} (hδ : 0 < δ) {z : UnitAddCircle}
    (h : dist z p ≤ s - δ) : rampAt p s δ z = 1 := by
  have h1 : 1 ≤ (s - dist z p) / δ := by rw [le_div_iff₀ hδ]; linarith
  simp only [rampAt, ContinuousMap.coe_mk]
  rw [max_eq_right (by linarith), min_eq_left h1]

lemma rampAt_eq_zero {p : UnitAddCircle} {s δ : ℝ} (hδ : 0 < δ) {z : UnitAddCircle}
    (h : s ≤ dist z p) : rampAt p s δ z = 0 := by
  have h1 : (s - dist z p) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  simp only [rampAt, ContinuousMap.coe_mk]
  rw [max_eq_left h1, min_eq_right zero_le_one]

lemma integral_le_measureReal {A : Set UnitAddCircle} (hA : MeasurableSet A)
    (g : C(UnitAddCircle, ℝ)) (hg : ∀ z, g z ≤ A.indicator 1 z) :
    ∫ z : UnitAddCircle, g z ≤ volume.real A := by
  have hint : Integrable (A.indicator (1 : UnitAddCircle → ℝ)) volume :=
    (integrable_indicator_iff hA).2 (integrableOn_const (by simp [measure_ne_top]))
  have := integral_mono (integrable_of_continuous_real g) hint hg
  rwa [integral_indicator_one hA] at this

lemma measureReal_le_integral {A : Set UnitAddCircle} (hA : MeasurableSet A)
    (g : C(UnitAddCircle, ℝ)) (hg : ∀ z, A.indicator 1 z ≤ g z) :
    volume.real A ≤ ∫ z : UnitAddCircle, g z := by
  have hint : Integrable (A.indicator (1 : UnitAddCircle → ℝ)) volume :=
    (integrable_indicator_iff hA).2 (integrableOn_const (by simp [measure_ne_top]))
  have := integral_mono hint (integrable_of_continuous_real g) hg
  rwa [integral_indicator_one hA] at this

lemma measureReal_closedBall (p : UnitAddCircle) (ε : ℝ) :
    volume.real (closedBall p ε) = max (min 1 (2 * ε)) 0 := by
  rw [measureReal_def, AddCircle.volume_closedBall, ENNReal.toReal_ofReal']

/-! ## Weyl's criterion -/

/-- **Weyl's criterion**: if all nonzero-frequency Weyl sums of `u` vanish asymptotically,
then `u` is equidistributed modulo one. -/
theorem equidistribution_of_asymptotic (u : ℕ → ℝ)
    (hweyl : ∀ h : ℤ, h ≠ 0 → Tendsto (weylSum u h) atTop (𝓝 0)) :
    IsEquidistributedMod1 u := by
  intro a b ha hab hb
  -- the counting function is the Cesàro average of the indicator of the arc `[a, b)`
  have hcount : ∀ N : ℕ,
      avgReal u ((arc a b).indicator 1) N
        = (((Finset.range N).filter fun k => Int.fract (u k) ∈ Ico a b).card : ℝ) / N := by
    intro N
    rw [avgReal, div_eq_inv_mul, Finset.card_filter]
    congr 1
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : Int.fract (u k) ∈ Ico a b
    · rw [if_pos hk, Set.indicator_of_mem ((mem_arc_iff ha hb (u k)).2 hk)]
      rfl
    · rw [if_neg hk, Set.indicator_of_notMem (fun hmem => hk ((mem_arc_iff ha hb (u k)).1 hmem))]
  refine Tendsto.congr hcount ?_
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : (0 : ℝ) < ε / 8 := by positivity
  -- continuous upper and lower approximations of the indicator of the arc
  have hgp_ge : ∀ z, (arc a b).indicator 1 z ≤
      rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8) (ε / 8) z := by
    intro z
    by_cases hz : z ∈ arc a b
    · rw [Set.indicator_of_mem hz]
      have hd : dist z (((a + b) / 2 : ℝ) : UnitAddCircle) ≤ (b - a) / 2 :=
        arc_subset_closedBall a b hz
      rw [rampAt_eq_one hδ (by linarith)]
      simp
    · rw [Set.indicator_of_notMem hz]
      exact rampAt_nonneg _ _ _ _
  have hgp_le : ∀ z, rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8) (ε / 8) z ≤
      (closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8)).indicator 1 z := by
    intro z
    by_cases hz : z ∈ closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8)
    · rw [Set.indicator_of_mem hz]; exact rampAt_le_one _ _ _ _
    · rw [Set.indicator_of_notMem hz]
      rw [mem_closedBall, not_le] at hz
      rw [rampAt_eq_zero hδ hz.le]
  have hgm_le : ∀ z, rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) (ε / 8) z ≤
      (arc a b).indicator 1 z := by
    intro z
    by_cases hz : z ∈ arc a b
    · rw [Set.indicator_of_mem hz]; exact rampAt_le_one _ _ _ _
    · rw [Set.indicator_of_notMem hz]
      have hd : (b - a) / 2 ≤ dist z (((a + b) / 2 : ℝ) : UnitAddCircle) := by
        by_contra hcon
        exact hz (ball_subset_arc a b (mem_ball.2 (lt_of_not_ge hcon)))
      rw [rampAt_eq_zero hδ hd]
  have hgm_ge : ∀ z, (closedBall (((a + b) / 2 : ℝ) : UnitAddCircle)
        ((b - a) / 2 - ε / 8)).indicator 1 z ≤
      rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) (ε / 8) z := by
    intro z
    by_cases hz : z ∈ closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 - ε / 8)
    · rw [Set.indicator_of_mem hz, rampAt_eq_one hδ (mem_closedBall.1 hz)]
      simp
    · rw [Set.indicator_of_notMem hz]; exact rampAt_nonneg _ _ _ _
  -- bounds for the integrals of the approximations
  have hIp : ∫ z : UnitAddCircle,
      rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8) (ε / 8) z
        ≤ (b - a) + 2 * (ε / 8) := by
    refine le_trans (integral_le_measureReal measurableSet_closedBall _ hgp_le) ?_
    rw [measureReal_closedBall, max_le_iff]
    refine ⟨le_trans (min_le_right _ _) (by linarith), by linarith⟩
  have hIm : (b - a) - 2 * (ε / 8) ≤ ∫ z : UnitAddCircle,
      rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) (ε / 8) z := by
    refine le_trans ?_ (measureReal_le_integral measurableSet_closedBall _ hgm_ge)
    rw [measureReal_closedBall, min_eq_right (by linarith)]
    exact le_max_of_le_left (by linarith)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.1 (avgReal_continuous u hweyl
    (rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8) (ε / 8))) (ε / 8) hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.1 (avgReal_continuous u hweyl
    (rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) (ε / 8))) (ε / 8) hδ
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have hup : avgReal u ((arc a b).indicator 1) N ≤ avgReal u
      (rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2 + ε / 8) (ε / 8)) N := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hgp_ge _) (by positivity)
  have hdn : avgReal u (rampAt (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) (ε / 8)) N
      ≤ avgReal u ((arc a b).indicator 1) N := by
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hgm_le _) (by positivity)
  have h1 := hN₁ N (le_trans (le_max_left _ _) hN)
  have h2 := hN₂ N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ## Discharging the hypothesis for `n • α` with `α` irrational -/

theorem weylSum_tendsto_zero_of_irrational {α : ℝ} (hα : Irrational α) (h : ℤ) (hh : h ≠ 0) :
    Tendsto (weylSum (fun n : ℕ => n * α) h) atTop (𝓝 0) := by
  set q : ℂ := Complex.exp (2 * Real.pi * Complex.I * h * α) with hqdef
  have hq1 : q ≠ 1 := by
    intro hcon
    rw [hqdef, Complex.exp_eq_one_iff] at hcon
    obtain ⟨n, hn⟩ := hcon
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hc : (h : ℂ) * α = n := by
      field_simp at hn ⊢
      linear_combination hn
    have hreal : (h : ℝ) * α = n := by exact_mod_cast hc
    exact (hα.intCast_mul hh).ne_int n hreal
  have hnorm : ‖q‖ = 1 := by
    rw [hqdef, Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * Complex.I * h * α).re = 0 := by simp
    rw [hre]
    simp
  have hq0 : (0 : ℝ) < ‖q - 1‖ := by simpa [sub_eq_zero] using hq1
  have hbound : ∀ N : ℕ, ‖weylSum (fun n : ℕ => n * α) h N‖ ≤ (N : ℝ)⁻¹ * (2 / ‖q - 1‖) := by
    intro N
    have hsum : ∑ k ∈ Finset.range N,
        Complex.exp (2 * Real.pi * Complex.I * h * (((k : ℝ) * α : ℝ) : ℂ))
        = (q ^ N - 1) / (q - 1) := by
      rw [← geom_sum_eq hq1]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast; ring
    simp only [weylSum]
    rw [hsum, norm_mul, norm_inv, Complex.norm_natCast, norm_div]
    have h2 : ‖q ^ N - 1‖ ≤ 2 := by
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_pow, hnorm]
      norm_num
    gcongr
  refine squeeze_zero_norm hbound ?_
  simpa using tendsto_inv_atTop_nhds_zero_nat.mul_const (2 / ‖q - 1‖)

/-- A sanity check showing that `IsEquidistributedMod1` is a nontrivial condition:
the constant sequence `0` is not equidistributed modulo one. -/
theorem not_isEquidistributedMod1_const_zero : ¬ IsEquidistributedMod1 (fun _ : ℕ => (0 : ℝ)) := by
  intro h
  have h2 := h 0 (1 / 2) le_rfl (by norm_num) (by norm_num)
  have heq : ∀ N : ℕ, (((Finset.range N).filter
      fun k => Int.fract ((fun _ : ℕ => (0 : ℝ)) k) ∈ Ico (0 : ℝ) (1 / 2)).card : ℝ) / N
      = (N : ℝ) / N := by
    intro N
    congr 2
    rw [Finset.filter_true_of_mem]
    · simp
    · intro k _
      simp [Int.fract]
  rw [show (fun N : ℕ => (((Finset.range N).filter
      fun k => Int.fract ((fun _ : ℕ => (0 : ℝ)) k) ∈ Ico (0 : ℝ) (1 / 2)).card : ℝ) / N)
      = fun N : ℕ => (N : ℝ) / N from funext heq] at h2
  have h3 : Tendsto (fun N : ℕ => (N : ℝ) / N) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    field_simp
  have h4 := tendsto_nhds_unique h2 h3
  norm_num at h4

/-- **Weyl's equidistribution theorem**: for irrational `α`, the sequence `n ↦ n α`
is equidistributed modulo one. -/
theorem isEquidistributedMod1_nat_mul_irrational {α : ℝ} (hα : Irrational α) :
    IsEquidistributedMod1 (fun n : ℕ => n * α) :=
  equidistribution_of_asymptotic _ (weylSum_tendsto_zero_of_irrational hα)

end

end Brockian.Equidistribution

