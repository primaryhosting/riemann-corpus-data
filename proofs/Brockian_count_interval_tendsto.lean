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

open Filter Finset MeasureTheory
open scoped Topology

namespace Brockian
namespace EquidistributionBVReduction

/-- A sequence `x : ℕ → ℝ` with values in `[0, 1)` is *uniformly distributed* if for every
`c ∈ [0, 1]` the proportion of the first `N` terms lying in `[0, c)` tends to `c`. -/
def UniformlyDistributed (x : ℕ → ℝ) : Prop :=
  (∀ n, x n ∈ Set.Ico (0 : ℝ) 1) ∧
    ∀ c ∈ Set.Icc (0 : ℝ) 1,
      Tendsto (fun N : ℕ => (((range N).filter (fun n => x n < c)).card : ℝ) / N) atTop (𝓝 c)

section Counting

variable {x : ℕ → ℝ}

/-- The proportion of the first `N` terms of a uniformly distributed sequence lying in a
subinterval `[a, b)` of `[0, 1]` tends to `b - a`. -/
lemma count_interval_tendsto (hx : UniformlyDistributed x) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Tendsto (fun N : ℕ => (((range N).filter (fun n => a ≤ x n ∧ x n < b)).card : ℝ) / N)
      atTop (𝓝 (b - a)) := by
  obtain ⟨-, hlim⟩ := hx
  have hcard : ∀ N : ℕ,
      ((range N).filter (fun n => x n < a)).card
        + ((range N).filter (fun n => a ≤ x n ∧ x n < b)).card
      = ((range N).filter (fun n => x n < b)).card := by
    intro N
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext n
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro (⟨hn, h⟩ | ⟨hn, -, h⟩)
        · exact ⟨hn, lt_of_lt_of_le h hab⟩
        · exact ⟨hn, h⟩
      · rintro ⟨hn, h⟩
        rcases lt_or_ge (x n) a with h' | h'
        · exact Or.inl ⟨hn, h'⟩
        · exact Or.inr ⟨hn, h', h⟩
    · rw [Finset.disjoint_left]
      rintro n hn1 hn2
      simp only [Finset.mem_filter] at hn1 hn2
      linarith [hn1.2, hn2.2.1]
  have hA := hlim a ⟨ha, hab.trans hb⟩
  have hB := hlim b ⟨ha.trans hab, hb⟩
  refine (hB.sub hA).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have h := hcard N
  field_simp
  push_cast [← h]
  ring

end Counting

/-- Membership in the `i`-th fiber of the floor map. -/
lemma floor_fiber_iff {k : ℕ} (hk : 0 < k) {y : ℝ} (hy : 0 ≤ y) (i : ℕ) :
    ⌊(k : ℝ) * y⌋₊ = i ↔ ((i : ℝ) / k ≤ y ∧ y < ((i : ℝ) + 1) / k) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Nat.floor_eq_iff (by positivity), div_le_iff₀ hk0, lt_div_iff₀ hk0]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> [linarith [h1]; linarith [h2]]
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

lemma integral_le_of_monotone {g : ℝ → ℝ} (hg : Monotone g) {a b : ℝ} (hab : a ≤ b) :
    (∫ t in a..b, g t) ≤ (b - a) * g b := by
  have hi : IntervalIntegrable g MeasureTheory.volume a b := hg.intervalIntegrable
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (f := g) (g := fun _ => g b) hab hi intervalIntegrable_const (fun t ht => hg ht.2)
  simpa [mul_comm] using h

lemma le_integral_of_monotone {g : ℝ → ℝ} (hg : Monotone g) {a b : ℝ} (hab : a ≤ b) :
    (b - a) * g a ≤ ∫ t in a..b, g t := by
  have hi : IntervalIntegrable g MeasureTheory.volume a b := hg.intervalIntegrable
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (f := fun _ => g a) (g := g) hab intervalIntegrable_const hi (fun t ht => hg ht.1)
  simpa [mul_comm] using h

section Monotone

variable {x : ℕ → ℝ} {g : ℝ → ℝ}

/-- Approximation at scale `k`: the Birkhoff averages of a monotone function along a uniformly
distributed sequence are eventually within `(g 1 - g 0) / k + ε` of the integral. -/
lemma abs_average_sub_integral_le (hx : UniformlyDistributed x) (hg : Monotone g)
    {k : ℕ} (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      |(∑ n ∈ range N, g (x n)) / N - ∫ t in (0 : ℝ)..1, g t| ≤ (g 1 - g 0) / k + ε := by
  classical
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set t : ℕ → ℝ := fun i => (i : ℝ) / k with htdef
  have ht0 : t 0 = 0 := by simp [htdef]
  have htk : t k = 1 := by
    simp only [htdef]
    field_simp
  have htsucc : ∀ i : ℕ, t (i + 1) = ((i : ℝ) + 1) / k := by
    intro i
    simp only [htdef]
    push_cast
    ring
  have htdiff : ∀ i : ℕ, t (i + 1) - t i = 1 / k := by
    intro i
    rw [htsucc i]
    simp only [htdef]
    ring
  have htmono : ∀ i : ℕ, t i ≤ t (i + 1) := by
    intro i
    have := htdiff i
    linarith [this, one_div_pos.2 hkR]
  have htnonneg : ∀ i : ℕ, 0 ≤ t i := by
    intro i; positivity
  set F : ℕ → ℕ → Finset ℕ := fun i N => (range N).filter (fun n => ⌊(k : ℝ) * x n⌋₊ = i)
    with hFdef
  have hmemF : ∀ (i N n : ℕ), n ∈ F i N ↔ (n ∈ range N ∧ t i ≤ x n ∧ x n < t (i + 1)) := by
    intro i N n
    simp only [hFdef, Finset.mem_filter]
    rw [floor_fiber_iff hk (hx.1 n).1, htsucc]
  have hFeq : ∀ (i N : ℕ),
      F i N = (range N).filter (fun n => t i ≤ x n ∧ x n < t (i + 1)) := by
    intro i N
    ext n
    rw [hmemF i N n, Finset.mem_filter]
  have hFcount : ∀ i < k, Tendsto (fun N : ℕ => ((F i N).card : ℝ) / N) atTop (𝓝 (1 / k)) := by
    intro i hi
    have hb : t (i + 1) ≤ 1 := by
      rw [htsucc, div_le_one hkR]
      have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hi
      linarith
    have h := count_interval_tendsto hx (a := t i) (b := t (i + 1)) (htnonneg i) (htmono i) hb
    rw [htdiff i] at h
    simpa only [hFeq] using h
  have hsum_fiber : ∀ N : ℕ, ∑ i ∈ range k, ∑ n ∈ F i N, g (x n) = ∑ n ∈ range N, g (x n) := by
    intro N
    refine Finset.sum_fiberwise_of_maps_to ?_ _
    intro n _
    simp only [Finset.mem_range]
    have h1 : x n < 1 := (hx.1 n).2
    have h0 : 0 ≤ x n := (hx.1 n).1
    refine (Nat.floor_lt (by positivity)).2 ?_
    nlinarith
  have hupper : ∀ N : ℕ,
      (∑ n ∈ range N, g (x n)) ≤ ∑ i ∈ range k, ((F i N).card : ℝ) * g (t (i + 1)) := by
    intro N
    rw [← hsum_fiber N]
    refine Finset.sum_le_sum ?_
    intro i _
    have hb : ∀ n ∈ F i N, g (x n) ≤ g (t (i + 1)) := fun n hn =>
      hg ((hmemF i N n).1 hn).2.2.le
    calc ∑ n ∈ F i N, g (x n) ≤ (F i N).card • g (t (i + 1)) :=
          Finset.sum_le_card_nsmul _ _ _ hb
      _ = ((F i N).card : ℝ) * g (t (i + 1)) := by simp [nsmul_eq_mul]
  have hlower : ∀ N : ℕ,
      (∑ i ∈ range k, ((F i N).card : ℝ) * g (t i)) ≤ ∑ n ∈ range N, g (x n) := by
    intro N
    rw [← hsum_fiber N]
    refine Finset.sum_le_sum ?_
    intro i _
    have hb : ∀ n ∈ F i N, g (t i) ≤ g (x n) := fun n hn =>
      hg ((hmemF i N n).1 hn).2.1
    calc ((F i N).card : ℝ) * g (t i) = (F i N).card • g (t i) := by simp [nsmul_eq_mul]
      _ ≤ ∑ n ∈ F i N, g (x n) := Finset.card_nsmul_le_sum _ _ _ hb
  have hpart : ∑ i ∈ range k, (∫ s in (t i)..(t (i + 1)), g s) = ∫ s in (0 : ℝ)..1, g s := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := g) (μ := MeasureTheory.volume) (a := t) (n := k)
      (fun i _ => hg.intervalIntegrable)
    rwa [ht0, htk] at h
  have hIle : (∫ s in (0 : ℝ)..1, g s) ≤ ∑ i ∈ range k, (1 / (k : ℝ)) * g (t (i + 1)) := by
    rw [← hpart]
    refine Finset.sum_le_sum ?_
    intro i _
    have h := integral_le_of_monotone hg (htmono i)
    rwa [htdiff i] at h
  have hIge : (∑ i ∈ range k, (1 / (k : ℝ)) * g (t i)) ≤ ∫ s in (0 : ℝ)..1, g s := by
    rw [← hpart]
    refine Finset.sum_le_sum ?_
    intro i _
    have h := le_integral_of_monotone hg (htmono i)
    rwa [htdiff i] at h
  have hUL : (∑ i ∈ range k, (1 / (k : ℝ)) * g (t (i + 1)))
      - (∑ i ∈ range k, (1 / (k : ℝ)) * g (t i)) = (g 1 - g 0) / k := by
    rw [← Finset.sum_sub_distrib]
    have hterm : ∀ i : ℕ, (1 / (k : ℝ)) * g (t (i + 1)) - (1 / (k : ℝ)) * g (t i)
        = (1 / (k : ℝ)) * (g (t (i + 1)) - g (t i)) := by intro i; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => g (t i)), ht0, htk]
    ring
  have hUlim : Tendsto (fun N : ℕ => ∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t (i + 1)))
      atTop (𝓝 (∑ i ∈ range k, (1 / (k : ℝ)) * g (t (i + 1)))) :=
    tendsto_finset_sum _ fun i hi => (hFcount i (Finset.mem_range.1 hi)).mul_const _
  have hLlim : Tendsto (fun N : ℕ => ∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t i))
      atTop (𝓝 (∑ i ∈ range k, (1 / (k : ℝ)) * g (t i))) :=
    tendsto_finset_sum _ fun i hi => (hFcount i (Finset.mem_range.1 hi)).mul_const _
  have hU' : ∀ᶠ N : ℕ in atTop,
      |(∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t (i + 1)))
        - ∑ i ∈ range k, (1 / (k : ℝ)) * g (t (i + 1))| ≤ ε := by
    rw [Metric.tendsto_atTop] at hUlim
    obtain ⟨N₁, h₁⟩ := hUlim ε hε
    filter_upwards [eventually_ge_atTop N₁] with N hN
    have := h₁ N hN
    rw [Real.dist_eq] at this
    linarith
  have hL' : ∀ᶠ N : ℕ in atTop,
      |(∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t i))
        - ∑ i ∈ range k, (1 / (k : ℝ)) * g (t i)| ≤ ε := by
    rw [Metric.tendsto_atTop] at hLlim
    obtain ⟨N₁, h₁⟩ := hLlim ε hε
    filter_upwards [eventually_ge_atTop N₁] with N hN
    have := h₁ N hN
    rw [Real.dist_eq] at this
    linarith
  filter_upwards [eventually_gt_atTop 0, hU', hL'] with N hN hUN hLN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hSU : (∑ n ∈ range N, g (x n)) / N
      ≤ ∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t (i + 1)) := by
    have hrw : (∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t (i + 1)))
        = (∑ i ∈ range k, ((F i N).card : ℝ) * g (t (i + 1))) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrw]
    exact (div_le_div_iff_of_pos_right hNR).mpr (hupper N)
  have hSL : (∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t i))
      ≤ (∑ n ∈ range N, g (x n)) / N := by
    have hrw : (∑ i ∈ range k, (((F i N).card : ℝ) / N) * g (t i))
        = (∑ i ∈ range k, ((F i N).card : ℝ) * g (t i)) / N := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrw]
    exact (div_le_div_iff_of_pos_right hNR).mpr (hlower N)
  rw [abs_le] at hUN hLN ⊢
  constructor
  · linarith [hUN.1, hUN.2, hLN.1, hLN.2, hIle, hIge, hUL, hSU, hSL]
  · linarith [hUN.1, hUN.2, hLN.1, hLN.2, hIle, hIge, hUL, hSU, hSL]

/-- Equidistribution for monotone functions. -/
lemma tendsto_average_of_monotone (hx : UniformlyDistributed x) (hg : Monotone g) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, g (x n)) / N) atTop (𝓝 (∫ t in (0 : ℝ)..1, g t)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨k, hk⟩ := exists_nat_gt (4 * (g 1 - g 0) / δ)
  have hk0 : 0 < k := by
    by_contra hk0
    have : k = 0 := by omega
    subst this
    have h01 : 0 ≤ g 1 - g 0 := sub_nonneg.2 (hg zero_le_one)
    have : 0 ≤ 4 * (g 1 - g 0) / δ := by positivity
    simp at hk
    linarith
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hsmall : (g 1 - g 0) / k < δ / 4 := by
    rw [div_lt_iff₀ hkR]
    rw [div_lt_iff₀ hδ] at hk
    nlinarith
  have h := abs_average_sub_integral_le hx hg hk0 (ε := δ / 4) (by linarith)
  rw [eventually_atTop] at h
  obtain ⟨N₀, hN₀⟩ := h
  refine ⟨N₀, fun N hN => ?_⟩
  have := hN₀ N hN
  rw [Real.dist_eq]
  linarith

end Monotone

/-- Clamping a real number to `[0, 1]`. -/
noncomputable def clamp (t : ℝ) : ℝ := max 0 (min 1 t)

lemma clamp_mem (t : ℝ) : clamp t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma clamp_mono : Monotone clamp := fun _ _ hab =>
  max_le_max le_rfl (min_le_min le_rfl hab)

lemma clamp_eq_self {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clamp t = t := by
  obtain ⟨h0, h1⟩ := ht
  simp [clamp, min_eq_right h1, max_eq_right h0]

lemma monotone_comp_clamp {g : ℝ → ℝ} (hg : MonotoneOn g (Set.Icc (0 : ℝ) 1)) :
    Monotone (fun t => g (clamp t)) := fun _ _ hab =>
  hg (clamp_mem _) (clamp_mem _) (clamp_mono hab)

/-- **Equidistribution for functions of bounded variation.**
If `x` is a uniformly distributed sequence in `[0, 1)` and `f` has bounded variation on `[0, 1]`,
then the Birkhoff averages `(1/N) ∑_{n < N} f (x n)` converge to `∫₀¹ f`. -/
theorem equidistribution_of_BV_uniform {x : ℕ → ℝ} (hx : UniformlyDistributed x)
    {f : ℝ → ℝ} (hf : BoundedVariationOn f (Set.Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, f (x n)) / N) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  set P : ℝ → ℝ := fun t => p (clamp t) with hPdef
  set Q : ℝ → ℝ := fun t => q (clamp t) with hQdef
  have hP : Monotone P := monotone_comp_clamp hp
  have hQ : Monotone Q := monotone_comp_clamp hq
  have hfeq : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t = P t - Q t := by
    intro t ht
    have : f t = p t - q t := by rw [hpq]; rfl
    rw [this, hPdef, hQdef]
    simp only [clamp_eq_self ht]
  have hfx : ∀ n, f (x n) = P (x n) - Q (x n) := fun n =>
    hfeq (x n) ⟨(hx.1 n).1, (hx.1 n).2.le⟩
  have hint : (∫ t in (0 : ℝ)..1, f t)
      = (∫ t in (0 : ℝ)..1, P t) - ∫ t in (0 : ℝ)..1, Q t := by
    rw [← intervalIntegral.integral_sub (hP.intervalIntegrable) (hQ.intervalIntegrable)]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (zero_le_one' ℝ)] at ht
    exact hfeq t ht
  have hPlim := tendsto_average_of_monotone hx hP
  have hQlim := tendsto_average_of_monotone hx hQ
  rw [hint]
  refine (hPlim.sub hQlim).congr ?_
  intro N
  rw [← sub_div, ← Finset.sum_sub_distrib]
  simp only [hfx]

/-- The identity has bounded variation on `[0, 1]`. -/
lemma boundedVariationOn_id : BoundedVariationOn (fun s : ℝ => s) (Set.Icc (0 : ℝ) 1) := by
  have hm : MonotoneOn (fun s : ℝ => s) (Set.Icc (0 : ℝ) 1) := fun _ _ _ _ h => h
  have h := hm.eVariationOn_le (a := 0) (b := 1) (by norm_num) (by norm_num)
  rw [Set.inter_self] at h
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h

/-- A special case of the main theorem: the Cesàro means of a uniformly distributed sequence
converge to `1 / 2`. -/
theorem tendsto_average_of_uniform {x : ℕ → ℝ} (hx : UniformlyDistributed x) :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, x n) / N) atTop (𝓝 (1 / 2)) := by
  simpa using equidistribution_of_BV_uniform hx boundedVariationOn_id

end EquidistributionBVReduction
end Brockian

