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
# Weyl's equidistribution theorem for irrational rotations

For an irrational number `a`, the fractional parts `{n * a}` are equidistributed in `[0,1)`:
for every subinterval `[u, v) ⊆ [0,1]` the proportion of `n < N` with `Int.fract (n * a) ∈ [u, v)`
tends to `v - u`.

The proof follows Weyl's method:

* `WeylSumsVanish a` is the statement that all non-trivial exponential (Weyl) sums along the
  orbit have vanishing averages;
* `tendsto_orbitAvg_of_weylSumsVanish` is the *conditional* statement that `WeylSumsVanish a`
  implies convergence of Birkhoff averages of continuous functions to their integral;
* `weylSumsVanish_of_irrational` *discharges* that hypothesis for irrational `a` (geometric
  series estimate), making the result unconditional;
* `equidistribution_of_asymptotic_exists` is the final unconditional interval version.
-/

namespace Brockian.Equidistribution

open Filter Topology MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- Birkhoff / empirical average of a complex-valued function over the first `N` points of the
orbit of `0` under the rotation by `a` on the circle `ℝ / ℤ`. -/
def orbitAvg (a : ℝ) (f : AddCircle (1 : ℝ) → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, f ((n * a : ℝ) : AddCircle (1 : ℝ))

/-- Real-valued Birkhoff average. -/
def orbitAvgR (a : ℝ) (f : AddCircle (1 : ℝ) → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, f ((n * a : ℝ) : AddCircle (1 : ℝ))

/-- The Weyl criterion hypothesis: all non-trivial exponential sums along the orbit have
averages tending to `0`. -/
def WeylSumsVanish (a : ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 → Tendsto (fun N => orbitAvg a (fourier k) N) atTop (𝓝 0)

/-! ### Integrals of the Fourier monomials -/

theorem integral_fourier_ne_zero {k : ℤ} (hk : k ≠ 0) :
    ∫ x : AddCircle (1 : ℝ), fourier k x ∂AddCircle.haarAddCircle = 0 :=
  integral_eq_zero_of_add_right_eq_neg (μ := AddCircle.haarAddCircle)
    (fourier_add_half_inv_index hk one_pos)

/-! ### Discharging the Weyl hypothesis -/

theorem weylSumsVanish_of_irrational {a : ℝ} (ha : Irrational a) : WeylSumsVanish a := by
  intro k hk
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * k * a) with hz
  have hnorm : ‖z‖ = 1 := by
    rw [hz, Complex.norm_exp]
    norm_num [Complex.ext_iff]
  have hzne : z ≠ 1 := by
    rw [hz]
    intro h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have hc : (k : ℂ) * a = m := by
      apply mul_left_cancel₀ h2
      linear_combination hm
    have hr : (k : ℝ) * a = (m : ℝ) := by exact_mod_cast hc
    exact (ha.intCast_mul hk).ne_int m hr
  have hterm : ∀ n : ℕ, (fourier k) ((n * a : ℝ) : AddCircle (1 : ℝ)) = z ^ n := by
    intro n
    rw [fourier_coe_apply, hz, ← Complex.exp_nat_mul]
    push_cast
    ring_nf
  have hz1 : (0 : ℝ) < ‖z - 1‖ := by
    simpa [sub_eq_zero] using hzne
  have hrw : ∀ N : ℕ, orbitAvg a (fourier k) N
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, z ^ n := by
    intro N
    simp only [orbitAvg, hterm]
  simp only [hrw]
  refine squeeze_zero_norm (a := fun N : ℕ => (2 / ‖z - 1‖) / N) ?_
    (tendsto_const_div_atTop_nhds_zero_nat _)
  intro N
  have h2 : ‖z ^ N - 1‖ ≤ 2 := by
    calc ‖z ^ N - 1‖ ≤ ‖z ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_pow, hnorm]
  rw [norm_mul, norm_inv, geom_sum_eq hzne, norm_div, Complex.norm_natCast]
  show (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖) ≤ 2 / ‖z - 1‖ / N
  have he : (N : ℝ)⁻¹ * (‖z ^ N - 1‖ / ‖z - 1‖) = ‖z ^ N - 1‖ / ‖z - 1‖ / N := by ring
  rw [he]
  gcongr

/-! ### Elementary estimates -/

theorem integrable_of_continuousMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : C(AddCircle (1 : ℝ), E)) : Integrable f AddCircle.haarAddCircle :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem norm_orbitAvg_sub_le (a : ℝ) (f g : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    ‖orbitAvg a f N - orbitAvg a g N‖ ≤ ‖f - g‖ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp [orbitAvg, norm_nonneg]
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiff : orbitAvg a f N - orbitAvg a g N
      = (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, ((f - g) ((n * a : ℝ) : AddCircle (1 : ℝ))) := by
    simp only [orbitAvg, ContinuousMap.sub_apply, Finset.sum_sub_distrib, mul_sub]
  rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast]
  have hs : ‖∑ n ∈ Finset.range N, ((f - g) ((n * a : ℝ) : AddCircle (1 : ℝ)))‖ ≤ N * ‖f - g‖ := by
    calc ‖∑ n ∈ Finset.range N, ((f - g) ((n * a : ℝ) : AddCircle (1 : ℝ)))‖
        ≤ ∑ n ∈ Finset.range N, ‖(f - g) ((n * a : ℝ) : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, ‖f - g‖ :=
          Finset.sum_le_sum fun n _ => ContinuousMap.norm_coe_le_norm (f - g) _
      _ = N * ‖f - g‖ := by simp
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N, ((f - g) ((n * a : ℝ) : AddCircle (1 : ℝ)))‖
      ≤ (N : ℝ)⁻¹ * (N * ‖f - g‖) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ‖f - g‖ := by field_simp

theorem norm_integral_sub_le (f g : C(AddCircle (1 : ℝ), ℂ)) :
    ‖(∫ x, f x ∂AddCircle.haarAddCircle) - ∫ x, g x ∂AddCircle.haarAddCircle‖ ≤ ‖f - g‖ := by
  rw [← integral_sub (integrable_of_continuousMap f) (integrable_of_continuousMap g)]
  have hb := norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
    (C := ‖f - g‖) (f := fun x => f x - g x)
    (Filter.Eventually.of_forall fun x => by
      simpa using ContinuousMap.norm_coe_le_norm (f - g) x)
  simpa using hb

/-! ### The conditional statement -/

theorem tendsto_orbitAvg_of_weylSumsVanish {a : ℝ} (h : WeylSumsVanish a)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (orbitAvg a f) atTop (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle)) := by
  have hspan : ∀ g ∈ Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))),
      Tendsto (orbitAvg a g) atTop (𝓝 (∫ x, g x ∂AddCircle.haarAddCircle)) := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨k, rfl⟩ := hx
        rcases eq_or_ne k 0 with rfl | hk
        · have hint : (∫ x : AddCircle (1 : ℝ), fourier 0 x ∂AddCircle.haarAddCircle) = 1 := by
            simp
          rw [hint]
          refine Tendsto.congr' ?_ tendsto_const_nhds
          filter_upwards [eventually_ge_atTop 1] with N hN
          have hNR : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          simp only [orbitAvg, fourier_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            mul_one]
          field_simp
        · rw [integral_fourier_ne_zero hk]
          exact h k hk
    | zero =>
        have hz : ∀ N, orbitAvg a (0 : C(AddCircle (1 : ℝ), ℂ)) N = 0 := by
          intro N; simp [orbitAvg]
        have h0 : (∫ x, (0 : C(AddCircle (1 : ℝ), ℂ)) x ∂AddCircle.haarAddCircle) = 0 := by simp
        rw [h0]
        exact Tendsto.congr (fun N => (hz N).symm) tendsto_const_nhds
    | add u v _ _ hu hv =>
        have hsum : ∀ N, orbitAvg a (u + v) N = orbitAvg a u N + orbitAvg a v N := by
          intro N
          simp only [orbitAvg, Pi.add_apply, Finset.sum_add_distrib, mul_add]
        have hint : (∫ x, (u + v) x ∂AddCircle.haarAddCircle)
            = (∫ x, u x ∂AddCircle.haarAddCircle) + ∫ x, v x ∂AddCircle.haarAddCircle := by
          simp only [ContinuousMap.add_apply]
          exact integral_add (integrable_of_continuousMap u) (integrable_of_continuousMap v)
        rw [hint]
        exact Tendsto.congr (fun N => (hsum N).symm) (hu.add hv)
    | smul c u _ hu =>
        have hsum : ∀ N, orbitAvg a (c • u) N = c * orbitAvg a u N := by
          intro N
          simp only [orbitAvg, Pi.smul_apply, smul_eq_mul]
          rw [← Finset.mul_sum]
          ring
        have hint : (∫ x, (c • u) x ∂AddCircle.haarAddCircle)
            = c * ∫ x, u x ∂AddCircle.haarAddCircle := by
          simp only [ContinuousMap.smul_apply, smul_eq_mul]
          simpa using integral_smul c (fun x => u x)
        rw [hint]
        exact Tendsto.congr (fun N => (hsum N).symm) (hu.const_mul c)
  have hd : Dense ((Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) :
      Submodule ℂ C(AddCircle (1 : ℝ), ℂ)) : Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact span_fourier_closure_eq_top
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgmem, hgd⟩ := hd.exists_dist_lt f (by linarith : (0:ℝ) < ε / 3)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp (hspan g hgmem)) (ε / 3) (by linarith)
  refine ⟨N₀, fun N hN => ?_⟩
  have h1 : ‖orbitAvg a f N - orbitAvg a g N‖ ≤ ‖f - g‖ := norm_orbitAvg_sub_le a f g N
  have h2 : dist (orbitAvg a g N) (∫ x, g x ∂AddCircle.haarAddCircle) < ε / 3 := hN₀ N hN
  have h3 : ‖(∫ x, g x ∂AddCircle.haarAddCircle) - ∫ x, f x ∂AddCircle.haarAddCircle‖ ≤ ‖g - f‖ :=
    norm_integral_sub_le g f
  have hfg : ‖f - g‖ < ε / 3 := by rwa [← dist_eq_norm]
  have hgf : ‖g - f‖ < ε / 3 := by rw [← dist_eq_norm, dist_comm]; exact hgd
  have hkey := dist_triangle4 (orbitAvg a f N) (orbitAvg a g N)
    (∫ x, g x ∂AddCircle.haarAddCircle) (∫ x, f x ∂AddCircle.haarAddCircle)
  rw [dist_eq_norm (orbitAvg a f N) (orbitAvg a g N),
    dist_eq_norm (∫ x, g x ∂AddCircle.haarAddCircle) (∫ x, f x ∂AddCircle.haarAddCircle)] at hkey
  linarith

/-- Unconditional version for continuous complex-valued test functions. -/
theorem tendsto_orbitAvg {a : ℝ} (ha : Irrational a) (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (orbitAvg a f) atTop (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle)) :=
  tendsto_orbitAvg_of_weylSumsVanish (weylSumsVanish_of_irrational ha) f

/-- Unconditional version for continuous real-valued test functions. -/
theorem tendsto_orbitAvgR {a : ℝ} (ha : Irrational a) (f : C(AddCircle (1 : ℝ), ℝ)) :
    Tendsto (orbitAvgR a f) atTop (𝓝 (∫ x, f x ∂AddCircle.haarAddCircle)) := by
  set F : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x => ((f x : ℝ) : ℂ), Complex.continuous_ofReal.comp f.continuous⟩ with hF
  have hcast : ∀ N, orbitAvg a F N = ((orbitAvgR a f N : ℝ) : ℂ) := by
    intro N
    simp only [orbitAvg, orbitAvgR, hF, ContinuousMap.coe_mk]
    push_cast
    ring
  have hint : (∫ x, F x ∂AddCircle.haarAddCircle)
      = ((∫ x, f x ∂AddCircle.haarAddCircle : ℝ) : ℂ) := integral_complex_ofReal
  have h := tendsto_orbitAvg ha F
  rw [hint] at h
  rw [← tendsto_ofReal_iff]
  exact Tendsto.congr hcast h

/-! ### Continuous approximations of indicator functions of intervals -/

/-- A continuous "trapezoid" bump on the circle, supported in the interval `(c, d)`, with
integral at least `d - c - 2 * δ`. -/
theorem exists_tent {c d δ : ℝ} (hc : 0 ≤ c) (hd : d ≤ 1) (hδ : 0 < δ) :
    ∃ g : C(AddCircle (1 : ℝ), ℝ),
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ 1) ∧
      (∀ x : ℝ, Int.fract x ∉ Ioo c d → g (x : AddCircle (1 : ℝ)) = 0) ∧
      d - c - 2 * δ ≤ ∫ x, g x ∂AddCircle.haarAddCircle := by
  -- the trapezoid on the real line
  set ψ : ℝ → ℝ := fun x => max 0 (min 1 (min ((x - c) / δ) ((d - x) / δ))) with hψ
  have hcont : Continuous ψ := by fun_prop
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => le_max_left _ _
  have hψ1 : ∀ x, ψ x ≤ 1 := fun x => max_le zero_le_one (min_le_left _ _)
  have hψsupp : ∀ x, x ∉ Ioo c d → ψ x = 0 := by
    intro x hx
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx
    have hle : min 1 (min ((x - c) / δ) ((d - x) / δ)) ≤ 0 := by
      rcases hx with h | h
      · have hq : (x - c) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
        exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hq)
      · have hq : (d - x) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) hq)
    simp only [hψ]
    exact max_eq_left hle
  have hψone : ∀ x, c + δ ≤ x → x ≤ d - δ → 1 ≤ ψ x := by
    intro x h1 h2
    have e1 : (1 : ℝ) ≤ (x - c) / δ := by rw [le_div_iff₀ hδ]; linarith
    have e2 : (1 : ℝ) ≤ (d - x) / δ := by rw [le_div_iff₀ hδ]; linarith
    simp only [hψ, min_eq_left (le_min e1 e2)]
    exact le_max_right _ _
  have hend : ψ 0 = ψ 1 := by
    rw [hψsupp 0 (by simp only [mem_Ioo, not_and, not_lt]; intro h; linarith),
      hψsupp 1 (by simp only [mem_Ioo, not_and, not_lt]; intro _; linarith)]
  -- transport it to the circle
  set g : C(AddCircle (1 : ℝ), ℝ) :=
    ⟨AddCircle.liftIco 1 0 ψ, AddCircle.liftIco_zero_continuous hend hcont.continuousOn⟩ with hg
  have hgcoe : ∀ x : ℝ, g (x : AddCircle (1 : ℝ)) = ψ (Int.fract x) := by
    intro x
    have h1 : ((Int.fract x : ℝ) : AddCircle (1 : ℝ)) = (x : AddCircle (1 : ℝ)) := by
      rw [Int.fract]; simp
    rw [← h1]
    simp only [hg, ContinuousMap.coe_mk]
    exact AddCircle.liftIco_zero_coe_apply ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [show (QuotientAddGroup.mk z : AddCircle (1 : ℝ)) = ((z : ℝ) : AddCircle (1 : ℝ)) from rfl,
      hgcoe]
    exact hψ0 _
  · intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [show (QuotientAddGroup.mk z : AddCircle (1 : ℝ)) = ((z : ℝ) : AddCircle (1 : ℝ)) from rfl,
      hgcoe]
    exact hψ1 _
  · intro x hx
    rw [hgcoe]
    exact hψsupp _ hx
  · -- the integral bound
    have hmeas : (AddCircle.haarAddCircle : Measure (AddCircle (1 : ℝ))) = volume := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
    rw [hmeas, ← AddCircle.integral_preimage 1 0 g]
    have hcongr : (∫ a in Ioc (0 : ℝ) (0 + 1), g (a : AddCircle (1 : ℝ)))
        = ∫ a in Ioc (0 : ℝ) (0 + 1), ψ a := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun a ha => ?_)
      show g (a : AddCircle (1 : ℝ)) = ψ a
      rw [hgcoe]
      rcases eq_or_lt_of_le ha.2 with h | h
      · rw [show a = 1 by simpa using h]
        simp [Int.fract, hend]
      · rw [Int.fract_eq_self.mpr ⟨ha.1.le, by simpa using h⟩]
    rw [hcongr, zero_add]
    rcases le_or_gt (d - c - 2 * δ) 0 with hsmall | hbig
    · exact le_trans hsmall (setIntegral_nonneg measurableSet_Ioc (fun a _ => hψ0 a))
    · have hsub : Ioc (c + δ) (d - δ) ⊆ Ioc (0 : ℝ) 1 := by
        apply Ioc_subset_Ioc <;> linarith
      have h1 : (∫ a in Ioc (c + δ) (d - δ), ψ a) ≤ ∫ a in Ioc (0 : ℝ) 1, ψ a :=
        setIntegral_mono_set hcont.integrableOn_Ioc (Filter.Eventually.of_forall hψ0)
          (HasSubset.Subset.eventuallyLE hsub)
      have h2 := setIntegral_ge_of_const_le (μ := (volume : Measure ℝ)) (c := (1 : ℝ))
        (s := Ioc (c + δ) (d - δ)) (f := ψ) measurableSet_Ioc (by simp [Real.volume_Ioc])
        (fun a ha => hψone a ha.1.le ha.2) hcont.integrableOn_Ioc
      rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul,
        mul_one] at h2
      linarith

/-! ### From continuous test functions to intervals -/

/-- The counting density rewritten as a Birkhoff average of an indicator. -/
theorem density_eq_avg_indicator (a u v : ℝ) (N : ℕ) :
    ((((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * a) ∈ Ico u v).card : ℝ) / N)
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          (if Int.fract ((n : ℝ) * a) ∈ Ico u v then (1 : ℝ) else 0) := by
  rw [Finset.card_filter]
  push_cast
  rw [div_eq_inv_mul]

/-! ### The main theorem -/

/-- **Weyl's equidistribution theorem.**  For irrational `a`, the fractional parts of `n * a`
are equidistributed: the asymptotic density of the set of `n` with `Int.fract (n * a) ∈ [u, v)`
exists and equals `v - u`. -/
theorem equidistribution_of_asymptotic_exists {a : ℝ} (ha : Irrational a) {u v : ℝ}
    (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ 1) :
    Tendsto (fun N : ℕ =>
        (((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * a) ∈ Ico u v).card : ℝ) / N)
      atTop (𝓝 (v - u)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / 6 with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨g₁, hg₁0, hg₁1, hg₁supp, hg₁int⟩ := exists_tent hu hv hδ
  obtain ⟨ga, hga0, hga1, hgasupp, hgaint⟩ := exists_tent le_rfl (huv.trans hv) hδ
  obtain ⟨gb, hgb0, hgb1, hgbsupp, hgbint⟩ := exists_tent (hu.trans huv) le_rfl hδ
  set g₂ : C(AddCircle (1 : ℝ), ℝ) := 1 - ga - gb with hg₂def
  -- the integral of the upper approximation
  have hint2 : (∫ x, g₂ x ∂AddCircle.haarAddCircle)
      = 1 - (∫ x, ga x ∂AddCircle.haarAddCircle) - ∫ x, gb x ∂AddCircle.haarAddCircle := by
    have hIa := integrable_of_continuousMap ga
    have hIb := integrable_of_continuousMap gb
    have h1 : (∫ _x : AddCircle (1 : ℝ), (1 : ℝ) ∂AddCircle.haarAddCircle) = 1 := by simp
    have e : ∀ x, g₂ x = 1 - ga x - gb x := by
      intro x; simp [hg₂def]
    have h2 : (∫ x, ((1 : ℝ) - ga x - gb x) ∂AddCircle.haarAddCircle)
        = (∫ x, ((1 : ℝ) - ga x) ∂AddCircle.haarAddCircle)
          - ∫ x, gb x ∂AddCircle.haarAddCircle :=
      integral_sub (f := fun x => (1 : ℝ) - ga x) (g := fun x => gb x)
        ((integrable_const (1 : ℝ)).sub hIa) hIb
    have h3 : (∫ x, ((1 : ℝ) - ga x) ∂AddCircle.haarAddCircle)
        = 1 - ∫ x, ga x ∂AddCircle.haarAddCircle := by
      rw [integral_sub (f := fun _ => (1 : ℝ)) (g := fun x => ga x) (integrable_const (1 : ℝ)) hIa,
        h1]
    simp only [e]
    rw [h2, h3]
  have hint2' : (∫ x, g₂ x ∂AddCircle.haarAddCircle) ≤ v - u + 4 * δ := by
    rw [hint2]; linarith
  -- comparison of the Birkhoff averages with the counting density
  have hlow : ∀ N : ℕ, orbitAvgR a g₁ N
      ≤ (((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * a) ∈ Ico u v).card : ℝ) / N := by
    intro N
    rw [density_eq_avg_indicator, orbitAvgR]
    have hpt : ∀ n ∈ Finset.range N, g₁ ((n * a : ℝ) : AddCircle (1 : ℝ))
        ≤ (if Int.fract ((n : ℝ) * a) ∈ Ico u v then (1 : ℝ) else 0) := by
      intro n _
      by_cases hmem : Int.fract ((n : ℝ) * a) ∈ Ico u v
      · rw [if_pos hmem]; exact hg₁1 _
      · have hnot : Int.fract ((n : ℝ) * a) ∉ Ioo u v := fun hx => hmem ⟨hx.1.le, hx.2⟩
        rw [if_neg hmem, hg₁supp _ hnot]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by positivity)
  have hhigh : ∀ N : ℕ,
      (((Finset.range N).filter fun n : ℕ => Int.fract ((n : ℝ) * a) ∈ Ico u v).card : ℝ) / N
        ≤ orbitAvgR a g₂ N := by
    intro N
    rw [density_eq_avg_indicator, orbitAvgR]
    have hpt : ∀ n ∈ Finset.range N,
        (if Int.fract ((n : ℝ) * a) ∈ Ico u v then (1 : ℝ) else 0)
          ≤ g₂ ((n * a : ℝ) : AddCircle (1 : ℝ)) := by
      intro n _
      have hfr := Int.fract_nonneg ((n : ℝ) * a)
      have hfr1 := Int.fract_lt_one ((n : ℝ) * a)
      by_cases hmem : Int.fract ((n : ℝ) * a) ∈ Ico u v
      · have hna : Int.fract ((n : ℝ) * a) ∉ Ioo (0 : ℝ) u := fun hx =>
          absurd hmem.1 (not_le.mpr hx.2)
        have hnb : Int.fract ((n : ℝ) * a) ∉ Ioo v 1 := fun hx =>
          absurd hmem.2 (not_lt.mpr hx.1.le)
        rw [if_pos hmem, hg₂def]
        simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply]
        rw [hgasupp _ hna, hgbsupp _ hnb]
        norm_num
      · have hle : ga ((n * a : ℝ) : AddCircle (1 : ℝ)) + gb ((n * a : ℝ) : AddCircle (1 : ℝ))
            ≤ 1 := by
          by_cases hx : Int.fract ((n : ℝ) * a) ∈ Ioo (0 : ℝ) u
          · have hnb : Int.fract ((n : ℝ) * a) ∉ Ioo v 1 := fun hy =>
              absurd (hx.2.trans_le (huv.trans hy.1.le)) (lt_irrefl _)
            have := hga1 ((n * a : ℝ) : AddCircle (1 : ℝ))
            rw [hgbsupp _ hnb]
            linarith
          · have := hgb1 ((n * a : ℝ) : AddCircle (1 : ℝ))
            rw [hgasupp _ hx]
            linarith
        simp only [hmem, if_false, hg₂def, ContinuousMap.sub_apply, ContinuousMap.one_apply]
        linarith
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hpt) (by positivity)
  -- pass to the limit
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp (tendsto_orbitAvgR ha g₁) δ hδ
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp (tendsto_orbitAvgR ha g₂) δ hδ
  refine ⟨max N₁ N₂, fun N hN => ?_⟩
  have h1 := hN₁ N (le_trans (le_max_left _ _) hN)
  have h2 := hN₂ N (le_trans (le_max_right _ _) hN)
  rw [Real.dist_eq, abs_lt] at h1 h2
  rw [Real.dist_eq, abs_lt]
  have hl := hlow N
  have hh := hhigh N
  constructor <;> [linarith; linarith]

end

end Brockian.Equidistribution

