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

namespace RiemannScaffold

noncomputable def riemannXi (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta s

lemma riemannXi_apply (s : ℂ) : riemannXi s = s * (s - 1) * completedRiemannZeta s := rfl

end RiemannScaffold

theorem riemannXi_functional_equation (s : ℂ) :
    RiemannScaffold.riemannXi (1 - s) = RiemannScaffold.riemannXi s := by
  rw [RiemannScaffold.riemannXi_apply, RiemannScaffold.riemannXi_apply,
    completedRiemannZeta_one_sub]
  ring

theorem zeta_zero_of_riemannXi_zero {s : ℂ} (h : RiemannScaffold.riemannXi s = 0)
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) : riemannZeta s = 0 := by
  have hΛ : completedRiemannZeta s = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact absurd h'' hs0
      · exact absurd (by linear_combination h'') (sub_ne_zero.mpr hs1)
    · exact h'
  have := riemannZeta_def_of_ne_zero hs0
  rw [this, hΛ, zero_div]

theorem RiemannScaffold.riemannXi_eq_zero_of_nontrivial_zeta_zero {s : ℂ}
    (h : riemannZeta s = 0) (htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) (hs1 : s ≠ 1) :
    RiemannScaffold.riemannXi s = 0 := by
  by_cases hs0 : s = 0
  · subst hs0; simp [RiemannScaffold.riemannXi]
  · rw [riemannZeta_def_of_ne_zero hs0] at h
    have hΛ : completedRiemannZeta s = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · exfalso
        obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp h'
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simp at hn; exact hs0 hn
        · refine htriv ⟨n - 1, ?_⟩
          have hle : (1 : ℕ) ≤ n := hpos
          rw [hn]
          push_cast [Nat.cast_sub hle]
          ring
    simp [RiemannScaffold.riemannXi, hΛ]

theorem riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) :
    RiemannScaffold.riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at h0
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  have htriv : ¬ ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, rfl⟩
    have hre : (-2 * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
      simp [Complex.mul_re, Complex.add_re, Complex.add_im]
    rw [hre] at h0
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  constructor
  · intro h; exact zeta_zero_of_riemannXi_zero h hs0 hs1
  · intro h
    exact RiemannScaffold.riemannXi_eq_zero_of_nontrivial_zeta_zero h htriv hs1

theorem zeta_zero_one_sub_of_mem_critical_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  have hr : (1 - s).re = 1 - s.re := by simp
  have hstrip0 : 0 < (1 - s).re := by rw [hr]; linarith
  have hstrip1 : (1 - s).re < 1 := by rw [hr]; linarith
  have hxi : RiemannScaffold.riemannXi s = 0 :=
    (riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip h0 h1).mpr hz
  have hxi' : RiemannScaffold.riemannXi (1 - s) = 0 := by
    rw [riemannXi_functional_equation]; exact hxi
  exact (riemannXi_eq_zero_iff_zeta_zero_of_mem_critical_strip hstrip0 hstrip1).mp hxi'

/-! ### Conjugation symmetry of the Riemann zeta function -/

/-- On the half-plane of absolute convergence, `ζ` commutes with complex conjugation. -/
theorem riemannZeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) s)) = riemannZeta s := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs', zeta_eq_tsum_one_div_nat_add_one_cpow hs,
    Complex.conj_tsum]
  refine tsum_congr fun n => ?_
  have harg : ((n : ℂ) + 1).arg ≠ Real.pi := by
    have : ((n : ℂ) + 1) = ((n + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.arg_ofReal_of_nonneg (by positivity)]
    exact fun h => Real.pi_ne_zero h.symm
  have hconj : (starRingEnd ℂ) ((n : ℂ) + 1) = (n : ℂ) + 1 := by
    simp
  have := Complex.conj_cpow ((n : ℂ) + 1) s harg
  rw [hconj] at this
  rw [map_div₀]
  simp only [map_one]
  rw [← this]

/-- `ζ` commutes with complex conjugation away from the pole. -/
theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) := by
  set g : ℂ → ℂ := fun z => (starRingEnd ℂ) (riemannZeta ((starRingEnd ℂ) z)) with hg
  have hUopen : IsOpen ({(1 : ℂ)}ᶜ) := isOpen_compl_singleton
  have hUconn : IsPreconnected ({(1 : ℂ)}ᶜ) :=
    (isConnected_compl_singleton_of_one_lt_rank (E := ℂ)
      (by simp [Complex.rank_real_complex]) 1).isPreconnected
  have hzeta : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hgan : AnalyticOnNhd ℂ g ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    have hz' : (starRingEnd ℂ) z ≠ 1 := by
      intro h
      apply hz
      have := congrArg (starRingEnd ℂ) h
      simpa using this
    have hd : DifferentiableAt ℂ riemannZeta ((starRingEnd ℂ) z) :=
      differentiableAt_riemannZeta hz'
    have := hd.conj_conj
    rw [Complex.conj_conj] at this
    exact this.differentiableWithinAt
  have hev : riemannZeta =ᶠ[nhds (2 : ℂ)] g := by
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := by
      refine (isOpen_lt continuous_const Complex.continuous_re).mem_nhds ?_
      norm_num
    filter_upwards [hmem] with z hz
    exact (riemannZeta_conj_of_one_lt_re hz).symm
  have h2 : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have : (2 : ℂ).re = (1 : ℂ).re := by rw [h]
    norm_num at this
  have := hzeta.eqOn_of_preconnected_of_eventuallyEq hgan hUconn h2 hev
  have hval := this (Set.mem_compl_singleton_iff.mpr hs)
  rw [hg] at hval
  simp only at hval
  rw [hval, Complex.conj_conj]

theorem zeta_zero_quartet_of_mem_critical_strip {s : ℂ}
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : riemannZeta s = 0) :
    riemannZeta s = 0 ∧ riemannZeta (1 - s) = 0 ∧
      riemannZeta (starRingEnd ℂ s) = 0 ∧
      riemannZeta (1 - starRingEnd ℂ s) = 0 := by
  have hs1 : s ≠ 1 := by rintro rfl; simp at h1
  have hconj : riemannZeta (starRingEnd ℂ s) = 0 := by
    rw [riemannZeta_conj hs1, hz, map_zero]
  have hcre : ((starRingEnd ℂ) s).re = s.re := Complex.conj_re s
  refine ⟨hz, zeta_zero_one_sub_of_mem_critical_strip h0 h1 hz, hconj, ?_⟩
  refine zeta_zero_one_sub_of_mem_critical_strip (by rw [hcre]; exact h0)
    (by rw [hcre]; exact h1) hconj

