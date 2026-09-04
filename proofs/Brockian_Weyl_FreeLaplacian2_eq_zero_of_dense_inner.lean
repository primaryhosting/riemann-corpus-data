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
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Free Laplacian Essentially Self Adjoint Of Fourier
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap Real LineDeriv Filter
open scoped FourierTransform ComplexInnerProductSpace ENNReal Laplacian Topology

noncomputable section

namespace Brockian.Weyl.FreeLaplacian2

/-! ## An abstract criterion for essential self-adjointness

A densely defined symmetric operator `T` on a complex Hilbert space is *essentially self-adjoint*
if and only if its adjoint `T†` is self-adjoint (equivalently, its closure is self-adjoint).
The basic criterion says that this holds as soon as the ranges of `T + i` and `T - i` are dense.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- A vector orthogonal to a dense set vanishes. -/
theorem eq_zero_of_dense_inner {w : H} {S : Set H} (hS : Dense S)
    (h : ∀ y ∈ S, inner ℂ w y = 0) : w = 0 := by
  have hclosed : IsClosed {y : H | inner ℂ w y = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have huniv : (Set.univ : Set H) ⊆ {y : H | inner ℂ w y = 0} := by
    rw [← hS.closure_eq]
    exact hclosed.closure_subset_iff.2 h
  have := huniv (Set.mem_univ w)
  simpa using inner_self_eq_zero.mp this

omit [CompleteSpace H] in
/-- For a symmetric operator `T` and a purely imaginary number `t * i`, we have
`‖T x + (t * i) • x‖ ^ 2 = ‖T x‖ ^ 2 + t ^ 2 * ‖x‖ ^ 2`. -/
theorem norm_add_imag_smul_sq {T : H →ₗ.[ℂ] H} (hsymm : T.IsFormalAdjoint T) (t : ℝ)
    (x : T.domain) :
    ‖T x + ((t : ℂ) * Complex.I) • (x : H)‖ ^ 2 = ‖T x‖ ^ 2 + t ^ 2 * ‖(x : H)‖ ^ 2 := by
  have hc : (starRingEnd ℂ) (inner ℂ (T x) (x : H)) = inner ℂ (T x) (x : H) := by
    rw [inner_conj_symm]
    exact (hsymm x x).symm
  have him : (inner ℂ (T x) (x : H)).im = 0 := by
    simpa using (Complex.conj_eq_iff_im.mp hc)
  rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul]
  have h1 : RCLike.re (((t : ℂ) * Complex.I) * inner ℂ (T x) (x : H)) = 0 := by simp [him]
  rw [h1]
  simp [mul_pow, sq_abs]

omit [CompleteSpace H] in
/-- The basic estimate `‖x‖ ≤ ‖(T + i) x‖` and `‖T x‖ ≤ ‖(T + i) x‖` for symmetric `T`. -/
theorem norm_le_norm_add_imag {T : H →ₗ.[ℂ] H} (hsymm : T.IsFormalAdjoint T) (x : T.domain) :
    ‖(x : H)‖ ≤ ‖T x + Complex.I • (x : H)‖ ∧ ‖T x‖ ≤ ‖T x + Complex.I • (x : H)‖ := by
  have h := norm_add_imag_smul_sq hsymm 1 x
  simp only [Complex.ofReal_one, one_mul, one_pow] at h
  constructor
  · nlinarith [norm_nonneg ((x : H)), norm_nonneg (T x), norm_nonneg (T x + Complex.I • (x : H))]
  · nlinarith [norm_nonneg ((x : H)), norm_nonneg (T x), norm_nonneg (T x + Complex.I • (x : H))]

/-- Every element of the domain of the adjoint of a densely defined symmetric operator with dense
deficiency ranges is a limit of elements of the domain of `T`, together with their images. -/
theorem exists_tendsto_of_mem_adjoint_domain {T : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H))
    (hsymm : T.IsFormalAdjoint T)
    (hplus : Dense (Set.range fun x : T.domain => T x + Complex.I • (x : H)))
    (hminus : Dense (Set.range fun x : T.domain => T x - Complex.I • (x : H)))
    (u : T.adjoint.domain) :
    ∃ f : ℕ → T.domain, Tendsto (fun n => ((f n : H))) atTop (𝓝 (u : H)) ∧
      Tendsto (fun n => T (f n)) atTop (𝓝 (T.adjoint u)) := by
  classical
  set g : H := T.adjoint u + Complex.I • (u : H) with hgdef
  have hchoice : ∀ n : ℕ, ∃ x : T.domain, ‖(T x + Complex.I • (x : H)) - g‖ < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 (hplus g) _ hpos
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, ?_⟩
    rw [← hx, dist_eq_norm] at hdist
    simpa [norm_sub_rev] using hdist
  choose f hf using hchoice
  set G : ℕ → H := fun n => T (f n) + Complex.I • ((f n : H)) with hGdef
  have hGconv : Tendsto G atTop (𝓝 g) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hf n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have est : ∀ m n : ℕ,
      ‖(f m : H) - (f n : H)‖ ≤ ‖G m - G n‖ ∧ ‖T (f m) - T (f n)‖ ≤ ‖G m - G n‖ := by
    intro m n
    have h := norm_le_norm_add_imag hsymm (f m - f n)
    have e : T (f m - f n) + Complex.I • ((f m - f n : T.domain) : H) = G m - G n := by
      rw [LinearPMap.map_sub, Submodule.coe_sub, smul_sub, hGdef]
      module
    rw [e, LinearPMap.map_sub, Submodule.coe_sub] at h
    exact h
  have hcauchyG : CauchySeq G := hGconv.cauchySeq
  have hcf : CauchySeq (fun n => (f n : H)) := by
    rw [Metric.cauchySeq_iff] at hcauchyG ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchyG ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    exact lt_of_le_of_lt (est m n).1 h1
  have hcT : CauchySeq (fun n => T (f n)) := by
    rw [Metric.cauchySeq_iff] at hcauchyG ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hcauchyG ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    exact lt_of_le_of_lt (est m n).2 h1
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcf
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcT
  have hgz : g = z + Complex.I • v := tendsto_nhds_unique hGconv (hz.add (hv.const_smul Complex.I))
  have hadj := LinearPMap.adjoint_isFormalAdjoint hd
  have hTu : (T.adjoint u : H) = z + Complex.I • v - Complex.I • (u : H) := by
    rw [← hgz, hgdef]
    abel
  have hvz : ∀ x : T.domain, inner ℂ v (T x) = inner ℂ z ((x : H)) := by
    intro x
    have l1 : Tendsto (fun n => inner ℂ ((f n : H)) (T x)) atTop (𝓝 (inner ℂ v (T x))) :=
      hv.inner tendsto_const_nhds
    have l2 : Tendsto (fun n => inner ℂ (T (f n)) ((x : H))) atTop (𝓝 (inner ℂ z ((x : H)))) :=
      hz.inner tendsto_const_nhds
    have hrw : ∀ n, inner ℂ ((f n : H)) (T x) = inner ℂ (T (f n)) ((x : H)) :=
      fun n => (hsymm (f n) x).symm
    simp_rw [hrw] at l1
    exact tendsto_nhds_unique l1 l2
  have huv : (u : H) - v = 0 := by
    refine eq_zero_of_dense_inner hminus ?_
    rintro y ⟨x, rfl⟩
    show inner ℂ ((u : H) - v) (T x - Complex.I • (x : H)) = 0
    have e1 : inner ℂ ((u : H)) (T x) = inner ℂ (z + Complex.I • v - Complex.I • (u : H))
        ((x : H)) := by rw [← hTu]; exact (hadj u x).symm
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right,
      e1, hvz x]
    simp only [inner_sub_left, inner_add_left, inner_smul_left, Complex.conj_I]
    ring
  have hvu : v = (u : H) := (sub_eq_zero.mp huv).symm
  subst hvu
  have hzz : (T.adjoint u : H) = z := by rw [hTu]; abel
  exact ⟨f, hv, by rw [hzz]; exact hz⟩

/-- **Basic criterion for essential self-adjointness**: a densely defined symmetric operator whose
deficiency ranges `range (T + i)` and `range (T - i)` are dense has self-adjoint adjoint, i.e. it
is essentially self-adjoint. -/
theorem isSelfAdjoint_adjoint_of_dense_deficiency_ranges {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (hsymm : T.IsFormalAdjoint T)
    (hplus : Dense (Set.range fun x : T.domain => T x + Complex.I • (x : H)))
    (hminus : Dense (Set.range fun x : T.domain => T x - Complex.I • (x : H))) :
    IsSelfAdjoint T.adjoint := by
  have hle : T ≤ T.adjoint := hsymm.le_adjoint hd
  have hd' : Dense (T.adjoint.domain : Set H) := hd.mono (by exact_mod_cast hle.1)
  have hadj := LinearPMap.adjoint_isFormalAdjoint hd
  have hsymm' : T.adjoint.IsFormalAdjoint T.adjoint := by
    intro x y
    obtain ⟨f, hf1, hf2⟩ := exists_tendsto_of_mem_adjoint_domain hd hsymm hplus hminus x
    have l1 : Tendsto (fun n => inner ℂ (T (f n)) ((y : H))) atTop
        (𝓝 (inner ℂ (T.adjoint x) ((y : H)))) := hf2.inner tendsto_const_nhds
    have l2 : Tendsto (fun n => inner ℂ ((f n : H)) (T.adjoint y)) atTop
        (𝓝 (inner ℂ ((x : H)) (T.adjoint y))) := hf1.inner tendsto_const_nhds
    have hrw : ∀ n, inner ℂ (T (f n)) ((y : H)) = inner ℂ ((f n : H)) (T.adjoint y) := by
      intro n
      rw [← inner_conj_symm (T (f n)) ((y : H)), ← hadj y (f n)]
      exact inner_conj_symm _ _
    simp_rw [hrw] at l1
    exact tendsto_nhds_unique l1 l2
  have h1 : T.adjoint ≤ T.adjoint.adjoint := hsymm'.le_adjoint hd'
  have h2 : T.adjoint.adjoint ≤ T.adjoint := by
    refine LinearPMap.IsFormalAdjoint.le_adjoint (T := T) hd ?_
    intro x y
    have hadj2 := LinearPMap.adjoint_isFormalAdjoint hd'
    have hx : (x : H) ∈ T.adjoint.domain := hle.1 x.2
    have hTx : T x = T.adjoint ⟨(x : H), hx⟩ := hle.2 rfl
    calc inner ℂ (T x) ((y : H)) = inner ℂ (T.adjoint ⟨(x : H), hx⟩) ((y : H)) := by rw [hTx]
      _ = (starRingEnd ℂ) (inner ℂ ((y : H)) (T.adjoint ⟨(x : H), hx⟩)) :=
          (inner_conj_symm _ _).symm
      _ = (starRingEnd ℂ) (inner ℂ (T.adjoint.adjoint y) ((x : H))) := by rw [hadj2 y ⟨(x : H), hx⟩]
      _ = inner ℂ ((x : H)) (T.adjoint.adjoint y) := inner_conj_symm _ _
  exact LinearPMap.isSelfAdjoint_def.2 (le_antisymm h2 h1)

end Abstract

/-! ## The free Laplacian on Schwartz functions -/

section FreeLaplacian

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The canonical inclusion of the Schwartz space into `L²`. -/
def schwartzToL2 : 𝓢(E, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure E)).toLinearMap

theorem schwartzToL2_injective : Function.Injective (schwartzToL2 E) :=
  SchwartzMap.injective_toLp 2 (volume : Measure E)

theorem schwartzToL2_apply (f : 𝓢(E, ℂ)) : schwartzToL2 E f = f.toLp 2 (volume : Measure E) := rfl

/-- The **free Laplacian** `-Δ` as an unbounded operator on `L²(E)` with domain the (image of the)
Schwartz space. -/
def freeLaplacianOp : Lp ℂ 2 (volume : Measure E) →ₗ.[ℂ] Lp ℂ 2 (volume : Measure E) where
  domain := LinearMap.range (schwartzToL2 E)
  toFun := (schwartzToL2 E ∘ₗ (-(laplacianCLM ℂ E 𝓢(E, ℂ)) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ)).toLinearMap) ∘ₗ
    (LinearEquiv.ofInjective (schwartzToL2 E) (schwartzToL2_injective E)).symm.toLinearMap

variable {E}

theorem freeLaplacianOp_apply (f : 𝓢(E, ℂ)) (h : schwartzToL2 E f ∈ (freeLaplacianOp E).domain) :
    freeLaplacianOp E ⟨schwartzToL2 E f, h⟩ = schwartzToL2 E (-Δ f) := by
  show (schwartzToL2 E ∘ₗ (-(laplacianCLM ℂ E 𝓢(E, ℂ)) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ)).toLinearMap)
      ((LinearEquiv.ofInjective (schwartzToL2 E) (schwartzToL2_injective E)).symm
        ⟨schwartzToL2 E f, h⟩) = _
  rw [show (LinearEquiv.ofInjective (schwartzToL2 E) (schwartzToL2_injective E)).symm
        ⟨schwartzToL2 E f, h⟩ = f from (LinearEquiv.symm_apply_eq _).2 (Subtype.ext rfl)]
  simp

theorem mem_freeLaplacianOp_domain (f : 𝓢(E, ℂ)) :
    schwartzToL2 E f ∈ (freeLaplacianOp E).domain := ⟨f, rfl⟩

/-! ### The Fourier transform turns `-Δ` into multiplication by `4π²‖ξ‖²` -/

theorem fourier_lineDeriv_apply (f : 𝓢(E, ℂ)) (m : E) (ξ : E) :
    𝓕 (∂_{m} f) ξ = (2 * π * Complex.I) * (inner ℝ ξ m : ℝ) * 𝓕 f ξ := by
  have hg : (fun x : E => (inner ℝ x m : ℝ)).HasTemperateGrowth := by fun_prop
  rw [fourier_lineDerivOp_eq f m]
  simp [smulLeftCLM_apply_apply hg]
  ring

theorem fourier_laplacian_apply (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (Δ f) ξ = (-(4 * π ^ 2 * ‖ξ‖ ^ 2) : ℝ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ E with hb
  rw [laplacian_eq_sum b f,
    show (𝓕 (∑ i, ∂_{b i} (∂_{b i} f)) : 𝓢(E, ℂ)) = ∑ i, 𝓕 (∂_{b i} (∂_{b i} f)) from
      map_sum (fourierTransformCLM (𝕜 := ℂ) (V := E) (E := ℂ)) _ _]
  rw [SchwartzMap.sum_apply]
  have key : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ
      = (-(4 * π ^ 2 * (inner ℝ ξ (b i) : ℝ) ^ 2) : ℝ) * 𝓕 f ξ := by
    intro i
    rw [fourier_lineDeriv_apply, fourier_lineDeriv_apply]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  simp only [key, ← Finset.sum_mul]
  congr 1
  rw [← Complex.ofReal_sum]
  congr 1
  have hsum : ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := b.sum_sq_inner_left ξ
  rw [show ∑ i, -(4 * π ^ 2 * (inner ℝ ξ (b i) : ℝ) ^ 2)
      = -(4 * π ^ 2 * ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2) by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib], hsum]

theorem fourier_freeLaplacian_apply (f : 𝓢(E, ℂ)) (ξ : E) :
    𝓕 (-Δ f) ξ = ((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) * 𝓕 f ξ := by
  rw [FourierTransform.fourier_neg]
  simp [fourier_laplacian_apply f ξ]

/-! ### Symmetry -/

theorem freeLaplacian_symmetric (f g : 𝓢(E, ℂ)) :
    inner ℂ (schwartzToL2 E (-Δ f)) (schwartzToL2 E g)
      = inner ℂ (schwartzToL2 E f) (schwartzToL2 E (-Δ g)) := by
  show inner ℂ ((-Δ f).toLp 2 (volume : Measure E)) (g.toLp 2 (volume : Measure E))
      = inner ℂ (f.toLp 2 (volume : Measure E)) ((-Δ g).toLp 2 (volume : Measure E))
  rw [SchwartzMap.inner_toL2_toL2_eq (-Δ f) g (volume : Measure E),
    SchwartzMap.inner_toL2_toL2_eq f (-Δ g) (volume : Measure E),
    ← SchwartzMap.integral_inner_fourier_fourier (-Δ f) g,
    ← SchwartzMap.integral_inner_fourier_fourier f (-Δ g)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  dsimp only
  rw [fourier_freeLaplacian_apply, fourier_freeLaplacian_apply]
  simp [RCLike.inner_apply, map_ofNat]
  ring

/-! ### Approximation lemmas in `L²` -/

theorem norm_schwartzToL2 (f : 𝓢(E, ℂ)) :
    ‖schwartzToL2 E f‖ = (eLpNorm (⇑f) 2 (volume : Measure E)).toReal := SchwartzMap.norm_toLp

/-- The inverse Fourier transform is an isometry for the `L²` norm on Schwartz functions. -/
theorem norm_schwartzToL2_fourierInv (h : 𝓢(E, ℂ)) :
    ‖schwartzToL2 E (𝓕⁻ h)‖ = ‖schwartzToL2 E h‖ := by
  have h1 := SchwartzMap.norm_fourier_toL2_eq (𝓕⁻ h : 𝓢(E, ℂ))
  rw [FourierTransform.fourier_fourierInv_eq] at h1
  exact h1.symm

/-- A Schwartz function can be approximated in `L²` by smooth compactly supported functions. -/
theorem exists_compactSupport_approx (h : 𝓢(E, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (w : E → ℂ) (hcs : HasCompactSupport w) (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w),
      ‖schwartzToL2 E (hcs.toSchwartzMap hsm) - schwartzToL2 E h‖ ≤ ε := by
  obtain ⟨w, hcs, hsm, hle⟩ := MeasureTheory.MemLp.exist_eLpNorm_sub_le (p := 2) (μ := volume)
    (by simp) (by norm_num) (h.memLp 2 (volume : Measure E)) hε
  refine ⟨w, hcs, hsm, ?_⟩
  rw [← map_sub, norm_schwartzToL2]
  have hfun : ⇑((hcs.toSchwartzMap hsm) - h) = w - ⇑h := rfl
  rw [hfun, eLpNorm_sub_comm]
  exact ENNReal.toReal_le_of_le_ofReal hε.le hle

/-- Schwartz functions are dense in `L²`. -/
theorem exists_schwartz_approx (u : Lp ℂ 2 (volume : Measure E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : 𝓢(E, ℂ), ‖schwartzToL2 E g - u‖ < ε := by
  have hdr : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure E)) :=
    SchwartzMap.denseRange_toLpCLM (by simp)
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 (hdr u) ε hε
  obtain ⟨g, hg⟩ := hy
  refine ⟨g, ?_⟩
  rw [← hg, dist_comm, dist_eq_norm] at hdist
  exact hdist

/-! ### Density of the deficiency ranges -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Dividing a smooth compactly supported function by `4π²‖ξ‖² + z`, for non-real `z`, yields
a smooth compactly supported function, hence a Schwartz function. -/
theorem exists_schwartz_div (w : E → ℂ) (hcs : HasCompactSupport w)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) (z : ℂ) (hz : z.im ≠ 0) :
    ∃ Φ : 𝓢(E, ℂ), ∀ ξ, (((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + z) * Φ ξ = w ξ := by
  set den : E → ℂ := fun ξ => ((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + z with hden
  have hne : ∀ ξ, den ξ ≠ 0 := by
    intro ξ h
    apply hz
    have h1 := congrArg Complex.im h
    simp only [hden, Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] at h1
    exact h1
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ξ : E => (4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  have hdensm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) den :=
    (Complex.ofRealCLM.contDiff.comp h1).add contDiff_const
  set φ : E → ℂ := fun ξ => w ξ * (den ξ)⁻¹ with hφ
  have hφsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ := hsm.mul (hdensm.inv hne)
  have hφcs : HasCompactSupport φ := hcs.mono (by
    intro x hx
    simp only [hφ, Function.mem_support, ne_eq, mul_eq_zero, not_or] at hx
    exact hx.1)
  refine ⟨hφcs.toSchwartzMap hφsm, fun ξ => ?_⟩
  show den ξ * (w ξ * (den ξ)⁻¹) = w ξ
  rw [mul_comm (w ξ), ← mul_assoc, mul_inv_cancel₀ (hne ξ), one_mul]

theorem schwartz_fourier_injective :
    Function.Injective (fun f : 𝓢(E, ℂ) => (𝓕 f : 𝓢(E, ℂ))) := by
  intro a b hab
  simp only at hab
  rw [← FourierTransform.fourierInv_fourier_eq (F := 𝓢(E, ℂ)) a, hab,
    FourierTransform.fourierInv_fourier_eq]

/-- Solving `(-Δ + z) f = 𝓕⁻ ψ` on the Fourier side. -/
theorem freeLaplacian_add_smul_fourierInv (Φ ψ : 𝓢(E, ℂ)) (z : ℂ)
    (h : ∀ ξ, (((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + z) * Φ ξ = ψ ξ) :
    -Δ (𝓕⁻ Φ) + z • (𝓕⁻ Φ : 𝓢(E, ℂ)) = 𝓕⁻ ψ := by
  apply schwartz_fourier_injective
  simp only
  ext ξ
  rw [FourierTransform.fourier_add, FourierTransform.fourier_smul, SchwartzMap.add_apply,
    SchwartzMap.smul_apply, fourier_freeLaplacian_apply, FourierTransform.fourier_fourierInv_eq,
    FourierTransform.fourier_fourierInv_eq, smul_eq_mul, ← h ξ]
  ring

/-- The deficiency ranges of the free Laplacian are dense: for every non-real `z` the set
`{(-Δ + z) f : f Schwartz}` is dense in `L²`. -/
theorem dense_range_freeLaplacian_add (z : ℂ) (hz : z.im ≠ 0) :
    Dense (Set.range fun f : 𝓢(E, ℂ) => schwartzToL2 E (-Δ f + z • f)) := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨g, hg⟩ := exists_schwartz_approx u (half_pos hε)
  obtain ⟨w, hcs, hsm, hw⟩ := exists_compactSupport_approx (𝓕 g : 𝓢(E, ℂ))
    (half_pos (half_pos hε))
  set ψ : 𝓢(E, ℂ) := hcs.toSchwartzMap hsm with hψ
  obtain ⟨Φ, hΦ⟩ := exists_schwartz_div w hcs hsm z hz
  refine ⟨schwartzToL2 E (-Δ (𝓕⁻ Φ) + z • (𝓕⁻ Φ : 𝓢(E, ℂ))), ⟨𝓕⁻ Φ, rfl⟩, ?_⟩
  rw [freeLaplacian_add_smul_fourierInv Φ ψ z (fun ξ => hΦ ξ)]
  have key : ‖schwartzToL2 E (𝓕⁻ ψ) - schwartzToL2 E g‖
      = ‖schwartzToL2 E ψ - schwartzToL2 E (𝓕 g)‖ := by
    rw [← map_sub, ← map_sub]
    have hsub : (𝓕⁻ ψ : 𝓢(E, ℂ)) - g = 𝓕⁻ (ψ - 𝓕 g) := by
      have h2 : (𝓕⁻ (ψ - 𝓕 g) : 𝓢(E, ℂ)) = 𝓕⁻ ψ - 𝓕⁻ (𝓕 g : 𝓢(E, ℂ)) := by
        simp [sub_eq_add_neg]
      rw [h2, FourierTransform.fourierInv_fourier_eq]
    rw [hsub]
    exact norm_schwartzToL2_fourierInv _
  rw [dist_comm, dist_eq_norm]
  calc ‖schwartzToL2 E (𝓕⁻ ψ) - u‖
      ≤ ‖schwartzToL2 E (𝓕⁻ ψ) - schwartzToL2 E g‖ + ‖schwartzToL2 E g - u‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by rw [key]; linarith [hw, hg]

/-! ### Essential self-adjointness -/

variable (E)

theorem dense_freeLaplacianOp_domain :
    Dense (((freeLaplacianOp E).domain : Submodule ℂ (Lp ℂ 2 (volume : Measure E)))
      : Set (Lp ℂ 2 (volume : Measure E))) := by
  have hdr : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure E)) :=
    SchwartzMap.denseRange_toLpCLM (by simp)
  have hset : (((freeLaplacianOp E).domain : Submodule ℂ (Lp ℂ 2 (volume : Measure E)))
      : Set (Lp ℂ 2 (volume : Measure E))) = Set.range (schwartzToL2 E) := LinearMap.coe_range _
  rw [hset]
  exact hdr

theorem freeLaplacianOp_isFormalAdjoint :
    (freeLaplacianOp E).IsFormalAdjoint (freeLaplacianOp E) := by
  intro x y
  obtain ⟨f, hf⟩ := x.2
  obtain ⟨g, hgg⟩ := y.2
  have hx : x = ⟨schwartzToL2 E f, mem_freeLaplacianOp_domain f⟩ := Subtype.ext hf.symm
  have hy : y = ⟨schwartzToL2 E g, mem_freeLaplacianOp_domain g⟩ := Subtype.ext hgg.symm
  rw [hx, hy, freeLaplacianOp_apply, freeLaplacianOp_apply]
  exact freeLaplacian_symmetric f g

theorem range_freeLaplacianOp_add (z : ℂ) :
    (Set.range fun x : (freeLaplacianOp E).domain =>
        freeLaplacianOp E x + z • (x : Lp ℂ 2 (volume : Measure E)))
      = Set.range (fun f : 𝓢(E, ℂ) => schwartzToL2 E (-Δ f + z • f)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨f, hf⟩ := x.2
    have hx : x = ⟨schwartzToL2 E f, mem_freeLaplacianOp_domain f⟩ := Subtype.ext hf.symm
    refine ⟨f, ?_⟩
    dsimp only
    rw [hx, freeLaplacianOp_apply]
    simp
  · rintro ⟨f, rfl⟩
    refine ⟨⟨schwartzToL2 E f, mem_freeLaplacianOp_domain f⟩, ?_⟩
    dsimp only
    rw [freeLaplacianOp_apply]
    simp

/-- **The free Laplacian is essentially self-adjoint on the Schwartz space.**

The operator `freeLaplacianOp E` is `-Δ` acting in `L²(E)` with domain the Schwartz functions,
where `E` is any finite-dimensional real inner product space.  Essential self-adjointness is
expressed as self-adjointness of the adjoint (equivalently: the closure of the operator is
self-adjoint, i.e. the operator has a unique self-adjoint extension).  The proof goes through the
Fourier transform, which turns `-Δ` into multiplication by `4π²‖ξ‖²`. -/
theorem freeLaplacian_essentiallySelfAdjoint_of_fourier :
    IsSelfAdjoint (freeLaplacianOp E).adjoint := by
  refine isSelfAdjoint_adjoint_of_dense_deficiency_ranges (dense_freeLaplacianOp_domain E)
    (freeLaplacianOp_isFormalAdjoint E) ?_ ?_
  · rw [range_freeLaplacianOp_add E Complex.I]
    exact dense_range_freeLaplacian_add Complex.I (by simp)
  · have hrw : (Set.range fun x : (freeLaplacianOp E).domain =>
        freeLaplacianOp E x - Complex.I • (x : Lp ℂ 2 (volume : Measure E)))
        = Set.range fun x : (freeLaplacianOp E).domain =>
          freeLaplacianOp E x + (-Complex.I) • (x : Lp ℂ 2 (volume : Measure E)) := by
      simp [sub_eq_add_neg]
    rw [hrw, range_freeLaplacianOp_add E (-Complex.I)]
    exact dense_range_freeLaplacian_add (-Complex.I) (by simp)

end FreeLaplacian

end Brockian.Weyl.FreeLaplacian2

