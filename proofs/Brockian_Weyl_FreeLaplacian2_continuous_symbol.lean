import Brockian.Weyl.FreeLaplacian2

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
Essential self-adjointness of the free Laplacian on `L²(ℝᵈ)`, via the Fourier transform.
-/
import Mathlib

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real Function LineDeriv
open scoped FourierTransform ComplexInnerProductSpace Laplacian LinearPMap ContDiff

noncomputable section

variable (d : ℕ)

/-- The configuration space `ℝᵈ`. -/
abbrev EuclSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝᵈ, ℂ)`. -/
abbrev L2 (d : ℕ) := Lp (α := EuclSpace d) ℂ 2

/-- The symbol of the free Laplacian: `-Δ` acts on the Fourier side as multiplication by
`4π²‖ξ‖²`. -/
def symbol (ξ : EuclSpace d) : ℝ := 4 * π ^ 2 * ‖ξ‖ ^ 2

variable {d}

theorem continuous_symbol : Continuous (symbol d) := by
  unfold symbol; fun_prop

theorem hasTemperateGrowth_symbol :
    Function.HasTemperateGrowth (fun ξ : EuclSpace d ↦ ((symbol d ξ : ℝ) : ℂ)) := by
  unfold symbol; fun_prop

variable (d)

/-- Multiplication by the symbol `4π²‖ξ‖²`, as an operator on Schwartz space. -/
def mulSymbolCLM : 𝓢(EuclSpace d, ℂ) →L[ℂ] 𝓢(EuclSpace d, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun ξ ↦ ((symbol d ξ : ℝ) : ℂ))

variable {d}

@[simp]
theorem mulSymbolCLM_apply (ψ : 𝓢(EuclSpace d, ℂ)) (ξ : EuclSpace d) :
    mulSymbolCLM d ψ ξ = ((symbol d ξ : ℝ) : ℂ) * ψ ξ := by
  simp [mulSymbolCLM, smulLeftCLM_apply_apply hasTemperateGrowth_symbol]

variable (d)

/-- The negative Laplacian `-Δ` acting on Schwartz functions. -/
def negLaplacianCLM : 𝓢(EuclSpace d, ℂ) →L[ℂ] 𝓢(EuclSpace d, ℂ) :=
  -laplacianCLM ℂ (EuclSpace d) 𝓢(EuclSpace d, ℂ)

variable {d}

@[simp]
theorem negLaplacianCLM_apply (φ : 𝓢(EuclSpace d, ℂ)) : negLaplacianCLM d φ = -Δ φ := by
  simp [negLaplacianCLM]

/-- The Fourier transform of a second directional derivative in direction `m` is multiplication
by `-(2π⟪ξ, m⟫)²`. -/
theorem fourier_lineDerivOp_sq_apply (φ : 𝓢(EuclSpace d, ℂ)) (m x : EuclSpace d) :
    (𝓕 (∂_{m} (∂_{m} φ)) : 𝓢(EuclSpace d, ℂ)) x
      = -(4 * (π : ℂ) ^ 2 * ((inner ℝ x m : ℝ) : ℂ) ^ 2) * (𝓕 φ : 𝓢(EuclSpace d, ℂ)) x := by
  have hg : Function.HasTemperateGrowth (fun x : EuclSpace d ↦ (inner ℝ x m : ℝ)) :=
    Function.hasTemperateGrowth_inner_left m
  rw [SchwartzMap.fourier_lineDerivOp_eq, SchwartzMap.fourier_lineDerivOp_eq]
  simp only [SchwartzMap.smul_apply, smulLeftCLM_apply_apply hg, Complex.real_smul, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  ring

variable (d)

/-- The Fourier transform intertwines `-Δ` on Schwartz space with multiplication by the
symbol `4π²‖ξ‖²`. -/
theorem fourier_negLaplacianCLM (φ : 𝓢(EuclSpace d, ℂ)) :
    𝓕 (negLaplacianCLM d φ) = mulSymbolCLM d (𝓕 φ) := by
  set b := stdOrthonormalBasis ℝ (EuclSpace d)
  have h1 : negLaplacianCLM d φ = -∑ i, ∂_{b i} (∂_{b i} φ) := by
    rw [negLaplacianCLM_apply, SchwartzMap.laplacian_eq_sum b φ]
  rw [h1, FourierTransform.fourier_neg, FourierTransform.fourier_sum]
  ext ξ
  simp only [SchwartzMap.neg_apply, SchwartzMap.sum_apply, mulSymbolCLM_apply,
    fourier_lineDerivOp_sq_apply]
  have hsum : ∑ i, ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2 = ((‖ξ‖ : ℝ) : ℂ) ^ 2 := by
    have hb2 := OrthonormalBasis.sum_sq_inner_left b ξ
    have h2 : ((∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 : ℝ) : ℂ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) := by rw [hb2]
    push_cast at h2
    exact h2
  rw [symbol]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib, neg_neg, ← Finset.sum_mul, ← Finset.mul_sum, hsum]

/-- The image of Schwartz space inside `L²(ℝᵈ)`; this is the domain of the free Laplacian. -/
def schwartzSubmodule : Submodule ℂ (L2 d) :=
  LinearMap.range ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclSpace d)))
    : 𝓢(EuclSpace d, ℂ) →ₗ[ℂ] L2 d)

/-- Schwartz space is linearly equivalent to its image in `L²`. -/
def schwartzEquiv : 𝓢(EuclSpace d, ℂ) ≃ₗ[ℂ] (schwartzSubmodule d) :=
  LinearEquiv.ofInjective
    ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclSpace d)))
      : 𝓢(EuclSpace d, ℂ) →ₗ[ℂ] L2 d)
    (SchwartzMap.injective_toLp 2 (volume : Measure (EuclSpace d)))

/-- The free Laplacian `-Δ` on `L²(ℝᵈ)`, as an unbounded operator with domain the Schwartz
functions. -/
def freeLaplacian : L2 d →ₗ.[ℂ] L2 d where
  domain := schwartzSubmodule d
  toFun :=
    (((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclSpace d)))
        : 𝓢(EuclSpace d, ℂ) →ₗ[ℂ] L2 d).comp (negLaplacianCLM d).toLinearMap).comp
      (schwartzEquiv d).symm.toLinearMap

theorem dense_domain_freeLaplacian :
    Dense (((freeLaplacian d).domain : Submodule ℂ (L2 d)) : Set (L2 d)) := by
  have hd := SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := EuclSpace d) (p := 2)
    (by simp) (μ := (volume : Measure (EuclSpace d)))
  have h2 : (((freeLaplacian d).domain : Submodule ℂ (L2 d)) : Set (L2 d)) =
      Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (EuclSpace d))) := by
    simp [freeLaplacian, schwartzSubmodule, LinearMap.coe_range]
    rfl
  rw [h2]
  exact hd

variable {d}

theorem toLp_mem_domain (φ : 𝓢(EuclSpace d, ℂ)) :
    (φ.toLp 2 (volume : Measure (EuclSpace d))) ∈ (freeLaplacian d).domain :=
  ⟨φ, rfl⟩

theorem freeLaplacian_apply_toLp (φ : 𝓢(EuclSpace d, ℂ)) :
    (freeLaplacian d) ⟨φ.toLp 2 volume, toLp_mem_domain φ⟩ =
      (negLaplacianCLM d φ).toLp 2 volume := by
  have h : (schwartzEquiv d).symm ⟨φ.toLp 2 volume, toLp_mem_domain φ⟩ = φ := by
    apply (schwartzEquiv d).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  show ((SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclSpace d)))
      ((negLaplacianCLM d) ((schwartzEquiv d).symm ⟨φ.toLp 2 volume, toLp_mem_domain φ⟩))) = _
  rw [h]
  rfl

/-- Every element of the domain of the free Laplacian comes from a Schwartz function. -/
theorem exists_schwartz_of_mem_domain (x : ((freeLaplacian d).domain)) :
    ∃ φ : 𝓢(EuclSpace d, ℂ), x = ⟨φ.toLp 2 volume, toLp_mem_domain φ⟩ := by
  obtain ⟨φ, hφ⟩ := x.2
  exact ⟨φ, Subtype.ext hφ.symm⟩

/-! ### The key "weak equals strong" lemma -/

/-- If `w` and `y` in `L²` satisfy `⟪w, ψ⟫ = ⟪y, symbol * ψ⟫` for every Schwartz function `ψ`,
then `symbol * y = w` almost everywhere. -/
theorem ae_symbol_mul_eq (y w : L2 d)
    (h : ∀ ψ : 𝓢(EuclSpace d, ℂ),
      (inner ℂ w (ψ.toLp 2 volume) : ℂ) = inner ℂ y ((mulSymbolCLM d ψ).toLp 2 volume)) :
    (fun ξ ↦ ((symbol d ξ : ℝ) : ℂ) * y ξ) =ᵐ[volume] (w : EuclSpace d → ℂ) := by
  have hyloc : LocallyIntegrable (y : EuclSpace d → ℂ) volume :=
    (MeasureTheory.Lp.memLp y).locallyIntegrable (by norm_num)
  have hwloc : LocallyIntegrable (w : EuclSpace d → ℂ) volume :=
    (MeasureTheory.Lp.memLp w).locallyIntegrable (by norm_num)
  have hmyloc : LocallyIntegrable (fun ξ ↦ ((symbol d ξ : ℝ) : ℂ) * y ξ) volume := by
    rw [← locallyIntegrableOn_univ] at hyloc ⊢
    have := hyloc.continuousOn_smul (𝕜 := ℂ) (g := fun ξ ↦ ((symbol d ξ : ℝ) : ℂ))
      isOpen_univ.isLocallyClosed
      (Continuous.continuousOn (Complex.continuous_ofReal.comp continuous_symbol))
    simpa [smul_eq_mul] using this
  refine ae_eq_of_integral_contDiff_smul_eq hmyloc hwloc ?_
  intro g hg hgsupp
  have hgC : ContDiff ℝ ∞ (fun x : EuclSpace d ↦ ((g x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hg
  have hgCsupp : HasCompactSupport (fun x : EuclSpace d ↦ ((g x : ℝ) : ℂ)) :=
    hgsupp.comp_left (g := ((↑·) : ℝ → ℂ)) Complex.ofReal_zero
  set ψ : 𝓢(EuclSpace d, ℂ) := hgCsupp.toSchwartzMap hgC
  have hψval : ∀ x, ψ x = ((g x : ℝ) : ℂ) := fun x ↦ rfl
  have hψae : ((ψ.toLp 2 (volume : Measure (EuclSpace d)) : L2 d) : EuclSpace d → ℂ)
      =ᵐ[volume] (ψ : EuclSpace d → ℂ) := ψ.coeFn_toLp 2 volume
  have hmψae : (((mulSymbolCLM d ψ).toLp 2 (volume : Measure (EuclSpace d)) : L2 d)
      : EuclSpace d → ℂ) =ᵐ[volume] ((mulSymbolCLM d ψ) : EuclSpace d → ℂ) :=
    (mulSymbolCLM d ψ).coeFn_toLp 2 volume
  have e1 : (inner ℂ w (ψ.toLp 2 (volume : Measure (EuclSpace d))) : ℂ)
      = ∫ ξ, (starRingEnd ℂ) (w ξ) * ((g ξ : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hψae] with ξ hξ
    rw [RCLike.inner_apply', hξ, hψval]
  have e2 : (inner ℂ y ((mulSymbolCLM d ψ).toLp 2 (volume : Measure (EuclSpace d))) : ℂ)
      = ∫ ξ, (starRingEnd ℂ) (((symbol d ξ : ℝ) : ℂ) * y ξ) * ((g ξ : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmψae] with ξ hξ
    rw [RCLike.inner_apply', hξ, mulSymbolCLM_apply, hψval]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have key := h ψ
  rw [e1, e2] at key
  have key' := congrArg (starRingEnd ℂ) key
  rw [← integral_conj, ← integral_conj] at key'
  simp only [map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply,
    Complex.conj_ofReal] at key'
  simp only [Complex.real_smul]
  have g1 : ∫ x, ((g x : ℝ) : ℂ) * (((symbol d x : ℝ) : ℂ) * y x)
      = ∫ x, ((symbol d x : ℝ) : ℂ) * y x * ((g x : ℝ) : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ by ring)
  have g2 : ∫ x, ((g x : ℝ) : ℂ) * (w : EuclSpace d → ℂ) x
      = ∫ x, (w : EuclSpace d → ℂ) x * ((g x : ℝ) : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun ξ ↦ by ring)
  rw [g1, g2, key']

/-! ### Symmetry -/

theorem freeLaplacian_isFormalAdjoint_self :
    (freeLaplacian d).IsFormalAdjoint (freeLaplacian d) := by
  intro x y
  obtain ⟨φ, rfl⟩ := exists_schwartz_of_mem_domain x
  obtain ⟨ψ, rfl⟩ := exists_schwartz_of_mem_domain y
  rw [freeLaplacian_apply_toLp, freeLaplacian_apply_toLp]
  simp only [SchwartzMap.inner_toL2_toL2_eq, negLaplacianCLM_apply, RCLike.inner_apply']
  have hIBP := SchwartzMap.integral_bilinear_laplacian_right_eq_left
    (μ := (volume : Measure (EuclSpace d))) φ ψ
    ((ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, ContinuousLinearMap.mul_apply'] at hIBP
  simp only [SchwartzMap.neg_apply, map_neg, neg_mul, mul_neg, integral_neg]
  rw [hIBP]

/-! ### The adjoint -/

/-- The Fourier transform of an element of the domain of the adjoint gets multiplied by the
symbol. -/
theorem fourier_adjoint_apply
    (hfourier : ∀ φ : 𝓢(EuclSpace d, ℂ), 𝓕 (negLaplacianCLM d φ) = mulSymbolCLM d (𝓕 φ))
    (x : ((freeLaplacian d)†).domain) :
    (fun ξ ↦ ((symbol d ξ : ℝ) : ℂ) * (𝓕 (x : L2 d) : L2 d) ξ)
      =ᵐ[volume] ((𝓕 ((freeLaplacian d)† x) : L2 d) : EuclSpace d → ℂ) := by
  refine ae_symbol_mul_eq (𝓕 (x : L2 d)) (𝓕 ((freeLaplacian d)† x)) ?_
  intro ψ
  have hdense : Dense (((freeLaplacian d).domain : Submodule ℂ (L2 d)) : Set (L2 d)) :=
    dense_domain_freeLaplacian d
  set φ : 𝓢(EuclSpace d, ℂ) := 𝓕⁻ ψ
  have hφ : 𝓕 φ = ψ := FourierTransform.fourier_fourierInv_eq ψ
  have e1 : (ψ.toLp 2 (volume : Measure (EuclSpace d)) : L2 d)
      = 𝓕 (φ.toLp 2 (volume : Measure (EuclSpace d))) := by
    rw [SchwartzMap.toLp_fourier_eq, hφ]
  have e2 : ((mulSymbolCLM d ψ).toLp 2 (volume : Measure (EuclSpace d)) : L2 d)
      = 𝓕 ((negLaplacianCLM d φ).toLp 2 (volume : Measure (EuclSpace d))) := by
    rw [SchwartzMap.toLp_fourier_eq, hfourier φ, hφ]
  rw [e1, e2, MeasureTheory.Lp.inner_fourier_eq, MeasureTheory.Lp.inner_fourier_eq]
  have hFA := LinearPMap.adjoint_isFormalAdjoint (T := freeLaplacian d) hdense x
    ⟨φ.toLp 2 volume, toLp_mem_domain φ⟩
  rw [hFA, freeLaplacian_apply_toLp]

theorem adjoint_isFormalAdjoint_self
    (hfourier : ∀ φ : 𝓢(EuclSpace d, ℂ), 𝓕 (negLaplacianCLM d φ) = mulSymbolCLM d (𝓕 φ)) :
    ((freeLaplacian d)†).IsFormalAdjoint ((freeLaplacian d)†) := by
  intro x y
  have hx := fourier_adjoint_apply hfourier x
  have hy := fourier_adjoint_apply hfourier y
  rw [← MeasureTheory.Lp.inner_fourier_eq ((freeLaplacian d)† x) (y : L2 d),
    ← MeasureTheory.Lp.inner_fourier_eq (x : L2 d) ((freeLaplacian d)† y),
    MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hx, hy] with ξ hxξ hyξ
  rw [← hxξ, ← hyξ]
  simp only [RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

/-! ### Essential self-adjointness -/

variable (d)

/-- **The free Laplacian is essentially self-adjoint.**  Conditional version: assuming the
Fourier transform intertwines `-Δ` with multiplication by the symbol `4π²‖ξ‖²` on Schwartz
space, the adjoint of the free Laplacian (with Schwartz domain) is self-adjoint, i.e. the free
Laplacian is essentially self-adjoint. -/
theorem freeLaplacian_essentiallySelfAdjoint_of_fourier
    (hfourier : ∀ φ : 𝓢(EuclSpace d, ℂ), 𝓕 (negLaplacianCLM d φ) = mulSymbolCLM d (𝓕 φ)) :
    IsSelfAdjoint ((freeLaplacian d)†) := by
  have hdense : Dense (((freeLaplacian d).domain : Submodule ℂ (L2 d)) : Set (L2 d)) :=
    dense_domain_freeLaplacian d
  have hsym : (freeLaplacian d) ≤ (freeLaplacian d)† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense freeLaplacian_isFormalAdjoint_self
  have hdense' : Dense ((((freeLaplacian d)†).domain : Submodule ℂ (L2 d)) : Set (L2 d)) :=
    hdense.mono (fun z hz ↦ hsym.1 hz)
  have h1 : (freeLaplacian d)† ≤ ((freeLaplacian d)†)† :=
    LinearPMap.IsFormalAdjoint.le_adjoint hdense' (adjoint_isFormalAdjoint_self hfourier)
  have hFA : ((freeLaplacian d)†).IsFormalAdjoint (((freeLaplacian d)†)†) :=
    (LinearPMap.adjoint_isFormalAdjoint hdense').symm
  have h2 : ((freeLaplacian d)†)† ≤ (freeLaplacian d)† := by
    refine LinearPMap.IsFormalAdjoint.le_adjoint hdense ?_
    intro x y
    have hx : (x : L2 d) ∈ ((freeLaplacian d)†).domain := hsym.1 x.2
    have h := hFA ⟨(x : L2 d), hx⟩ y
    rw [← h]
    congr 1
    exact hsym.2 (x := x) (y := ⟨(x : L2 d), hx⟩) rfl
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm h2 h1

/-- **The free Laplacian is essentially self-adjoint** (unconditional). -/
theorem freeLaplacian_essentiallySelfAdjoint : IsSelfAdjoint ((freeLaplacian d)†) :=
  freeLaplacian_essentiallySelfAdjoint_of_fourier d (fourier_negLaplacianCLM d)

end

end Brockian.Weyl.FreeLaplacian2

