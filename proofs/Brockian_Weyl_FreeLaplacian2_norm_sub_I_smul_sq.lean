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
# Essential self-adjointness of the free Laplacian

This file proves that the free Laplacian `-Δ`, defined on the Schwartz space
`𝓢(ℝ^d, ℂ)` inside `L²(ℝ^d, ℂ)`, is essentially self-adjoint.

## Formalisation of essential self-adjointness

An unbounded operator is modelled here by a pair of linear maps `ι, A : D →ₗ[ℂ] H`
out of an abstract "domain" module `D`: `ι` is the (dense-range) inclusion of the
operator domain into the Hilbert space `H`, and `A` is the operator itself.

* `Brockian.Weyl.FreeLaplacian2.IsAdjointPair ι A u v` says that `(u, v)` belongs to the graph
  of the adjoint operator `A*`, i.e. `⟪v, ι f⟫ = ⟪u, A f⟫` for all `f` in the domain.
* `Brockian.Weyl.FreeLaplacian2.IsEssentiallySelfAdjoint ι A` says that the domain is dense,
  that `A` is symmetric, and that the adjoint `A*` is symmetric.  For a densely defined
  symmetric operator, symmetry of `A*` is the standard characterisation of essential
  self-adjointness (it is equivalent to `A* = A** = closure of A` being self-adjoint).

The abstract criterion `isEssentiallySelfAdjoint_of_dense_ranges` is von Neumann's basic
criterion: a densely defined symmetric operator with `Ran(A + i)` and `Ran(A - i)` dense is
essentially self-adjoint.

## Main results

* `Brockian.Weyl.FreeLaplacian2.fourier_freeLaplacian`: the Fourier transform conjugates the free
  Laplacian into multiplication by the symbol `4 π² ‖ξ‖²`.
* `Brockian.Weyl.FreeLaplacian2.freeLaplacian_essentiallySelfAdjoint_of_fourier`: the free
  Laplacian on `𝓢(ℝ^d, ℂ) ⊆ L²(ℝ^d, ℂ)` is essentially self-adjoint.  The statement is
  unconditional: the Fourier-side input is supplied by `fourier_freeLaplacian`.
-/

namespace Brockian.Weyl.FreeLaplacian2

open MeasureTheory SchwartzMap Real Filter Topology
open scoped FourierTransform ComplexInnerProductSpace SchwartzMap ContDiff

noncomputable section

/-! ## An abstract criterion for essential self-adjointness -/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {D : Type*} [AddCommGroup D] [Module ℂ D]

/-- `IsAdjointPair ι A u v` states that the pair `(u, v)` belongs to the graph of the adjoint
of the operator `A` with domain `ι`, that is, `⟪v, ι f⟫ = ⟪u, A f⟫` for every `f` in the
domain. -/
def IsAdjointPair (ι A : D →ₗ[ℂ] H) (u v : H) : Prop := ∀ f : D, ⟪v, ι f⟫ = ⟪u, A f⟫

/-- Essential self-adjointness of the operator `A` with domain `ι : D →ₗ[ℂ] H`:
the domain is dense, `A` is symmetric, and the adjoint `A*` (whose graph consists of the
pairs satisfying `IsAdjointPair`) is symmetric as well.  For a densely defined symmetric
operator the latter condition is equivalent to the closure of `A` being self-adjoint. -/
structure IsEssentiallySelfAdjoint (ι A : D →ₗ[ℂ] H) : Prop where
  /-- The domain of the operator is dense in the ambient Hilbert space. -/
  dense_domain : Dense (Set.range ι)
  /-- The operator is symmetric. -/
  symmetric : ∀ f g : D, ⟪A f, ι g⟫ = ⟪ι f, A g⟫
  /-- The adjoint operator is symmetric. -/
  adjoint_symmetric : ∀ u₁ v₁ u₂ v₂ : H, IsAdjointPair ι A u₁ v₁ → IsAdjointPair ι A u₂ v₂ →
    ⟪v₁, u₂⟫ = ⟪u₁, v₂⟫

/-- For a symmetric operator, `‖A g - i ι g‖² = ‖A g‖² + ‖ι g‖²`. -/
theorem norm_sub_I_smul_sq (ι A : D →ₗ[ℂ] H) (hsymm : ∀ f g : D, ⟪A f, ι g⟫ = ⟪ι f, A g⟫)
    (g : D) : ‖A g - Complex.I • ι g‖ ^ 2 = ‖A g‖ ^ 2 + ‖ι g‖ ^ 2 := by
  have hreal : (⟪A g, ι g⟫ : ℂ).im = 0 := by
    have h : (starRingEnd ℂ) ⟪A g, ι g⟫ = ⟪A g, ι g⟫ := by
      rw [inner_conj_symm]; exact (hsymm g g).symm
    exact Complex.conj_eq_iff_im.mp h
  rw [norm_sub_sq (𝕜 := ℂ), inner_smul_right]
  simp [hreal, norm_smul]

/-- If `Ran(A + i)` is dense, then the adjoint has no eigenvector with eigenvalue `i`. -/
theorem eq_zero_of_isAdjointPair_smul_I (ι A : D →ₗ[ℂ] H)
    (hd : Dense (Set.range (A + Complex.I • ι))) {x : H}
    (hx : IsAdjointPair ι A x (Complex.I • x)) : x = 0 := by
  have hsub : Set.range (A + Complex.I • ι) ⊆ {y : H | ⟪x, y⟫ = 0} := by
    rintro _ ⟨f, rfl⟩
    have h1 : ⟪Complex.I • x, ι f⟫ = ⟪x, A f⟫ := hx f
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Set.mem_setOf_eq]
    rw [inner_add_right, inner_smul_right, ← h1, inner_smul_left]
    simp
  have hcl : IsClosed {y : H | ⟪x, y⟫ = (0 : ℂ)} :=
    isClosed_eq (innerSL ℂ x).continuous continuous_const
  have huniv : (Set.univ : Set H) ⊆ {y : H | ⟪x, y⟫ = 0} := by
    rw [← hd.closure_eq]; exact hcl.closure_subset_iff.mpr hsub
  exact inner_self_eq_zero.mp (huniv (Set.mem_univ x))

variable [CompleteSpace H]

/-- Under the hypotheses of von Neumann's basic criterion, every point of the graph of the
adjoint is a limit of points of the graph of the operator. -/
theorem exists_seq_tendsto_of_isAdjointPair (ι A : D →ₗ[ℂ] H)
    (hsymm : ∀ f g : D, ⟪A f, ι g⟫ = ⟪ι f, A g⟫)
    (hpos : Dense (Set.range (A + Complex.I • ι)))
    (hneg : Dense (Set.range (A - Complex.I • ι)))
    {u v : H} (huv : IsAdjointPair ι A u v) :
    ∃ f : ℕ → D, Tendsto (fun n => ι (f n)) atTop (𝓝 u) ∧
      Tendsto (fun n => A (f n)) atTop (𝓝 v) := by
  set B : D →ₗ[ℂ] H := A - Complex.I • ι with hB
  set t : H := v - Complex.I • u with ht
  have hchoice : ∀ n : ℕ, ∃ g : D, ‖B g - t‖ < 1 / (n + 1) := by
    intro n
    obtain ⟨y, hy, hlt⟩ := hneg.exists_dist_lt t (show (0 : ℝ) < 1 / (n + 1) by positivity)
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, by rwa [dist_comm, dist_eq_norm] at hlt⟩
  choose f hf using hchoice
  have hBtend : Tendsto (fun n => B (f n)) atTop (𝓝 t) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hf n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hBcauchy : CauchySeq (fun n => B (f n)) := hBtend.cauchySeq
  have hle : ∀ m n : ℕ, ‖A (f m) - A (f n)‖ ≤ ‖B (f m) - B (f n)‖ ∧
      ‖ι (f m) - ι (f n)‖ ≤ ‖B (f m) - B (f n)‖ := by
    intro m n
    have hsubeq : B (f m) - B (f n) = A (f m - f n) - Complex.I • ι (f m - f n) := by
      simp [hB, map_sub, smul_sub]; abel
    have hkey := norm_sub_I_smul_sq ι A hsymm (f m - f n)
    rw [← hsubeq] at hkey
    rw [show ‖A (f m - f n)‖ = ‖A (f m) - A (f n)‖ by rw [map_sub],
      show ‖ι (f m - f n)‖ = ‖ι (f m) - ι (f n)‖ by rw [map_sub]] at hkey
    constructor
    · nlinarith [norm_nonneg (A (f m) - A (f n)), norm_nonneg (ι (f m) - ι (f n)),
        norm_nonneg (B (f m) - B (f n))]
    · nlinarith [norm_nonneg (A (f m) - A (f n)), norm_nonneg (ι (f m) - ι (f n)),
        norm_nonneg (B (f m) - B (f n))]
  have hAcauchy : CauchySeq (fun n => A (f n)) := by
    rw [Metric.cauchySeq_iff] at hBcauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hBcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hle m n).1 (by rw [← dist_eq_norm]; exact hN m hm n hn)
  have hicauchy : CauchySeq (fun n => ι (f n)) := by
    rw [Metric.cauchySeq_iff] at hBcauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hBcauchy ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hle m n).2 (by rw [← dist_eq_norm]; exact hN m hm n hn)
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hAcauchy
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hicauchy
  have hBtend' : Tendsto (fun n => B (f n)) atTop (𝓝 (w - Complex.I • g)) := by
    have hBn : ∀ n, B (f n) = A (f n) - Complex.I • ι (f n) := fun n => by simp [hB]
    simpa [hBn] using hw.sub (hg.const_smul Complex.I)
  have hlim : w - Complex.I • g = v - Complex.I • u := tendsto_nhds_unique hBtend' hBtend
  have hgw : IsAdjointPair ι A g w := by
    intro φ
    have h1 : Tendsto (fun n => (⟪A (f n), ι φ⟫ : ℂ)) atTop (𝓝 ⟪w, ι φ⟫) :=
      hw.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => (⟪ι (f n), A φ⟫ : ℂ)) atTop (𝓝 ⟪g, A φ⟫) :=
      hg.inner tendsto_const_nhds
    exact tendsto_nhds_unique (h1.congr fun n => hsymm (f n) φ) h2
  have hx : IsAdjointPair ι A (u - g) (Complex.I • (u - g)) := by
    have hvw : v - w = Complex.I • (u - g) := by
      rw [smul_sub]
      rw [sub_eq_sub_iff_sub_eq_sub] at hlim ⊢
      linear_combination (norm := module) -hlim
    intro φ
    rw [← hvw, inner_sub_left, inner_sub_left, huv φ, hgw φ]
  have hzero := eq_zero_of_isAdjointPair_smul_I ι A hpos hx
  have hug : u = g := by rwa [sub_eq_zero] at hzero
  refine ⟨f, hug ▸ hg, ?_⟩
  have hvw : v = w := by
    rw [hug] at hlim
    exact (sub_left_injective (by rw [hlim] : w - Complex.I • g = v - Complex.I • g)).symm
  exact hvw ▸ hw

/-- **Von Neumann's basic criterion**: a densely defined symmetric operator whose ranges
`Ran(A + i)` and `Ran(A - i)` are dense is essentially self-adjoint. -/
theorem isEssentiallySelfAdjoint_of_dense_ranges (ι A : D →ₗ[ℂ] H)
    (hdense : Dense (Set.range ι))
    (hsymm : ∀ f g : D, ⟪A f, ι g⟫ = ⟪ι f, A g⟫)
    (hpos : Dense (Set.range (A + Complex.I • ι)))
    (hneg : Dense (Set.range (A - Complex.I • ι))) :
    IsEssentiallySelfAdjoint ι A where
  dense_domain := hdense
  symmetric := hsymm
  adjoint_symmetric := by
    intro u₁ v₁ u₂ v₂ h₁ h₂
    obtain ⟨f, hf₁, hf₂⟩ := exists_seq_tendsto_of_isAdjointPair ι A hsymm hpos hneg h₁
    have hA : Tendsto (fun n => (⟪A (f n), u₂⟫ : ℂ)) atTop (𝓝 ⟪v₁, u₂⟫) :=
      hf₂.inner tendsto_const_nhds
    have hι : Tendsto (fun n => (⟪ι (f n), v₂⟫ : ℂ)) atTop (𝓝 ⟪u₁, v₂⟫) :=
      hf₁.inner tendsto_const_nhds
    refine tendsto_nhds_unique (hA.congr fun n => ?_) hι
    calc (⟪A (f n), u₂⟫ : ℂ) = (starRingEnd ℂ) ⟪u₂, A (f n)⟫ := (inner_conj_symm _ _).symm
      _ = (starRingEnd ℂ) ⟪v₂, ι (f n)⟫ := by rw [h₂ (f n)]
      _ = ⟪ι (f n), v₂⟫ := inner_conj_symm _ _

end Abstract

/-! ## The free Laplacian on `L²(ℝ^d)` -/

/-- The Euclidean space `ℝ^d`. -/
abbrev EuclSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The symbol of the free Laplacian: `4 π² ‖ξ‖²`. -/
def freeSymbol (d : ℕ) (x : EuclSpace d) : ℝ := 4 * π ^ 2 * ‖x‖ ^ 2

theorem contDiff_freeSymbol (d : ℕ) : ContDiff ℝ ∞ (freeSymbol d) :=
  contDiff_const.mul (contDiff_norm_sq ℝ)

/-- The free Laplacian `-Δ = -∑ ∂ᵢ∂ᵢ` acting on Schwartz functions on `ℝ^d`. -/
def freeLaplacian (d : ℕ) : 𝓢(EuclSpace d, ℂ) →L[ℂ] 𝓢(EuclSpace d, ℂ) :=
  -∑ i : Fin d, (LineDeriv.lineDerivOpCLM ℂ 𝓢(EuclSpace d, ℂ) (EuclideanSpace.single i (1 : ℝ)))
    ∘L (LineDeriv.lineDerivOpCLM ℂ 𝓢(EuclSpace d, ℂ) (EuclideanSpace.single i (1 : ℝ)))

/-- The Fourier transform turns the free Laplacian into multiplication by its symbol. -/
theorem fourier_freeLaplacian (d : ℕ) (f : 𝓢(EuclSpace d, ℂ)) (x : EuclSpace d) :
    𝓕 (freeLaplacian d f) x = (freeSymbol d x : ℂ) * 𝓕 f x := by
  have key : ∀ (g : 𝓢(EuclSpace d, ℂ)) (m y : EuclSpace d),
      𝓕 (LineDeriv.lineDerivOp m g) y = (2 * π * Complex.I) * (inner ℝ y m : ℝ) * 𝓕 g y := by
    intro g m y
    have h : (fun z : EuclSpace d => (inner ℝ z m : ℝ)).HasTemperateGrowth := by fun_prop
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    simp [SchwartzMap.smulLeftCLM_apply_apply h]
    ring
  have hlap : freeLaplacian d f = -∑ i : Fin d,
      LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))
        (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f) := by
    simp [freeLaplacian]
  rw [hlap]
  have h2 : 𝓕 (-∑ i : Fin d, LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))
        (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f))
      = -∑ i : Fin d, 𝓕 (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))
        (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f)) := by
    change (fourierTransformCLM ℂ) _ = _
    rw [map_neg, map_sum]
    rfl
  rw [h2]
  simp only [SchwartzMap.neg_apply, SchwartzMap.sum_apply]
  have h3 : ∀ i : Fin d, 𝓕 (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ))
      (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) f)) x
      = -(4 * (π : ℂ) ^ 2) * ((x i : ℝ) : ℂ) ^ 2 * 𝓕 f x := by
    intro i
    rw [key, key]
    simp only [EuclideanSpace.inner_single_right, one_mul, conj_trivial]
    ring_nf
    rw [show Complex.I ^ 2 = -1 from Complex.I_sq]
    ring
  simp only [h3]
  rw [← Finset.sum_mul]
  have h4 : ∑ i : Fin d, (-(4 * (π : ℂ) ^ 2)) * ((x i : ℝ) : ℂ) ^ 2
      = -(4 * (π : ℂ) ^ 2) * ((‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.mul_sum]
    congr 1
    have hnorm : ∑ i : Fin d, (x i) ^ 2 = ‖x‖ ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [sq_abs]
    push_cast [← hnorm]
    ring
  rw [h4]
  simp only [freeSymbol]
  push_cast
  ring

/-- The inclusion of the Schwartz space into `L²(ℝ^d)`, i.e. the domain of the operator. -/
def schwartzToL2 (d : ℕ) :
    𝓢(EuclSpace d, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (EuclSpace d)) :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclSpace d))).toLinearMap

/-- The free Laplacian as an operator from the Schwartz space into `L²(ℝ^d)`. -/
def freeLaplacianL2 (d : ℕ) :
    𝓢(EuclSpace d, ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (EuclSpace d)) :=
  (schwartzToL2 d).comp (freeLaplacian d).toLinearMap

@[simp] theorem schwartzToL2_apply (d : ℕ) (f : 𝓢(EuclSpace d, ℂ)) :
    schwartzToL2 d f = f.toLp 2 (volume : Measure (EuclSpace d)) := rfl

@[simp] theorem freeLaplacianL2_apply (d : ℕ) (f : 𝓢(EuclSpace d, ℂ)) :
    freeLaplacianL2 d f = (freeLaplacian d f).toLp 2 (volume : Measure (EuclSpace d)) := rfl

theorem dense_range_schwartzToL2 (d : ℕ) : Dense (Set.range (schwartzToL2 d)) :=
  SchwartzMap.denseRange_toLpCLM (F := ℂ) (p := 2)
    (μ := (volume : Measure (EuclSpace d))) ENNReal.ofNat_ne_top

/-- The `L²` inner product of a Schwartz function with an arbitrary `L²` function. -/
theorem inner_toLp_left (d : ℕ) (Ψ : 𝓢(EuclSpace d, ℂ))
    (u : Lp ℂ 2 (volume : Measure (EuclSpace d))) :
    ⟪Ψ.toLp 2 (volume : Measure (EuclSpace d)), u⟫ = ∫ x, (starRingEnd ℂ) (Ψ x) * u x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Ψ.coeFn_toLp 2 (volume : Measure (EuclSpace d))] with x hx
  rw [hx]
  simp [RCLike.inner_apply, mul_comm]

/-- The free Laplacian is a symmetric operator on the Schwartz space. -/
theorem symmetric_freeLaplacianL2 (d : ℕ) (f g : 𝓢(EuclSpace d, ℂ)) :
    ⟪freeLaplacianL2 d f, schwartzToL2 d g⟫ = ⟪schwartzToL2 d f, freeLaplacianL2 d g⟫ := by
  simp only [schwartzToL2_apply, freeLaplacianL2_apply]
  rw [← SchwartzMap.inner_fourier_toL2_eq (freeLaplacian d f) g,
    ← SchwartzMap.inner_fourier_toL2_eq f (freeLaplacian d g),
    SchwartzMap.inner_toL2_toL2_eq (𝓕 (freeLaplacian d f)) (𝓕 g)
      (volume : Measure (EuclSpace d)),
    SchwartzMap.inner_toL2_toL2_eq (𝓕 f) (𝓕 (freeLaplacian d g))
      (volume : Measure (EuclSpace d))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [fourier_freeLaplacian, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- Given a real test function `χ`, the Schwartz function `χ / (freeSymbol + c)`. -/
theorem exists_schwartz_div (d : ℕ) (c : ℂ) (hc : c.im ≠ 0) {χ : EuclSpace d → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∃ Φ : 𝓢(EuclSpace d, ℂ), ∀ x, Φ x = (χ x : ℂ) / (((freeSymbol d x : ℝ) : ℂ) + c) := by
  have hden : ∀ x : EuclSpace d, ((freeSymbol d x : ℝ) : ℂ) + c ≠ 0 := fun x h =>
    hc (by simpa using congrArg Complex.im h)
  have hg : ContDiff ℝ ∞ (fun x : EuclSpace d => ((freeSymbol d x : ℝ) : ℂ) + c) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_freeSymbol d)).add contDiff_const
  have hsm : ContDiff ℝ ∞
      (fun x : EuclSpace d => (χ x : ℂ) / (((freeSymbol d x : ℝ) : ℂ) + c)) := by
    simp only [div_eq_mul_inv]
    exact (Complex.ofRealCLM.contDiff.comp hχ).mul (hg.inv hden)
  have hcs : HasCompactSupport
      (fun x : EuclSpace d => (χ x : ℂ) / (((freeSymbol d x : ℝ) : ℂ) + c)) := by
    have h1 : HasCompactSupport (fun x : EuclSpace d => (χ x : ℂ)) :=
      hχc.comp_left (g := Complex.ofReal) (by simp)
    have h2 := h1.mul_right (f' := fun x : EuclSpace d => (((freeSymbol d x : ℝ) : ℂ) + c)⁻¹)
    simpa [div_eq_mul_inv] using h2
  exact ⟨hcs.toSchwartzMap hsm, fun x => rfl⟩

/-- The range of `-Δ + c` on Schwartz functions is dense in `L²(ℝ^d)` whenever `c` is not
real; in particular for `c = ± i`. -/
theorem dense_range_freeLaplacianL2_add_smul (d : ℕ) (c : ℂ) (hc : c.im ≠ 0) :
    Dense (Set.range (freeLaplacianL2 d + c • schwartzToL2 d)) := by
  have hden : ∀ x : EuclSpace d, ((freeSymbol d x : ℝ) : ℂ) + c ≠ 0 := fun x h =>
    hc (by simpa using congrArg Complex.im h)
  have htoLp_add : ∀ a b : 𝓢(EuclSpace d, ℂ),
      (a + b).toLp 2 (volume : Measure (EuclSpace d))
        = a.toLp 2 (volume : Measure (EuclSpace d))
          + b.toLp 2 (volume : Measure (EuclSpace d)) :=
    fun a b => map_add (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclSpace d))) a b
  have htoLp_smul : ∀ (z : ℂ) (a : 𝓢(EuclSpace d, ℂ)),
      (z • a).toLp 2 (volume : Measure (EuclSpace d))
        = z • a.toLp 2 (volume : Measure (EuclSpace d)) :=
    fun z a => map_smul (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (EuclSpace d))) z a
  have hbot : (LinearMap.range (freeLaplacianL2 d + c • schwartzToL2 d))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hint : ∀ f : 𝓢(EuclSpace d, ℂ),
        ∫ x, (starRingEnd ℂ) ((((freeSymbol d x : ℝ) : ℂ) + c) * 𝓕 f x)
          * (𝓕 v : Lp ℂ 2 (volume : Measure (EuclSpace d))) x = 0 := by
      intro f
      have hmem : (freeLaplacian d f + c • f).toLp 2 (volume : Measure (EuclSpace d))
          ∈ LinearMap.range (freeLaplacianL2 d + c • schwartzToL2 d) := by
        refine ⟨f, ?_⟩
        simp only [LinearMap.add_apply, LinearMap.smul_apply, freeLaplacianL2_apply,
          schwartzToL2_apply]
        rw [htoLp_add, htoLp_smul]
      have h1 : ⟪(freeLaplacian d f + c • f).toLp 2 (volume : Measure (EuclSpace d)), v⟫
          = (0 : ℂ) := hv _ hmem
      rw [← MeasureTheory.Lp.inner_fourier_eq, SchwartzMap.toLp_fourier_eq,
        inner_toLp_left] at h1
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)) h1
      have hval : 𝓕 (freeLaplacian d f + c • f) x = 𝓕 (freeLaplacian d f) x + c * 𝓕 f x := by
        change (fourierTransformCLM ℂ) (freeLaplacian d f + c • f) x = _
        rw [map_add, map_smul]
        simp
      have heq : (((freeSymbol d x : ℝ) : ℂ) + c) * 𝓕 f x
          = 𝓕 (freeLaplacian d f + c • f) x := by
        rw [hval, fourier_freeLaplacian]
        ring
      simp only [heq]
    have hV : (𝓕 v : Lp ℂ 2 (volume : Measure (EuclSpace d))) = 0 := by
      rw [Lp.eq_zero_iff_ae_eq_zero]
      apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
        ((Lp.memLp (𝓕 v : Lp ℂ 2 (volume : Measure (EuclSpace d)))).locallyIntegrable
          (by norm_num))
      intro χ hχ hχc
      obtain ⟨Φ, hΦ⟩ := exists_schwartz_div d c hc hχ hχc
      have hf := hint (𝓕⁻ Φ)
      rw [show 𝓕 (𝓕⁻ Φ) = Φ from FourierTransform.fourier_fourierInv_eq Φ] at hf
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)) hf
      rw [hΦ x, mul_div_cancel₀ _ (hden x)]
      simp [Complex.real_smul]
    calc v = 𝓕⁻ (𝓕 v : Lp ℂ 2 (volume : Measure (EuclSpace d))) :=
          (FourierTransform.fourierInv_fourier_eq v).symm
      _ = 0 := by rw [hV, FourierTransform.fourierInv_zero]
  have hclosure := (Submodule.topologicalClosure_eq_top_iff
    (K := LinearMap.range (freeLaplacianL2 d + c • schwartzToL2 d))).mpr hbot
  have hd := Submodule.dense_iff_topologicalClosure_eq_top.mpr hclosure
  simpa [LinearMap.coe_range] using hd

/-- **The free Laplacian is essentially self-adjoint.**

`-Δ`, defined on the Schwartz space `𝓢(ℝ^d, ℂ)` viewed inside `L²(ℝ^d, ℂ)`, is essentially
self-adjoint: its domain is dense, it is symmetric, and its adjoint is symmetric.

The proof is via the Fourier transform (see `fourier_freeLaplacian`), which conjugates `-Δ`
into multiplication by the real symbol `4 π² ‖ξ‖²`; the statement is unconditional. -/
theorem freeLaplacian_essentiallySelfAdjoint_of_fourier (d : ℕ) :
    IsEssentiallySelfAdjoint (schwartzToL2 d) (freeLaplacianL2 d) := by
  refine isEssentiallySelfAdjoint_of_dense_ranges _ _ (dense_range_schwartzToL2 d)
    (symmetric_freeLaplacianL2 d) ?_ ?_
  · exact dense_range_freeLaplacianL2_add_smul d Complex.I (by simp)
  · have h := dense_range_freeLaplacianL2_add_smul d (-Complex.I) (by simp)
    rwa [show freeLaplacianL2 d + (-Complex.I) • schwartzToL2 d
      = freeLaplacianL2 d - Complex.I • schwartzToL2 d by rw [neg_smul, ← sub_eq_add_neg]] at h

end

end Brockian.Weyl.FreeLaplacian2

