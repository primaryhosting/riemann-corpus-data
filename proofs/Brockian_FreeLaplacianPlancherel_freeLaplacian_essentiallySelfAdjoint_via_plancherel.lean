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
# Free Laplacian Essentially Self Adjoint Via Plancherel
Category: Brockian (Open Discharge)
Target: Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory SchwartzMap FourierTransform Laplacian LineDeriv
open scoped ContDiff

namespace Brockian.FreeLaplacianPlancherel

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Von Neumann's basic criterion for essential self-adjointness of a symmetric operator
`A` defined on a dense domain, presented abstractly: the domain is a complex vector space `D`
mapped into the Hilbert space `H` by `ι` with dense range, `A` is symmetric, and the operators
`A ± i` have dense range (i.e. both deficiency subspaces are trivial). -/
structure IsEssentiallySelfAdjointCore {D H : Type*} [AddCommGroup D] [Module ℂ D]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι A : D →ₗ[ℂ] H) : Prop where
  /-- The operator is densely defined. -/
  denseRange_domain : DenseRange ι
  /-- The operator is symmetric on its domain. -/
  symmetric : ∀ f g : D, inner ℂ (A f) (ι g) = inner ℂ (ι f) (A g)
  /-- The deficiency subspace at `i` is trivial. -/
  denseRange_add_I : DenseRange fun f : D => A f + Complex.I • ι f
  /-- The deficiency subspace at `-i` is trivial. -/
  denseRange_sub_I : DenseRange fun f : D => A f - Complex.I • ι f

variable (V) in
/-- The inclusion of the Schwartz space into `L²`, i.e. the domain of the free Laplacian. -/
def incl : 𝓢(V, ℂ) →L[ℂ] Lp (α := V) ℂ 2 := SchwartzMap.toLpCLM ℂ ℂ 2 volume

variable (V) in
/-- The free Laplacian `-Δ` on `L²(V)`, defined on the Schwartz space. -/
def freeLaplacian : 𝓢(V, ℂ) →L[ℂ] Lp (α := V) ℂ 2 :=
  -(incl V ∘L laplacianCLM ℂ V 𝓢(V, ℂ))

@[simp] lemma incl_apply (f : 𝓢(V, ℂ)) : incl V f = f.toLp 2 volume := rfl

@[simp] lemma freeLaplacian_apply (f : 𝓢(V, ℂ)) :
    freeLaplacian V f = -((Δ f : 𝓢(V, ℂ)).toLp 2 volume) := by
  simp [freeLaplacian, incl]

/-- The Fourier transform turns the Laplacian into multiplication by `-4π²‖ξ‖²`. -/
lemma fourier_laplacian_apply (f : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (Δ f) ξ = (-(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) : ℝ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ V with hb
  have h1 : ∀ (m : V) (h : 𝓢(V, ℂ)) (ζ : V),
      𝓕 (∂_{m} h) ζ = (2 * Real.pi * Complex.I) * ((inner ℝ ζ m : ℝ) : ℂ) * 𝓕 h ζ := by
    intro m h ζ
    have ht : (fun x : V => (inner ℝ x m : ℝ)).HasTemperateGrowth := by fun_prop
    rw [SchwartzMap.fourier_lineDerivOp_eq h m]
    simp [ht, mul_assoc]
  have h2 : 𝓕 (Δ f) ξ = ∑ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ := by
    rw [SchwartzMap.laplacian_eq_sum b f, ← SchwartzMap.fourierTransformCLM_apply ℂ, map_sum]
    simp [SchwartzMap.sum_apply]
  have h3 : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ
      = -(4 * (Real.pi : ℂ) ^ 2 * ((inner ℝ ξ (b i) : ℝ) : ℂ) ^ 2) * 𝓕 f ξ := by
    intro i
    rw [h1, h1]
    ring_nf
    simp [Complex.I_sq]
  have hsum : ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2 = ‖ξ‖ ^ 2 := b.sum_sq_inner_left ξ
  have h := congrArg (fun r : ℝ => (r : ℂ)) hsum
  push_cast at h
  rw [h2]
  simp only [h3, ← Finset.sum_mul]
  push_cast
  rw [← h, Finset.mul_sum]
  simp

/-- The free Laplacian is symmetric on the Schwartz space. -/
lemma freeLaplacian_symmetric (f g : 𝓢(V, ℂ)) :
    inner ℂ (freeLaplacian V f) (incl V g) = inner ℂ (incl V f) (freeLaplacian V g) := by
  have key := SchwartzMap.integral_bilinear_laplacian_right_eq_left (μ := (volume : Measure V)) f g
    ((ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, ContinuousLinearMap.mul_apply'] at key
  simp only [freeLaplacian_apply, incl_apply, inner_neg_left, inner_neg_right,
    SchwartzMap.inner_toL2_toL2_eq, RCLike.inner_apply]
  have key2 : ∫ (x : V), g x * (starRingEnd ℂ) ((Δ f) x)
      = ∫ (x : V), (Δ g) x * (starRingEnd ℂ) (f x) := by
    calc ∫ (x : V), g x * (starRingEnd ℂ) ((Δ f) x)
        = ∫ (x : V), (starRingEnd ℂ) ((Δ f) x) * g x := by congr 1; funext x; ring
      _ = ∫ (x : V), (starRingEnd ℂ) (f x) * (Δ g) x := key.symm
      _ = _ := by congr 1; funext x; ring
  rw [key2]

/-- The operator `-Δ + c` is the composition of the inclusion with the Schwartz-space
operator `f ↦ -Δ f + c • f`. -/
lemma op_eq_incl (c : ℂ) (f : 𝓢(V, ℂ)) :
    freeLaplacian V f + c • incl V f = incl V (-(Δ f) + c • f) := by
  rw [map_add, map_neg, map_smul]
  simp [freeLaplacian]

/-- The inclusion `𝓢 → L²` intertwines the two Fourier transforms. -/
lemma incl_fourier (w : 𝓢(V, ℂ)) : incl V (𝓕 w) = 𝓕 (incl V w) := by
  simp [incl]

/-- The Fourier multiplier of `-Δ + c` is `4π²‖ξ‖² + c`. -/
lemma fourier_op_apply (c : ℂ) (f : 𝓢(V, ℂ)) (ξ : V) :
    𝓕 (-(Δ f) + c • f : 𝓢(V, ℂ)) ξ = (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c) * 𝓕 f ξ := by
  rw [← SchwartzMap.fourierTransformCLM_apply ℂ, map_add, map_neg, map_smul]
  simp only [SchwartzMap.add_apply, SchwartzMap.neg_apply, SchwartzMap.smul_apply,
    SchwartzMap.fourierTransformCLM_apply, fourier_laplacian_apply, smul_eq_mul]
  push_cast
  ring

/-- Since `4π²‖ξ‖² + c` never vanishes for non-real `c`, every real test function is of the
form `𝓕 (-Δ f + c • f)` for some Schwartz function `f`. -/
lemma exists_schwartz_fourier_eq (c : ℂ) (hc : c.im ≠ 0) (g : V → ℝ) (hg : ContDiff ℝ ∞ g)
    (hsupp : HasCompactSupport g) :
    ∃ f : 𝓢(V, ℂ), ∀ ξ, 𝓕 (-(Δ f) + c • f : 𝓢(V, ℂ)) ξ = (g ξ : ℂ) := by
  have hne : ∀ ξ : V, ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c ≠ 0 := by
    intro ξ h
    apply hc
    have h2 := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.zero_im, zero_add] at h2
    exact h2
  have hden : ContDiff ℝ ∞ (fun ξ : V => ((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c) := by
    have h1 : ContDiff ℝ ∞ (fun ξ : V => (4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) := by
      have : ContDiff ℝ ∞ (fun ξ : V => ‖ξ‖ ^ 2) := contDiff_norm_sq ℝ
      fun_prop
    exact (Complex.ofRealCLM.contDiff.comp h1).add contDiff_const
  have hnum : ContDiff ℝ ∞ (fun ξ : V => (g ξ : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  have hsmooth : ContDiff ℝ ∞
      (fun ξ : V => (g ξ : ℂ) * (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c)⁻¹) :=
    hnum.mul (hden.inv hne)
  have hcs : HasCompactSupport
      (fun ξ : V => (g ξ : ℂ) * (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c)⁻¹) := by
    have : HasCompactSupport (fun ξ : V => (g ξ : ℂ)) :=
      hsupp.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    exact this.mul_right
  refine ⟨𝓕⁻ (hcs.toSchwartzMap hsmooth), fun ξ => ?_⟩
  rw [fourier_op_apply, FourierTransform.fourier_fourierInv_eq]
  show (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c) *
      ((g ξ : ℂ) * (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + c)⁻¹) = (g ξ : ℂ)
  rw [mul_comm (g ξ : ℂ), ← mul_assoc, mul_inv_cancel₀ (hne ξ), one_mul]

/-- If an `L²` function is orthogonal to the range of `-Δ + c` (`c` non-real), it vanishes.
This is the triviality of the deficiency subspaces, obtained from Plancherel's theorem. -/
lemma eq_zero_of_inner_op_eq_zero (c : ℂ) (hc : c.im ≠ 0) (u : Lp (α := V) ℂ 2)
    (hu : ∀ f : 𝓢(V, ℂ), inner ℂ (freeLaplacian V f + c • incl V f) u = 0) : u = 0 := by
  have hmain : ∀ f : 𝓢(V, ℂ),
      inner ℂ (incl V (𝓕 (-(Δ f) + c • f) : 𝓢(V, ℂ))) (𝓕 u : Lp (α := V) ℂ 2 volume) = 0 := by
    intro f
    rw [incl_fourier, Lp.inner_fourier_eq, ← op_eq_incl]
    exact hu f
  have hzero : ∀ g : V → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • ((𝓕 u : Lp (α := V) ℂ 2 volume) x) = 0 := by
    intro g hg hsupp
    obtain ⟨f, hf⟩ := exists_schwartz_fourier_eq c hc g hg hsupp
    have h2 := hmain f
    rw [L2.inner_def] at h2
    have hcoe := (𝓕 (-(Δ f) + c • f) : 𝓢(V, ℂ)).coeFn_toLp 2 (μ := (volume : Measure V))
    rw [← h2]
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [incl_apply, hx, RCLike.inner_apply, hf x]
    simp [Complex.real_smul, mul_comm]
  have hloc : LocallyIntegrable (fun x => (𝓕 u : Lp (α := V) ℂ 2 volume) x) (volume : Measure V) :=
    (Lp.memLp _).locallyIntegrable one_le_two
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hzero
  have hv0 : (𝓕 u : Lp (α := V) ℂ 2 volume) = 0 := Lp.eq_zero_iff_ae_eq_zero.2 hae
  have hu' : u = 𝓕⁻ (𝓕 u : Lp (α := V) ℂ 2 volume) := (FourierTransform.fourierInv_fourier_eq u).symm
  rw [hu', hv0]
  simp

/-- For any non-real complex number `c`, the operator `-Δ + c` has dense range. -/
lemma denseRange_freeLaplacian_add_smul (c : ℂ) (hc : c.im ≠ 0) :
    DenseRange fun f : 𝓢(V, ℂ) => freeLaplacian V f + c • incl V f := by
  set T : 𝓢(V, ℂ) →L[ℂ] Lp (α := V) ℂ 2 := freeLaplacian V + c • incl V with hT
  have hrange : (Set.range fun f : 𝓢(V, ℂ) => freeLaplacian V f + c • incl V f)
      = ((LinearMap.range (T : 𝓢(V, ℂ) →ₗ[ℂ] Lp (α := V) ℂ 2) : Submodule ℂ _) :
        Set (Lp (α := V) ℂ 2)) := by
    ext x
    simp [hT, LinearMap.mem_range]
  rw [DenseRange, hrange, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro u hu
  refine eq_zero_of_inner_op_eq_zero c hc u fun f => ?_
  exact hu _ ⟨f, rfl⟩

lemma denseRange_incl : DenseRange (incl V) :=
  SchwartzMap.denseRange_toLpCLM (by simp)

/-- **The free Laplacian is essentially self-adjoint on the Schwartz space.**
Proved via Plancherel's theorem: the Fourier transform conjugates `-Δ` into multiplication by
the real function `4π²‖ξ‖²`, which is symmetric, and `4π²‖ξ‖² ± i` never vanishes, so both
deficiency subspaces are trivial. -/
theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel :
    IsEssentiallySelfAdjointCore ((incl V).toLinearMap) ((freeLaplacian V).toLinearMap) where
  denseRange_domain := denseRange_incl
  symmetric := freeLaplacian_symmetric
  denseRange_add_I := denseRange_freeLaplacian_add_smul Complex.I (by simp)
  denseRange_sub_I := by
    have := denseRange_freeLaplacian_add_smul (V := V) (-Complex.I) (by simp)
    simpa [sub_eq_add_neg, neg_smul] using this

/-- Triviality of the deficiency subspaces in adjoint form: if an `L²` function `u` is a weak
eigenfunction of the adjoint of the free Laplacian with non-real eigenvalue `z`, then `u = 0`. -/
theorem deficiency_eq_zero (z : ℂ) (hz : z.im ≠ 0) (u : Lp (α := V) ℂ 2)
    (hu : ∀ f : 𝓢(V, ℂ), inner ℂ (freeLaplacian V f) u = z * inner ℂ (incl V f) u) : u = 0 := by
  refine eq_zero_of_inner_op_eq_zero (-(starRingEnd ℂ) z) (by simpa using hz) u fun f => ?_
  rw [inner_add_left, inner_smul_left, hu f]
  simp

/-- The concrete case of the free Laplacian on `L²(ℝ^d)`. -/
theorem freeLaplacian_essentiallySelfAdjoint_euclidean (d : ℕ) :
    IsEssentiallySelfAdjointCore ((incl (EuclideanSpace ℝ (Fin d))).toLinearMap)
      ((freeLaplacian (EuclideanSpace ℝ (Fin d))).toLinearMap) :=
  freeLaplacian_essentiallySelfAdjoint_via_plancherel

end

end Brockian.FreeLaplacianPlancherel

