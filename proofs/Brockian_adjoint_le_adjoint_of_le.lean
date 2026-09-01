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
# A basic criterion for essential self-adjointness

This file develops, from scratch, the classical criterion of von Neumann:

If `A` is a densely defined symmetric operator on a complex Hilbert space `H` such that the
ranges of `A + i` and `A - i` are dense — stated here in the equivalent form that a vector
orthogonal to such a range vanishes — then the adjoint `A†` is self-adjoint.  This is exactly
the statement that `A` is *essentially self-adjoint*: the closure of `A` (which is `A††`) is
self-adjoint, equivalently `A` has a unique self-adjoint extension, namely `A†`.

## Main results

* `Brockian.isSelfAdjoint_adjoint_of_denseRange`: the criterion.
* `Brockian.eq_adjoint_of_isSelfAdjoint_of_le`: uniqueness of the self-adjoint extension.
-/

open scoped ComplexInnerProductSpace
open LinearPMap

noncomputable section

namespace Brockian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Antitonicity of the adjoint: an extension has a smaller adjoint. -/
theorem adjoint_le_adjoint_of_le {A B : H →ₗ.[ℂ] H} (hA : Dense (A.domain : Set H))
    (h : A ≤ B) : B.adjoint ≤ A.adjoint := by
  have hB : Dense (B.domain : Set H) := hA.mono (by exact_mod_cast h.1)
  have key : ∀ (y : H) (hy : y ∈ B.adjoint.domain) (x : A.domain),
      ⟪B.adjoint ⟨y, hy⟩, (x : H)⟫ = ⟪y, A x⟫ := by
    intro y hy x
    rw [(LinearPMap.adjoint_isFormalAdjoint hB) ⟨y, hy⟩ ⟨(x : H), h.1 x.2⟩]
    congr 1
    exact (h.2 rfl).symm
  constructor
  · intro y hy
    exact LinearPMap.mem_adjoint_domain_of_exists _ ⟨B.adjoint ⟨y, hy⟩, key y hy⟩
  · rintro ⟨y, hy⟩ ⟨y', hy'⟩ hxy
    simp only at hxy
    subst hxy
    exact (LinearPMap.adjoint_apply_eq hA ⟨y, hy'⟩ (key y hy)).symm

/-- A densely defined operator whose adjoint is densely defined is contained in its
double adjoint. -/
theorem le_adjoint_adjoint {A : H →ₗ.[ℂ] H} (hA : Dense (A.domain : Set H))
    (hA' : Dense (A.adjoint.domain : Set H)) : A ≤ A.adjoint.adjoint := by
  have key : ∀ (x : H) (hx : x ∈ A.domain) (y : A.adjoint.domain),
      ⟪A ⟨x, hx⟩, (y : H)⟫ = ⟪x, A.adjoint y⟫ := by
    intro x hx y
    have h2 := (LinearPMap.adjoint_isFormalAdjoint hA) y ⟨x, hx⟩
    rw [← inner_conj_symm, ← h2, inner_conj_symm]
  constructor
  · intro x hx
    exact LinearPMap.mem_adjoint_domain_of_exists _ ⟨A ⟨x, hx⟩, key x hx⟩
  · rintro ⟨x, hx⟩ ⟨x', hx'⟩ hxy
    simp only at hxy
    subst hxy
    exact (LinearPMap.adjoint_apply_eq hA' ⟨x, hx'⟩ (key x hx)).symm

/-- A densely defined symmetric operator is contained in its adjoint. -/
theorem symmetric_le_adjoint {A : H →ₗ.[ℂ] H} (hdense : Dense (A.domain : Set H))
    (hsym : ∀ x y : A.domain, ⟪A x, (y : H)⟫ = ⟪(x : H), A y⟫) : A ≤ A.adjoint := by
  constructor
  · intro x hx
    exact LinearPMap.mem_adjoint_domain_of_exists _ ⟨A ⟨x, hx⟩, fun y => hsym ⟨x, hx⟩ y⟩
  · rintro ⟨x, hx⟩ ⟨x', hx'⟩ hxy
    simp only at hxy
    subst hxy
    exact (LinearPMap.adjoint_apply_eq hdense ⟨x, hx'⟩ fun y => hsym ⟨x, hx⟩ y).symm

/-- The range of `B + z`, as a submodule of `H`. -/
def shiftRange (B : H →ₗ.[ℂ] H) (z : ℂ) : Submodule ℂ H :=
  LinearMap.range (B.toFun + z • B.domain.subtype)

omit [CompleteSpace H] in
theorem mem_shiftRange_iff (B : H →ₗ.[ℂ] H) (z : ℂ) (y : H) :
    y ∈ shiftRange B z ↔ ∃ x : B.domain, B x + z • (x : H) = y := by
  simp [shiftRange, LinearMap.mem_range]

omit [CompleteSpace H] in
/-- For a symmetric operator `B` and a purely imaginary `z` of modulus one we have the
Pythagoras identity `‖Bx + z x‖² = ‖Bx‖² + ‖x‖²`. -/
theorem norm_shift_sq {B : H →ₗ.[ℂ] H}
    (hsym : ∀ x y : B.domain, ⟪B x, (y : H)⟫ = ⟪(x : H), B y⟫) {z : ℂ} (hre : z.re = 0)
    (hnorm : ‖z‖ = 1) (x : B.domain) :
    ‖B x + z • (x : H)‖ ^ 2 = ‖B x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
  have hr : ⟪B x, (x : H)⟫ = ((⟪B x, (x : H)⟫.re : ℝ) : ℂ) := by
    have h2 : ⟪B x, (x : H)⟫ = (starRingEnd ℂ) ⟪B x, (x : H)⟫ := by
      rw [inner_conj_symm]; exact hsym x x
    exact (Complex.conj_eq_iff_re.mp h2.symm).symm
  rw [@norm_add_sq ℂ, inner_smul_right, hr]
  simp [hre, norm_smul, hnorm]

/-- The range of `B + z` is closed, for `B` closed and satisfying the Pythagoras identity. -/
theorem isClosed_shiftRange {B : H →ₗ.[ℂ] H} (hcl : B.IsClosed) {z : ℂ}
    (hns : ∀ x : B.domain, ‖B x + z • (x : H)‖ ^ 2 = ‖B x‖ ^ 2 + ‖(x : H)‖ ^ 2) :
    IsClosed (shiftRange B z : Set H) := by
  classical
  set G := B.graph
  haveI : CompleteSpace G := hcl.completeSpace_coe
  set L : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) + z • (ContinuousLinearMap.fst ℂ H H) with hL
  set Ψ : G → H := fun v => L (v : H × H) with hΨ
  have hrange : (shiftRange B z : Set H) = Set.range Ψ := by
    ext y
    simp only [SetLike.mem_coe, mem_shiftRange_iff, Set.mem_range, hΨ, hL]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨((x : H), B x), by rw [LinearPMap.mem_graph_iff]; exact ⟨x, rfl, rfl⟩⟩, by simp⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff B).mp v.2
      exact ⟨x, by simp [hx1, hx2]⟩
  rw [hrange]
  have hanti : AntilipschitzWith 1 Ψ := by
    refine AntilipschitzWith.of_le_mul_dist ?_
    intro v w
    have hvw : (v : H × H) - (w : H × H) ∈ B.graph := Submodule.sub_mem _ v.2 w.2
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff B).mp hvw
    have hxe : ((v : H × H) - w) = ((x : H), B x) := Prod.ext hx1.symm hx2.symm
    have key := hns x
    have h1 : Ψ v - Ψ w = B x + z • (x : H) := by
      simp only [hΨ, hL, ← _root_.map_sub]
      rw [hxe]
      simp [add_comm]
    have hd : dist (Ψ v) (Ψ w) = ‖B x + z • (x : H)‖ := by rw [dist_eq_norm, h1]
    have hd2 : dist v w = ‖((x : H), B x)‖ := by
      rw [Subtype.dist_eq, dist_eq_norm, hxe]
    rw [hd, hd2, NNReal.coe_one, one_mul, Prod.norm_def]
    refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (norm_nonneg _) ?_
    rw [key]
    rcases max_cases ‖(x : H)‖ ‖B x‖ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
      nlinarith [sq_nonneg ‖B x‖, sq_nonneg ‖(x : H)‖]
  exact hanti.isClosed_range (L.uniformContinuous.comp uniformContinuous_subtype_val)

/-- **von Neumann's criterion.** A densely defined symmetric operator `A` such that the ranges
of `A + i` and of `A - i` have trivial orthogonal complement is essentially self-adjoint:
its adjoint is self-adjoint. -/
theorem isSelfAdjoint_adjoint_of_denseRange {A : H →ₗ.[ℂ] H} (hdense : Dense (A.domain : Set H))
    (hsym : ∀ x y : A.domain, ⟪A x, (y : H)⟫ = ⟪(x : H), A y⟫)
    (hplus : ∀ u : H, (∀ x : A.domain, ⟪u, A x + Complex.I • (x : H)⟫ = 0) → u = 0)
    (hminus : ∀ u : H, (∀ x : A.domain, ⟪u, A x - Complex.I • (x : H)⟫ = 0) → u = 0) :
    IsSelfAdjoint A.adjoint := by
  set S := A.adjoint with hS
  have hAS : A ≤ S := symmetric_le_adjoint hdense hsym
  have hSdense : Dense (S.domain : Set H) := hdense.mono (by exact_mod_cast hAS.1)
  have hSS : S.adjoint ≤ S := adjoint_le_adjoint_of_le hdense hAS
  have hASS : A ≤ S.adjoint := le_adjoint_adjoint hdense hSdense
  have hS'sym : ∀ x y : S.adjoint.domain, ⟪S.adjoint x, (y : H)⟫ = ⟪(x : H), S.adjoint y⟫ := by
    intro x y
    rw [(LinearPMap.adjoint_isFormalAdjoint hSdense) x ⟨(y : H), hSS.1 y.2⟩]
    congr 1
    exact (hSS.2 (x := y) (y := ⟨(y : H), hSS.1 y.2⟩) rfl).symm
  have hS'closed : S.adjoint.IsClosed := LinearPMap.adjoint_isClosed hSdense
  have hns := norm_shift_sq hS'sym (z := Complex.I) (by simp) (by simp)
  have hKclosed : IsClosed (shiftRange S.adjoint Complex.I : Set H) :=
    isClosed_shiftRange hS'closed hns
  haveI : CompleteSpace (shiftRange S.adjoint Complex.I) := hKclosed.completeSpace_coe
  have hKtop : shiftRange S.adjoint Complex.I = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro u hu
    refine hplus u fun x => ?_
    have hx : (x : H) ∈ S.adjoint.domain := hASS.1 x.2
    have hval : S.adjoint ⟨(x : H), hx⟩ = A x := (hASS.2 (x := x) (y := ⟨(x : H), hx⟩) rfl).symm
    have hmem : A x + Complex.I • (x : H) ∈ shiftRange S.adjoint Complex.I := by
      rw [mem_shiftRange_iff]
      exact ⟨⟨(x : H), hx⟩, by rw [hval]⟩
    rw [← inner_eq_zero_symm]
    exact (Submodule.mem_orthogonal _ u).mp hu _ hmem
  have hker : ∀ w : S.domain, S w + Complex.I • (w : H) = 0 → (w : H) = 0 := by
    intro w hw
    refine hminus (w : H) fun x => ?_
    have h1 := (LinearPMap.adjoint_isFormalAdjoint hdense) w x
    have h2 : S w = -(Complex.I • (w : H)) := by linear_combination (norm := module) hw
    rw [inner_sub_right, ← h1, h2, inner_neg_left, inner_smul_left, inner_smul_right]
    simp [Complex.conj_I]
  have hSS' : S ≤ S.adjoint := by
    have hmain : ∀ (u : H) (hu : u ∈ S.domain), ∃ (h : u ∈ S.adjoint.domain),
        S.adjoint ⟨u, h⟩ = S ⟨u, hu⟩ := by
      intro u hu
      have hmem : S ⟨u, hu⟩ + Complex.I • u ∈ shiftRange S.adjoint Complex.I := by
        rw [hKtop]; trivial
      rw [mem_shiftRange_iff] at hmem
      obtain ⟨x, hx⟩ := hmem
      have hxS : (x : H) ∈ S.domain := hSS.1 x.2
      have hxval : S ⟨(x : H), hxS⟩ = S.adjoint x :=
        (hSS.2 (x := x) (y := ⟨(x : H), hxS⟩) rfl).symm
      have hw0 : S (⟨u, hu⟩ - ⟨(x : H), hxS⟩)
          + Complex.I • ((⟨u, hu⟩ - ⟨(x : H), hxS⟩ : S.domain) : H) = 0 := by
        rw [LinearPMap.map_sub]
        have hc : ((⟨u, hu⟩ - ⟨(x : H), hxS⟩ : S.domain) : H) = u - (x : H) := rfl
        rw [hc, hxval, smul_sub]
        linear_combination (norm := module) -hx
      have hzero := hker _ hw0
      have huv : u = (x : H) := by
        have hc : ((⟨u, hu⟩ - ⟨(x : H), hxS⟩ : S.domain) : H) = u - (x : H) := rfl
        rw [hc] at hzero
        exact sub_eq_zero.mp hzero
      subst huv
      exact ⟨x.2, by rw [← hxval]⟩
    refine ⟨fun u hu => (hmain u hu).1, ?_⟩
    rintro ⟨u, hu⟩ ⟨u', hu'⟩ h
    simp only at h
    subst h
    exact ((hmain u hu).2).symm
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm hSS hSS'

/-- If `A` is essentially self-adjoint, then `A.adjoint` is its unique self-adjoint
extension. -/
theorem eq_adjoint_of_isSelfAdjoint_of_le {A B : H →ₗ.[ℂ] H} (hdense : Dense (A.domain : Set H))
    (hA : IsSelfAdjoint A.adjoint) (hB : IsSelfAdjoint B) (hAB : A ≤ B) : B = A.adjoint := by
  rw [LinearPMap.isSelfAdjoint_def] at hA hB
  have hBdense : Dense (B.domain : Set H) := hdense.mono (by exact_mod_cast hAB.1)
  have h1 : B ≤ A.adjoint := hB ▸ adjoint_le_adjoint_of_le hdense hAB
  have h2 : A.adjoint ≤ B := by
    have := adjoint_le_adjoint_of_le hBdense h1
    rwa [hA, hB] at this
  exact le_antisymm h1 h2

end Brockian

import Brockian.EssentialSelfAdjointness

/-!
# Essential self-adjointness of the free Laplacian, via Plancherel's theorem

We consider the *free Laplacian* `-Δ` on `L²(ℝ^d, ℂ)`, defined on the (dense) domain given by
the image of the Schwartz space `𝓢(ℝ^d, ℂ)` inside `L²`.  We show that this operator, viewed as
a densely defined unbounded operator (`LinearPMap`), is symmetric and **essentially
self-adjoint**: its adjoint is self-adjoint, and it admits a unique self-adjoint extension.

The proof of the crucial hypothesis of von Neumann's criterion (density of the ranges of
`-Δ ± i`) is carried out with the Fourier transform: by Plancherel's theorem the Fourier
transform is unitary on `L²`, it maps the Schwartz space onto itself, and it turns `-Δ` into
multiplication by `4π²‖ξ‖²`.  A vector orthogonal to the range of `-Δ ± i` therefore gives a
locally integrable function which integrates to zero against every test function, hence
vanishes; since `4π²‖ξ‖² ± i` never vanishes, the vector itself is zero.

## Main definitions

* `Brockian.FreeLaplacianPlancherel.freeLaplacianPMap`: the operator `-Δ` on `L²(ℝ^d)` with
  domain the image of the Schwartz space.

## Main results

* `Brockian.FreeLaplacianPlancherel.freeLaplacian_essentiallySelfAdjoint_via_plancherel`:
  the free Laplacian is densely defined, symmetric, essentially self-adjoint, and `(-Δ)†` is
  its unique self-adjoint extension.
-/

open MeasureTheory SchwartzMap Laplacian LineDeriv
open scoped ComplexConjugate FourierTransform ComplexInnerProductSpace

noncomputable section

namespace Brockian.FreeLaplacianPlancherel

/-- Euclidean space `ℝ^d`. -/
abbrev EuclSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The Hilbert space `L²(ℝ^d, ℂ)`. -/
abbrev L2s (d : ℕ) := Lp (α := EuclSpace d) ℂ 2 volume

/-- The canonical (injective) linear map from the Schwartz space into `L²(ℝ^d, ℂ)`. -/
def schwartzToL2 (d : ℕ) : 𝓢(EuclSpace d, ℂ) →ₗ[ℂ] L2s d :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).toLinearMap

theorem schwartzToL2_apply (d : ℕ) (f : 𝓢(EuclSpace d, ℂ)) :
    schwartzToL2 d f = f.toLp 2 volume := rfl

theorem schwartzToL2_injective (d : ℕ) : Function.Injective (schwartzToL2 d) :=
  SchwartzMap.injective_toLp 2 volume

/-- `-Δ` as a linear map of the Schwartz space to itself. -/
def negLaplacianL (d : ℕ) : 𝓢(EuclSpace d, ℂ) →ₗ[ℂ] 𝓢(EuclSpace d, ℂ) :=
  -(LineDeriv.laplacianCLM ℂ (EuclSpace d) 𝓢(EuclSpace d, ℂ)).toLinearMap

theorem negLaplacianL_apply (d : ℕ) (f : 𝓢(EuclSpace d, ℂ)) : negLaplacianL d f = -(Δ f) := by
  simp [negLaplacianL]

/-- The free Laplacian `-Δ` on `L²(ℝ^d, ℂ)`, as an unbounded operator with domain the image
of the Schwartz space. -/
def freeLaplacianPMap (d : ℕ) : L2s d →ₗ.[ℂ] L2s d where
  domain := LinearMap.range (schwartzToL2 d)
  toFun := (schwartzToL2 d ∘ₗ negLaplacianL d) ∘ₗ
    (LinearEquiv.ofInjective (schwartzToL2 d) (schwartzToL2_injective d)).symm.toLinearMap

theorem freeLaplacianPMap_domain (d : ℕ) :
    (freeLaplacianPMap d).domain = LinearMap.range (schwartzToL2 d) := rfl

theorem mem_freeLaplacianPMap_domain (d : ℕ) (f : 𝓢(EuclSpace d, ℂ)) :
    schwartzToL2 d f ∈ (freeLaplacianPMap d).domain := ⟨f, rfl⟩

/-- The free Laplacian sends (the `L²`-class of) a Schwartz function `f` to `-Δ f`. -/
theorem freeLaplacianPMap_apply (d : ℕ) (x : (freeLaplacianPMap d).domain)
    (f : 𝓢(EuclSpace d, ℂ)) (hx : schwartzToL2 d f = (x : L2s d)) :
    freeLaplacianPMap d x = schwartzToL2 d (-(Δ f)) := by
  have hxe : (LinearEquiv.ofInjective (schwartzToL2 d) (schwartzToL2_injective d)).symm x = f := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext hx.symm
  refine Eq.trans (congrArg (⇑(schwartzToL2 d ∘ₗ negLaplacianL d)) hxe) ?_
  rw [LinearMap.comp_apply, negLaplacianL_apply]

/-! ### The Fourier transform of the Laplacian -/

/-- The Fourier transform turns a line derivative into multiplication by `2πi⟪ξ, m⟫`. -/
theorem fourier_lineDerivOp_apply (d : ℕ) (f : 𝓢(EuclSpace d, ℂ)) (m ξ : EuclSpace d) :
    𝓕 (∂_{m} f) ξ = (2 * Real.pi * Complex.I) * (inner ℝ ξ m : ℝ) * 𝓕 f ξ := by
  have h : Function.HasTemperateGrowth (fun x : EuclSpace d => inner ℝ x m) :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  rw [SchwartzMap.fourier_lineDerivOp_eq f m]
  simp [SchwartzMap.smulLeftCLM_apply h, Complex.real_smul]
  ring

/-- The Fourier transform turns the Laplacian into multiplication by `-4π²‖ξ‖²`. -/
theorem fourier_laplacian_apply (d : ℕ) (f : 𝓢(EuclSpace d, ℂ)) (ξ : EuclSpace d) :
    𝓕 (Δ f) ξ = -(4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) * 𝓕 f ξ := by
  classical
  set b := stdOrthonormalBasis ℝ (EuclSpace d) with hb
  have hsum : ∑ i, ((inner ℝ ξ (b i) : ℝ)) ^ 2 = ‖ξ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner ξ ξ]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (b i) ξ]; ring
  rw [SchwartzMap.laplacian_eq_sum b f]
  rw [show (𝓕 (∑ i, ∂_{b i} (∂_{b i} f))) = ∑ i, 𝓕 (∂_{b i} (∂_{b i} f)) from
    map_sum (SchwartzMap.fourierTransformCLM ℂ) _ _]
  rw [SchwartzMap.sum_apply]
  have h1 : ∀ i, 𝓕 (∂_{b i} (∂_{b i} f)) ξ
      = ((-((2 * Real.pi) ^ 2 * (inner ℝ ξ (b i) : ℝ) ^ 2) : ℝ) : ℂ) * 𝓕 f ξ := by
    intro i
    rw [fourier_lineDerivOp_apply, fourier_lineDerivOp_apply]
    push_cast
    ring_nf
    simp [Complex.I_sq]
  simp_rw [h1]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum]
  congr 2
  have h2 : ∑ i, -((2 * Real.pi) ^ 2 * (inner ℝ ξ (b i) : ℝ) ^ 2)
      = -((2 * Real.pi) ^ 2 * ∑ i, (inner ℝ ξ (b i) : ℝ) ^ 2) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [h2, hsum]
  push_cast
  ring

/-! ### Density and symmetry -/

theorem dense_domain (d : ℕ) : Dense ((freeLaplacianPMap d).domain : Set (L2s d)) := by
  rw [freeLaplacianPMap_domain, LinearMap.coe_range]
  exact SchwartzMap.denseRange_toLpCLM (F := ℂ) (E := EuclSpace d) (p := 2)
    (by simp) (μ := volume)

theorem inner_schwartzToL2 (d : ℕ) (f g : 𝓢(EuclSpace d, ℂ)) :
    ⟪schwartzToL2 d f, schwartzToL2 d g⟫ = ∫ x, conj (f x) * g x := by
  rw [schwartzToL2_apply, schwartzToL2_apply, SchwartzMap.inner_toL2_toL2_eq f g volume]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp [RCLike.inner_apply, mul_comm])

theorem inner_negLaplacian_symm (d : ℕ) (f g : 𝓢(EuclSpace d, ℂ)) :
    ⟪schwartzToL2 d (-(Δ f)), schwartzToL2 d g⟫
      = ⟪schwartzToL2 d f, schwartzToL2 d (-(Δ g))⟫ := by
  set L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
    (ContinuousLinearMap.mul ℝ ℂ).comp (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap)
    with hL
  have hLapp : ∀ a b : ℂ, L a b = conj a * b := fun _ _ => rfl
  have key := SchwartzMap.integral_bilinear_laplacian_right_eq_left
    (μ := (volume : Measure (EuclSpace d))) f g L
  simp only [hLapp] at key
  rw [inner_schwartzToL2, inner_schwartzToL2]
  simp only [SchwartzMap.neg_apply, map_neg, neg_mul, mul_neg, integral_neg]
  rw [key]

theorem freeLaplacian_symmetric (d : ℕ) (x y : (freeLaplacianPMap d).domain) :
    ⟪freeLaplacianPMap d x, (y : L2s d)⟫ = ⟪(x : L2s d), freeLaplacianPMap d y⟫ := by
  obtain ⟨f, hf⟩ := x.2
  obtain ⟨g, hg⟩ := y.2
  rw [freeLaplacianPMap_apply d x f hf, freeLaplacianPMap_apply d y g hg, ← hf, ← hg]
  exact inner_negLaplacian_symm d f g

/-! ### Density of the ranges of `-Δ ± i`, via Plancherel -/

theorem inner_lp_schwartz (d : ℕ) (v : L2s d) (h : 𝓢(EuclSpace d, ℂ)) :
    ⟪v, schwartzToL2 d h⟫ = ∫ ξ, conj ((v : EuclSpace d → ℂ) ξ) * h ξ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [SchwartzMap.coeFn_toLp h 2 (volume : Measure (EuclSpace d))] with ξ hξ
  rw [schwartzToL2_apply, hξ, RCLike.inner_apply, mul_comm]

/-- The Plancherel step: if `u` is orthogonal to the range of `-Δ + z` on Schwartz functions,
then the Fourier transform of `u`, multiplied by the symbol `4π²‖ξ‖² + z`, integrates to zero
against every Schwartz function. -/
theorem integral_symbol_eq_zero (d : ℕ) (z : ℂ) (u : L2s d)
    (hu : ∀ f : 𝓢(EuclSpace d, ℂ),
      ⟪u, schwartzToL2 d (-(Δ f)) + z • schwartzToL2 d f⟫ = 0)
    (g : 𝓢(EuclSpace d, ℂ)) :
    ∫ ξ, conj (((𝓕 u : L2s d) : EuclSpace d → ℂ) ξ)
      * ((((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) + z) * g ξ = 0 := by
  set f : 𝓢(EuclSpace d, ℂ) := 𝓕⁻ g with hf
  have hfg : (𝓕 f : 𝓢(EuclSpace d, ℂ)) = g := FourierTransform.fourier_fourierInv_eq g
  set h : 𝓢(EuclSpace d, ℂ) := -(Δ f) + z • f with hh
  have h1 : schwartzToL2 d (-(Δ f)) + z • schwartzToL2 d f = schwartzToL2 d h := by
    rw [hh, map_add, map_smul]
  have h2 : ⟪u, schwartzToL2 d h⟫ = 0 := by rw [← h1]; exact hu f
  have h3 : ⟪(𝓕 u : L2s d), (𝓕 (schwartzToL2 d h) : L2s d)⟫ = 0 := by
    rw [MeasureTheory.Lp.inner_fourier_eq]; exact h2
  have h4 : (𝓕 (schwartzToL2 d h) : L2s d) = schwartzToL2 d (𝓕 h) := by
    rw [schwartzToL2_apply, SchwartzMap.toLp_fourier_eq]
    rfl
  rw [h4, inner_lp_schwartz] at h3
  rw [← h3]
  apply integral_congr_ae
  filter_upwards with ξ
  have hFT : ∀ p : 𝓢(EuclSpace d, ℂ), (𝓕 p : 𝓢(EuclSpace d, ℂ))
      = SchwartzMap.fourierTransformCLM ℂ p := fun _ => rfl
  have h5 : (𝓕 h : 𝓢(EuclSpace d, ℂ)) ξ
      = (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ) : ℂ) + z) * g ξ := by
    rw [hh, hFT, map_add, map_smul, map_neg]
    simp only [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.neg_apply, smul_eq_mul,
      SchwartzMap.fourierTransformCLM_apply]
    rw [fourier_laplacian_apply, hfg]
    push_cast
    ring
  rw [h5]
  ring

/-- A vector of `L²` whose product with a nowhere vanishing continuous function integrates to
zero against every Schwartz function is zero. -/
theorem eq_zero_of_integral_eq_zero (d : ℕ) (v : L2s d) (ψ : EuclSpace d → ℂ)
    (hψc : Continuous ψ) (hψ : ∀ ξ, ψ ξ ≠ 0)
    (hE : ∀ g : 𝓢(EuclSpace d, ℂ), ∫ ξ, conj ((v : EuclSpace d → ℂ) ξ) * ψ ξ * g ξ = 0) :
    v = 0 := by
  set w : EuclSpace d → ℂ := fun ξ => conj ((v : EuclSpace d → ℂ) ξ) * ψ ξ with hw
  have hloc : LocallyIntegrable w volume := by
    rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    have h0 : IntegrableOn (fun ξ => (v : EuclSpace d → ℂ) ξ) K volume :=
      ((Lp.memLp v).locallyIntegrable (by norm_num)).integrableOn_isCompact hK
    have h1 : IntegrableOn (fun ξ => conj ((v : EuclSpace d → ℂ) ξ)) K volume :=
      (Complex.conjLIE.toLinearIsometry.toContinuousLinearMap).integrable_comp h0
    exact h1.mul_continuousOn hψc.continuousOn hK
  have hzero : ∀ᵐ ξ, w ξ = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    intro g g_smooth g_cpt
    have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := g_cpt.comp_left rfl
    have hg₂ : ContDiff ℝ (↑(⊤ : ℕ∞)) (Complex.ofRealCLM ∘ g) := by fun_prop
    have hE' := hE (hg₁.toSchwartzMap hg₂)
    rw [← hE']
    apply integral_congr_ae
    filter_upwards with ξ
    have hcoe : (hg₁.toSchwartzMap hg₂ : EuclSpace d → ℂ) ξ = (g ξ : ℂ) := rfl
    rw [hcoe, hw]
    simp [Complex.real_smul]
    ring
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hzero] with ξ hξ
  rcases mul_eq_zero.mp hξ with h | h
  · simpa using congrArg (starRingEnd ℂ) h
  · exact absurd h (hψ ξ)

/-- The range of `-Δ + z` (on Schwartz functions) has trivial orthogonal complement, for any
non-real `z`. -/
theorem eq_zero_of_orthogonal_range (d : ℕ) (z : ℂ) (hz : z.im ≠ 0) (u : L2s d)
    (hu : ∀ f : 𝓢(EuclSpace d, ℂ),
      ⟪u, schwartzToL2 d (-(Δ f)) + z • schwartzToL2 d f⟫ = 0) :
    u = 0 := by
  have hv : (𝓕 u : L2s d) = 0 := by
    refine eq_zero_of_integral_eq_zero d (𝓕 u)
      (fun ξ => (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) + z) (by fun_prop) ?_
      (integral_symbol_eq_zero d z u hu)
    intro ξ hξ
    apply hz
    have hξ' : (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) + z = 0 := hξ
    have h0 : (((4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ).im + z.im = 0 := by
      rw [← Complex.add_im, hξ', Complex.zero_im]
    rwa [Complex.ofReal_im, zero_add] at h0
  have hv' : (MeasureTheory.Lp.fourierTransformₗᵢ (EuclSpace d) ℂ) u = 0 := hv
  exact (LinearIsometryEquiv.map_eq_zero_iff _).mp hv'

/-! ### The main theorem -/

/-- **The free Laplacian is essentially self-adjoint.**

The operator `-Δ` on `L²(ℝ^d, ℂ)`, with domain the image of the Schwartz space, is densely
defined and symmetric, its adjoint is self-adjoint (that is: `-Δ` is essentially
self-adjoint), and `(-Δ)†` is its unique self-adjoint extension.

The proof of the range condition in von Neumann's criterion goes through Plancherel's theorem:
the Fourier transform is unitary on `L²` and conjugates `-Δ` into multiplication by the
nowhere vanishing symbol `4π²‖ξ‖² ± i`. -/
theorem freeLaplacian_essentiallySelfAdjoint_via_plancherel (d : ℕ) :
    Dense ((freeLaplacianPMap d).domain : Set (L2s d)) ∧
      freeLaplacianPMap d ≤ (freeLaplacianPMap d).adjoint ∧
        IsSelfAdjoint (freeLaplacianPMap d).adjoint ∧
          ∀ B : L2s d →ₗ.[ℂ] L2s d, IsSelfAdjoint B → freeLaplacianPMap d ≤ B →
            B = (freeLaplacianPMap d).adjoint := by
  have hdense := dense_domain d
  have hsym := freeLaplacian_symmetric d
  have hshift : ∀ z : ℂ, z.im ≠ 0 → ∀ u : L2s d,
      (∀ x : (freeLaplacianPMap d).domain,
        ⟪u, freeLaplacianPMap d x + z • (x : L2s d)⟫ = 0) → u = 0 := by
    intro z hz u hu
    refine eq_zero_of_orthogonal_range d z hz u fun f => ?_
    have hx := hu ⟨schwartzToL2 d f, mem_freeLaplacianPMap_domain d f⟩
    rwa [freeLaplacianPMap_apply d ⟨schwartzToL2 d f, mem_freeLaplacianPMap_domain d f⟩ f rfl]
      at hx
  have hesa : IsSelfAdjoint (freeLaplacianPMap d).adjoint :=
    Brockian.isSelfAdjoint_adjoint_of_denseRange hdense hsym
      (hshift Complex.I (by simp))
      (by
        intro u hu
        refine hshift (-Complex.I) (by simp) u fun x => ?_
        have := hu x
        rw [← this]
        congr 1
        module)
  exact ⟨hdense, Brockian.symmetric_le_adjoint hdense hsym, hesa,
    fun B hB hAB => Brockian.eq_adjoint_of_isSelfAdjoint_of_le hdense hesa hB hAB⟩

end Brockian.FreeLaplacianPlancherel

