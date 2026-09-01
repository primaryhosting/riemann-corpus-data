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
  Brockian/WeylCayley.lean — unitary conjugation of unbounded operators.

  The corpus module of this name was not supplied; this file provides the object
  `conjugatePMap` used by `Brockian.WeylFreeLaplacianCorrected`: the unitary
  conjugate `U T U⁻¹` of a partially defined operator `T`, with domain the image
  `U (dom T)`.
-/
import Mathlib
import Brockian.WeylOperator

namespace Brockian.Weyl.Cayley

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- **Unitary conjugation of an unbounded operator.** For a unitary
`e : H ≃ₗᵢ[ℂ] K` and a partially defined operator `T` on `H`, the operator
`e ∘ T ∘ e⁻¹` on `K`, defined on the image `e (dom T)`. -/
noncomputable def conjugatePMap (e : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H) : K →ₗ.[ℂ] K where
  domain := Submodule.map (e.toLinearEquiv : H →ₗ[ℂ] K) T.domain
  toFun := ((e.toLinearEquiv.toLinearMap.comp T.toFun).comp
    (e.toLinearEquiv.submoduleMap T.domain).symm.toLinearMap)

@[simp] theorem conjugatePMap_domain (e : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H) :
    (conjugatePMap e T).domain = Submodule.map (e.toLinearEquiv : H →ₗ[ℂ] K) T.domain := rfl

/-- Membership in the domain of the conjugated operator. -/
theorem mem_conjugatePMap_domain (e : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H) (x : T.domain) :
    (e (x : H)) ∈ (conjugatePMap e T).domain := ⟨(x : H), x.2, rfl⟩

/-- The value of the conjugated operator at `e x` is `e (T x)`. -/
theorem conjugatePMap_apply (e : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H) (x : T.domain)
    (y : (conjugatePMap e T).domain) (hy : (y : K) = e (x : H)) :
    conjugatePMap e T y = e (T x) := by
  have hxy : (e.toLinearEquiv.submoduleMap T.domain).symm y = x := by
    apply (e.toLinearEquiv.submoduleMap T.domain).injective
    rw [LinearEquiv.apply_symm_apply]
    exact Subtype.ext (by rw [hy]; exact (LinearEquiv.submoduleMap_apply _ _ _).symm)
  show e.toLinearEquiv (T ((e.toLinearEquiv.submoduleMap T.domain).symm y)) = e (T x)
  rw [hxy]
  rfl

end Brockian.Weyl.Cayley

/-
  Brockian/WeylOperator.lean — the abstract symmetric-operator / (essential)
  self-adjointness scaffolding underneath the **Weyl criterion**, built over
  Mathlib's partially-defined linear maps `H →ₗ.[ℂ] H` (`LinearPMap`).

  (Supplied corpus source, reproduced verbatim.)
-/
import Mathlib

namespace Brockian.Weyl.Operator

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Symmetric densely-defined operators -/

/-- **Symmetric operator.** A partially-defined operator `T : H →ₗ.[ℂ] H` is
*symmetric* when it is its own formal adjoint: `⟪T x, y⟫ = ⟪x, T y⟫` for all
`x, y` in the domain. This is the honest `LinearPMap` formulation (Mathlib has
`IsFormalAdjoint` but no `IsSymmetric`). -/
def IsSymmetric (T : H →ₗ.[ℂ] H) : Prop := T.IsFormalAdjoint T

/-- The defining identity of a symmetric operator, unpacked. -/
theorem IsSymmetric.inner_apply {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (x y : T.domain) : ⟪T x, (y : H)⟫_ℂ = ⟪(x : H), T y⟫_ℂ := hT x y

/-- **The quadratic form of a symmetric operator is real.** For any `v` in the
domain, `⟪T v, v⟫` has zero imaginary part. This is the seed of the "spectrum is
real" phenomenon: from it both real eigenvalues and the basic inequality below
follow. -/
theorem IsSymmetric.inner_self_im {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (v : T.domain) : (⟪T v, (v : H)⟫_ℂ).im = 0 := by
  have h1 : ⟪T v, (v : H)⟫_ℂ = ⟪(v : H), T v⟫_ℂ := hT v v
  have h2 : (starRingEnd ℂ) ⟪T v, (v : H)⟫_ℂ = ⟪(v : H), T v⟫_ℂ :=
    inner_conj_symm (v : H) (T v)
  rw [← h1] at h2
  rwa [Complex.conj_eq_iff_im] at h2

/-- **Eigenvalues of a symmetric operator are real.** If `T v = μ • v` for a
nonzero `v` in the domain, then `μ` is real (`μ.im = 0`). -/
theorem IsSymmetric.im_eq_zero_of_apply_eq_smul {T : H →ₗ.[ℂ] H}
    (hT : IsSymmetric T) {v : T.domain} {μ : ℂ} (hv : (v : H) ≠ 0)
    (heig : T v = μ • (v : H)) : μ.im = 0 := by
  have hb := hT.inner_self_im v
  rw [heig, inner_smul_left] at hb
  set s : ℂ := ⟪(v : H), (v : H)⟫_ℂ with hs
  have hsim : s.im = 0 := by
    have hc : (starRingEnd ℂ) s = s := inner_conj_symm (v : H) (v : H)
    rwa [Complex.conj_eq_iff_im] at hc
  have hsre : s.re = ‖(v : H)‖ ^ 2 := by rw [hs]; exact inner_self_eq_norm_sq (𝕜 := ℂ) (v : H)
  rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, hsim] at hb
  have hsrepos : (0 : ℝ) < s.re := by rw [hsre]; positivity
  have hz : μ.im * s.re = 0 := by linear_combination -hb
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hsrepos)

/-! ### The basic symmetric-operator inequality -/

/-- **The basic symmetric-operator inequality** `‖T v − z·v‖ ≥ |Im z|·‖v‖`.

For a symmetric `T`, every `z : ℂ`, and every `v` in the domain. This is the
analytic heart of the whole self-adjointness story: it is the Pythagorean
identity
    `‖(T − z)v‖² = ‖(T − Re z)v‖² + (Im z)²‖v‖²`
(valid because `⟪T v, v⟫` is real), from which we read off `≥ (Im z)²‖v‖²` and
take square roots. When `Im z ≠ 0` it forces `T − z` injective (below) and, in
the closed case, boundedly-invertible onto its range. -/
theorem IsSymmetric.norm_sub_smul_ge {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (v : T.domain) (z : ℂ) : |z.im| * ‖(v : H)‖ ≤ ‖T v - z • (v : H)‖ := by
  set u : H := T v with hu
  set w : H := (v : H) with hw
  -- `⟪u, w⟫` is real (quadratic form of a symmetric operator)
  have hc : (⟪u, w⟫_ℂ).im = 0 := hT.inner_self_im v
  -- component identities for the complex scalar `z`
  have hnormz : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
  have hnormzr : ‖(z.re : ℂ)‖ = |z.re| := by simp
  -- expand both norms via the (RCLike) parallelogram/`norm_sub_sq` formula
  have e1 : ‖u - z • w‖ ^ 2 = ‖u‖ ^ 2 - 2 * RCLike.re (⟪u, z • w⟫_ℂ) + ‖z • w‖ ^ 2 :=
    norm_sub_sq u (z • w)
  have e2 : ‖u - (z.re : ℂ) • w‖ ^ 2
      = ‖u‖ ^ 2 - 2 * RCLike.re (⟪u, (z.re : ℂ) • w⟫_ℂ) + ‖(z.re : ℂ) • w‖ ^ 2 :=
    norm_sub_sq u _
  rw [inner_smul_right, norm_smul] at e1
  rw [inner_smul_right, norm_smul, hnormzr] at e2
  -- the real parts of the cross terms coincide (imaginary part of `⟪u,w⟫` drops out)
  have hr1 : RCLike.re (z * ⟪u, w⟫_ℂ) = z.re * (⟪u, w⟫_ℂ).re := by
    show (z * ⟪u, w⟫_ℂ).re = z.re * (⟪u, w⟫_ℂ).re
    rw [Complex.mul_re, hc]; ring
  have hr2 : RCLike.re ((z.re : ℂ) * ⟪u, w⟫_ℂ) = z.re * (⟪u, w⟫_ℂ).re := by
    show ((z.re : ℂ) * ⟪u, w⟫_ℂ).re = z.re * (⟪u, w⟫_ℂ).re
    rw [Complex.mul_re, hc]; simp
  rw [hr1] at e1; rw [hr2] at e2
  -- the Pythagorean split identity
  have key : ‖u - z • w‖ ^ 2 = ‖u - (z.re : ℂ) • w‖ ^ 2 + z.im ^ 2 * ‖w‖ ^ 2 := by
    rw [e1, e2]
    have ha : (‖z‖ * ‖w‖) ^ 2 = (z.re ^ 2 + z.im ^ 2) * ‖w‖ ^ 2 := by rw [mul_pow, hnormz]
    have hb : (|z.re| * ‖w‖) ^ 2 = z.re ^ 2 * ‖w‖ ^ 2 := by rw [mul_pow, sq_abs]
    rw [ha, hb]; ring
  -- read off the squared inequality, then take square roots
  have hge : z.im ^ 2 * ‖w‖ ^ 2 ≤ ‖u - z • w‖ ^ 2 := by
    rw [key]; nlinarith [sq_nonneg ‖u - (z.re : ℂ) • w‖]
  have hA : (0 : ℝ) ≤ |z.im| * ‖w‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hsq : (|z.im| * ‖w‖) ^ 2 = z.im ^ 2 * ‖w‖ ^ 2 := by rw [mul_pow, sq_abs]
  calc |z.im| * ‖w‖ = Real.sqrt ((|z.im| * ‖w‖) ^ 2) := (Real.sqrt_sq hA).symm
    _ = Real.sqrt (z.im ^ 2 * ‖w‖ ^ 2) := by rw [hsq]
    _ ≤ Real.sqrt (‖u - z • w‖ ^ 2) := Real.sqrt_le_sqrt hge
    _ = ‖u - z • w‖ := Real.sqrt_sq (norm_nonneg _)

/-- **`T − z` is injective on the domain for nonreal `z`.** If `T` is symmetric,
`Im z ≠ 0`, and `T v = z • v`, then `v = 0`. Immediate from the basic inequality
(a nonzero eigenvector at `z` would force `|Im z|·‖v‖ ≤ 0`). -/
theorem IsSymmetric.eq_zero_of_apply_eq_smul {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    {z : ℂ} (hz : z.im ≠ 0) {v : T.domain} (h : T v = z • (v : H)) :
    (v : H) = 0 := by
  have hineq := hT.norm_sub_smul_ge v z
  rw [h, sub_self, norm_zero] at hineq
  have h1 : |z.im| * ‖(v : H)‖ = 0 :=
    le_antisymm hineq (mul_nonneg (abs_nonneg _) (norm_nonneg _))
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (abs_eq_zero.mp h2) hz
  · exact norm_eq_zero.mp h2

/-! ### Deficiency spaces and essential self-adjointness -/

section Adjoint

variable [CompleteSpace H]

/-- **The deficiency space `ker(T* − z)`.** For a densely-defined `T`, the
adjoint `T* = T.adjoint` is a `LinearPMap`; the deficiency space at `z` is the
kernel of the honest linear map `f ↦ T* f − z·f` on `dom(T*)`. It is *not*
`{0}` by fiat — it is a genuine kernel, and it measures the failure of essential
self-adjointness (Weyl / von Neumann). -/
noncomputable def deficiencySpace (T : H →ₗ.[ℂ] H) (z : ℂ) :
    Submodule ℂ T.adjoint.domain :=
  LinearMap.ker (T.adjoint.toFun - z • T.adjoint.domain.subtype)

/-- **Deficiency-space membership = eigenvector of the adjoint.**
`g ∈ ker(T* − z) ↔ T* g = z • g`. Confirms the definition is the real one. -/
theorem mem_deficiencySpace_iff (T : H →ₗ.[ℂ] H) (z : ℂ) (g : T.adjoint.domain) :
    g ∈ deficiencySpace T z ↔ T.adjoint g = z • (g : H) := by
  rw [deficiencySpace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Submodule.subtype_apply, sub_eq_zero]
  rfl

/-- **Essential self-adjointness (the Weyl-criterion predicate).** A symmetric
operator is essentially self-adjoint exactly when both deficiency spaces
`ker(T* ∓ i)` are trivial. This is the genuine predicate the Weyl limit-point
criterion certifies — not a placeholder. -/
def EssentiallySelfAdjoint (T : H →ₗ.[ℂ] H) : Prop :=
  deficiencySpace T Complex.I = ⊥ ∧ deficiencySpace T (-Complex.I) = ⊥

end Adjoint

/-! ### Gate-0 witness: a concrete symmetric operator -/

/-- **The everywhere-defined real-scalar operator** `x ↦ (c : ℝ) • x`, packaged
as a `LinearPMap` with full domain `⊤`. For `c = 1` this is the identity. -/
noncomputable def smulPMap (c : ℝ) : H →ₗ.[ℂ] H := ((c : ℂ) • LinearMap.id).toPMap ⊤

/-- The witness acts as multiplication by the real scalar `c`. -/
@[simp] theorem smulPMap_apply (c : ℝ) (x : (smulPMap (H := H) c).domain) :
    (smulPMap c) x = (c : ℂ) • (x : H) := by
  simp [smulPMap, LinearMap.toPMap_apply]

/-- The witness is everywhere defined (domain `= ⊤`), hence densely defined. -/
theorem smulPMap_domain (c : ℝ) : (smulPMap (H := H) c).domain = ⊤ := by
  simp [smulPMap, LinearMap.toPMap]

/-- **Gate-0 (non-vacuity).** The real-scalar operator `smulPMap c` is symmetric,
instantiating `IsSymmetric` — and hence the inequality `norm_sub_smul_ge`, the
real-spectrum lemmas, and the injectivity corollary — on a genuine, nonzero
operator. So none of the framework is vacuous. -/
theorem smulPMap_isSymmetric (c : ℝ) : IsSymmetric (smulPMap (H := H) c) := by
  intro x y
  rw [smulPMap_apply, smulPMap_apply, inner_smul_left, inner_smul_right]
  simp

end Brockian.Weyl.Operator

/-
  Brockian/WeylSchrodingerGate1Final.lean — the minimal free Schrödinger
  operator `-d²/dx²` on the Schwartz core.

  The corpus module of this name was not supplied; this file provides the object
  `freeSchrodingerPMap` used by `Brockian.WeylFreeLaplacianCorrected`, built
  exactly like the minimal Schrödinger operator of
  `Brockian.WeylSchrodingerMinimal` with zero potential: the operator
  `f ↦ -f″` defined on the dense Schwartz core `range schwartzToL2 ⊆ L²(ℝ)`.
-/
import Mathlib
import Brockian.WeylSchrodingerMinimal

open MeasureTheory SchwartzMap
open scoped InnerProductSpace

namespace Brockian.Weyl.SchrodingerGate1Final

open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerMinimal

/-- The free (kinetic) action `f ↦ -f″` on the Schwartz core, valued in `L²`. -/
noncomputable def freeCoreMap : SchwartzMap ℝ ℂ →ₗ[ℂ] H2 :=
  -(schwartzToL2.comp (D2 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ).toLinearMap)

theorem freeCoreMap_apply (f : SchwartzMap ℝ ℂ) :
    freeCoreMap f = -(schwartzToL2 (D2 f)) := rfl

/-- **The minimal free Schrödinger operator** `-d²/dx²` on `L²(ℝ)`, defined on
the dense Schwartz core. -/
noncomputable def freeSchrodingerPMap : H2 →ₗ.[ℂ] H2 where
  domain := LinearMap.range schwartzToL2
  toFun := freeCoreMap.comp
    (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap

@[simp] theorem freeSchrodingerPMap_domain :
    freeSchrodingerPMap.domain = LinearMap.range schwartzToL2 := rfl

/-- Exact action on an embedded Schwartz function. -/
theorem freeSchrodingerPMap_toFun_ofInjective (f : SchwartzMap ℝ ℂ) :
    freeSchrodingerPMap (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
      = freeCoreMap f := by
  show freeCoreMap.comp
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
    = freeCoreMap f
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]

/-- **Density of the free core** (Schwartz functions are dense in `L²`). -/
theorem freeSchrodingerPMap_dense :
    Dense (freeSchrodingerPMap.domain : Set H2) := by
  have hfun : (schwartzToL2 : SchwartzMap ℝ ℂ → H2)
      = (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) := by
    funext f; rw [schwartzToL2_apply, SchwartzMap.toLpCLM_apply]
  rw [freeSchrodingerPMap_domain, LinearMap.coe_range, hfun]
  exact SchwartzMap.denseRange_toLpCLM (by norm_num)

/-- **Symmetry of the minimal free operator** (double integration by parts). -/
theorem freeSchrodingerPMap_isSymmetric : IsSymmetric freeSchrodingerPMap := by
  intro x y
  obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
  obtain ⟨g, hg⟩ := (LinearMap.mem_range).mp y.2
  have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
  have hye : y = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective g :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hg.symm)
  rw [hxe, hye, freeSchrodingerPMap_toFun_ofInjective, freeSchrodingerPMap_toFun_ofInjective,
    LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply, freeCoreMap_apply,
    freeCoreMap_apply, inner_neg_left, inner_neg_right, kinetic_symm f g]

end Brockian.Weyl.SchrodingerGate1Final

/-
  Brockian/WeylMaximalMultiplication.lean — maximal multiplication operators on
  `L²`.

  The corpus module of this name was not supplied; this file provides the object
  `maximalMul` used by `Brockian.WeylFreeLaplacianCorrected`, defined in the
  standard way: the multiplication operator `f ↦ m · f` with its *maximal*
  domain `{f ∈ L² | m · f ∈ L²}`.
-/
import Mathlib
import Brockian.WeylSchrodingerMinimal

open MeasureTheory

namespace Brockian.Weyl.MaximalMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The maximal domain of multiplication by `m` inside `L²(μ)`: the set of `L²`
classes `f` such that `m · f` is again square integrable. -/
noncomputable def maximalMulDomain (m : α → ℂ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (m * (f : α → ℂ)) 2 μ}
  add_mem' := by
    intro f g hf hg
    refine MemLp.ae_eq ?_ (hf.add hg)
    filter_upwards [Lp.coeFn_add f g] with x hx
    simp only [Pi.add_apply, Pi.mul_apply, hx, mul_add]
  zero_mem' := by
    show MemLp (m * ((0 : Lp ℂ 2 μ) : α → ℂ)) 2 μ
    refine MemLp.ae_eq ?_ (MemLp.zero (ε := ℂ) (p := 2) (μ := μ))
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx
    simp only [Pi.mul_apply, hx, Pi.zero_apply, mul_zero]
  smul_mem' := by
    intro c f hf
    refine MemLp.ae_eq ?_ (hf.const_smul c)
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply, Pi.mul_apply, hx, smul_eq_mul]
    ring

@[simp] theorem mem_maximalMulDomain_iff (m : α → ℂ) (f : Lp ℂ 2 μ) :
    f ∈ maximalMulDomain (μ := μ) m ↔ MemLp (m * (f : α → ℂ)) 2 μ := Iff.rfl

/-- **Maximal multiplication operator.** The unbounded operator `f ↦ m · f` on
`L²(μ)`, with maximal domain `{f | m · f ∈ L²}`. -/
noncomputable def maximalMul (m : α → ℂ) : Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := maximalMulDomain m
  toFun :=
    { toFun := fun f => MemLp.toLp _ f.2
      map_add' := by
        intro f g
        refine Lp.ext ?_
        filter_upwards [(MemLp.coeFn_toLp (f + g).2), Lp.coeFn_add (MemLp.toLp _ f.2)
          (MemLp.toLp _ g.2), MemLp.coeFn_toLp f.2, MemLp.coeFn_toLp g.2,
          Lp.coeFn_add (f : Lp ℂ 2 μ) (g : Lp ℂ 2 μ)] with x h1 h2 h3 h4 h5
        rw [h1, h2]
        simp only [Pi.add_apply]
        rw [h3, h4]
        have hfg : ((f + g : maximalMulDomain m) : Lp ℂ 2 μ) = (f : Lp ℂ 2 μ) + g := rfl
        rw [hfg]
        simp only [Pi.mul_apply, Pi.add_apply, h5, mul_add]
      map_smul' := by
        intro c f
        refine Lp.ext ?_
        filter_upwards [(MemLp.coeFn_toLp (c • f).2), Lp.coeFn_smul c (MemLp.toLp _ f.2),
          MemLp.coeFn_toLp f.2, Lp.coeFn_smul c (f : Lp ℂ 2 μ)] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h2]
        simp only [Pi.smul_apply]
        rw [h3]
        have hcf : ((c • f : maximalMulDomain m) : Lp ℂ 2 μ) = c • (f : Lp ℂ 2 μ) := rfl
        rw [hcf]
        simp only [Pi.mul_apply, Pi.smul_apply, h4, smul_eq_mul]
        ring }

@[simp] theorem maximalMul_domain (m : α → ℂ) :
    (maximalMul (μ := μ) m).domain = maximalMulDomain m := rfl

/-- The value of the maximal multiplication operator is the class of `m · f`. -/
theorem coeFn_maximalMul (m : α → ℂ) (f : (maximalMul (μ := μ) m).domain) :
    ((maximalMul m f : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ] m * ((f : Lp ℂ 2 μ) : α → ℂ) :=
  MemLp.coeFn_toLp f.2

end Brockian.Weyl.MaximalMultiplication

/-
  Brockian/WeylFreeLaplacianCorrected.lean — the correctly normalised spectral
  free Laplacian `F⁻¹ M_{4π²ξ²} F` on `L²(ℝ)`, and the restriction of the
  Schwartz-core free Schrödinger operator into it.

  The declarations up to `spectralFreeLaplacian` are the supplied corpus source.
  The declarations of the corpus module that are phrased in terms of the Cayley
  criterion (`rangeSMulSub`, `essentiallySelfAdjoint_iff`,
  `conjugatePMap_essentiallySelfAdjoint`, and the two essential
  self-adjointness theorems they prove) live in corpus modules that were not
  supplied, and are not reproduced here; nothing below depends on them.
-/
import Brockian.WeylMaximalMultiplication
import Brockian.WeylSchrodingerGate1Final
import Brockian.WeylCayley
import Brockian.FreeLaplacianPlancherel

open MeasureTheory
open scoped InnerProductSpace FourierTransform ENNReal

namespace Brockian.Weyl.FreeLaplacianCorrected

open Brockian.Weyl.Operator
open Brockian.Weyl.Cayley
open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.SchrodingerGate1Final
open Brockian.Weyl.MaximalMultiplication

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- The physical Fourier symbol for `-d^2/dx^2` under Mathlib's
`exp(-2*pi*i*x*xi)` convention. -/
noncomputable def freeSymbol (xi : Real) : Complex :=
  Complex.ofReal (4 * Real.pi ^ 2 * xi ^ 2)

noncomputable def freeSymbolResolventMultiplier (z : Complex) : Real -> Complex :=
  fun xi => (freeSymbol xi - z)⁻¹

theorem freeSymbol_sub_ne_zero {z : Complex} (hz : z.im ≠ 0) (xi : Real) :
    freeSymbol xi - z ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [freeSymbol, Complex.sub_im, Complex.ofReal_im, zero_sub, Complex.zero_im] at hi
  exact hz (neg_eq_zero.mp hi)

theorem continuous_freeSymbolResolventMultiplier {z : Complex} (hz : z.im ≠ 0) :
    Continuous (freeSymbolResolventMultiplier z) := by
  apply Continuous.inv₀
  · unfold freeSymbol
    fun_prop
  · exact freeSymbol_sub_ne_zero hz

theorem norm_freeSymbolResolventMultiplier_le {z : Complex} (hz : z.im ≠ 0)
    (xi : Real) :
    ‖freeSymbolResolventMultiplier z xi‖ ≤ |z.im|⁻¹ := by
  rw [freeSymbolResolventMultiplier, norm_inv]
  have hsim : (freeSymbol xi).im = 0 := Complex.ofReal_im _
  have hnorm : |z.im| ≤ ‖freeSymbol xi - z‖ := by
    calc
      |z.im| = |(freeSymbol xi - z).im| := by
        rw [Complex.sub_im, hsim, zero_sub, abs_neg]
      _ ≤ ‖freeSymbol xi - z‖ := Complex.abs_im_le_norm _
  exact (inv_le_inv₀ (norm_pos_iff.mpr (freeSymbol_sub_ne_zero hz xi))
    (abs_pos.mpr hz)).2 hnorm

theorem freeSymbolResolventMultiplier_memLp_top {z : Complex} (hz : z.im ≠ 0) :
    MemLp (freeSymbolResolventMultiplier z) ∞ (volume : Measure Real) := by
  apply memLp_top_of_bound
    (continuous_freeSymbolResolventMultiplier hz).aestronglyMeasurable |z.im|⁻¹
  exact Filter.Eventually.of_forall (norm_freeSymbolResolventMultiplier_le hz)

theorem freeSymbol_resolvent_inverse {z : Complex} (hz : z.im ≠ 0) (xi : Real) :
    (freeSymbol xi - z) * freeSymbolResolventMultiplier z xi = 1 := by
  exact mul_inv_cancel₀ (freeSymbol_sub_ne_zero hz xi)

/-- Maximal multiplication by the correctly normalized free symbol. -/
noncomputable def freeSymbolMaximal : L2R →ₗ.[Complex] L2R :=
  maximalMul (μ := (volume : Measure Real)) freeSymbol

noncomputable def freeSymbolMulSchwartz :
    SchwartzMap Real Complex →L[Complex] SchwartzMap Real Complex :=
  SchwartzMap.smulLeftCLM Complex
    (fun xi : Real => (4 * Real.pi ^ 2 * xi ^ 2 : Complex))

@[simp] theorem freeSymbolMulSchwartz_apply (f : SchwartzMap Real Complex) (xi : Real) :
    freeSymbolMulSchwartz f xi = freeSymbol xi * f xi := by
  rw [freeSymbolMulSchwartz]
  simpa [freeSymbol, Complex.ofReal_mul, Complex.ofReal_pow, smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply
      (show (fun xi : Real => (4 * Real.pi ^ 2 * xi ^ 2 : Complex)).HasTemperateGrowth by
        fun_prop) f xi

theorem schwartzToL2_mem_freeSymbolMaximal_domain (f : SchwartzMap Real Complex) :
    schwartzToL2 f ∈ freeSymbolMaximal.domain := by
  change MemLp (freeSymbol * (schwartzToL2 f : Real -> Complex)) 2 volume
  have hm : MemLp (freeSymbolMulSchwartz f : Real -> Complex) 2 volume :=
    (freeSymbolMulSchwartz f).memLp 2 volume
  refine hm.ae_eq ?_
  filter_upwards [coeFn_schwartzToL2 f] with xi hxi
  simp only [Pi.mul_apply, freeSymbolMulSchwartz_apply]
  rw [hxi]

theorem freeSymbolMaximal_dense :
    Dense (freeSymbolMaximal.domain : Set L2R) := by
  apply freeSchrodingerPMap_dense.mono
  intro u hu
  rw [freeSchrodingerPMap_domain] at hu
  obtain ⟨f, rfl⟩ := hu
  exact schwartzToL2_mem_freeSymbolMaximal_domain f

theorem freeSymbolMaximal_isSymmetric : IsSymmetric freeSymbolMaximal := by
  change IsSymmetric (maximalMul (μ := (volume : Measure Real)) freeSymbol)
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [coeFn_maximalMul freeSymbol f, coeFn_maximalMul freeSymbol g]
      with xi hf hg
  simp only [hf, hg, Pi.mul_apply, freeSymbol]
  rw [RCLike.inner_apply, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
  ring

/-- The normalized spectral free Laplacian `F^{-1} M_{4*pi^2*xi^2} F`. -/
noncomputable def spectralFreeLaplacian : L2R →ₗ.[Complex] L2R :=
  conjugatePMap Brockian.FreeLaplacianPlancherel.fourierL2.symm freeSymbolMaximal

/-! ### The Schwartz core sits inside the spectral free Laplacian -/

/-- The Fourier transform of the second derivative of a Schwartz function:
`𝓕 (f″)(ξ) = -4π²ξ² 𝓕 f(ξ)`. -/
theorem fourier_deriv_deriv_schwartz (f : SchwartzMap Real Complex) (xi : Real) :
    𝓕 (deriv (deriv (⇑f))) xi = -(freeSymbol xi) * 𝓕 (⇑f) xi := by
  have hd1 : (⇑(SchwartzMap.derivCLM Complex Complex f) : Real → Complex) = deriv ⇑f :=
    funext fun y => SchwartzMap.derivCLM_apply Complex f y
  set g := SchwartzMap.derivCLM Complex Complex f with hg
  have hd2 : (⇑(SchwartzMap.derivCLM Complex Complex g) : Real → Complex) = deriv ⇑g :=
    funext fun y => SchwartzMap.derivCLM_apply Complex g y
  have h1 : 𝓕 (deriv ⇑f) = fun xi : Real => (2 * Real.pi * Complex.I * xi) • 𝓕 (⇑f) xi :=
    Real.fourier_deriv f.integrable f.differentiable (by rw [← hd1]; exact g.integrable)
  have h2 : 𝓕 (deriv (deriv ⇑f))
      = fun xi : Real => (2 * Real.pi * Complex.I * xi) • 𝓕 (deriv ⇑f) xi := by
    rw [← hd1]
    exact Real.fourier_deriv g.integrable g.differentiable
      (by rw [← hd2]; exact (SchwartzMap.derivCLM Complex Complex g).integrable)
  rw [h2, h1, freeSymbol]
  push_cast
  simp only [smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

/-- The Fourier transform turns `-d²/dx²` on the Schwartz core into
multiplication by the free symbol. -/
theorem fourier_neg_D2_eq (f : SchwartzMap Real Complex) :
    𝓕 (-(D2 f)) = freeSymbolMulSchwartz (𝓕 f) := by
  have hneg : 𝓕 (-(D2 f)) = -(𝓕 (D2 f)) := by
    rw [← SchwartzMap.fourierTransformCLM_apply Complex,
      ← SchwartzMap.fourierTransformCLM_apply Complex, map_neg]
  have hD2 : (⇑(D2 f) : Real → Complex) = deriv (deriv ⇑f) := funext fun x => D2_apply f x
  ext xi
  rw [hneg, freeSymbolMulSchwartz_apply, SchwartzMap.neg_apply,
    SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, hD2, fourier_deriv_deriv_schwartz]
  ring

/-- The inverse Fourier transform of `freeSymbol · 𝓕 f` is `-f″`. -/
theorem fourierInv_freeSymbolMul_eq (f : SchwartzMap Real Complex) :
    𝓕⁻ (freeSymbolMulSchwartz (𝓕 f)) = -(D2 f) := by
  rw [← fourier_neg_D2_eq f, FourierTransform.fourierInv_fourier_eq]

/-- Multiplication by the free symbol on the image of the Schwartz core. -/
theorem freeSymbolMaximal_schwartz (g : SchwartzMap Real Complex)
    (x : freeSymbolMaximal.domain) (hx : (x : L2R) = schwartzToL2 g) :
    freeSymbolMaximal x = schwartzToL2 (freeSymbolMulSchwartz g) := by
  have h1 : ((freeSymbolMaximal x : L2R) : Real → Complex)
      =ᵐ[volume] freeSymbol * ((x : L2R) : Real → Complex) := coeFn_maximalMul freeSymbol x
  refine Lp.ext ?_
  filter_upwards [h1, coeFn_schwartzToL2 (freeSymbolMulSchwartz g),
    hx ▸ coeFn_schwartzToL2 g] with xi h1 h2 h3
  rw [h1, h2, Pi.mul_apply, h3, freeSymbolMulSchwartz_apply]

/-- Every Schwartz class lies in the domain of the spectral free Laplacian. -/
theorem schwartzToL2_mem_spectralFreeLaplacian_domain (f : SchwartzMap Real Complex) :
    schwartzToL2 f ∈ spectralFreeLaplacian.domain := by
  refine ⟨Brockian.FreeLaplacianPlancherel.fourierL2 (schwartzToL2 f), ?_, ?_⟩
  · rw [Brockian.FreeLaplacianPlancherel.fourierL2_schwartzToL2]
    exact schwartzToL2_mem_freeSymbolMaximal_domain _
  · exact (Brockian.FreeLaplacianPlancherel.fourierL2).symm_apply_apply _

/-- The spectral free Laplacian acts on the Schwartz core as `-d²/dx²`. -/
theorem spectralFreeLaplacian_schwartz (f : SchwartzMap Real Complex)
    (y : spectralFreeLaplacian.domain) (hy : (y : L2R) = schwartzToL2 f) :
    spectralFreeLaplacian y = -(schwartzToL2 (D2 f)) := by
  have hmem : schwartzToL2 (𝓕 f) ∈ freeSymbolMaximal.domain :=
    schwartzToL2_mem_freeSymbolMaximal_domain _
  have hval : spectralFreeLaplacian y
      = Brockian.FreeLaplacianPlancherel.fourierL2.symm
          (freeSymbolMaximal ⟨schwartzToL2 (𝓕 f), hmem⟩) := by
    refine conjugatePMap_apply _ freeSymbolMaximal ⟨schwartzToL2 (𝓕 f), hmem⟩ y ?_
    rw [hy]
    show schwartzToL2 f
      = Brockian.FreeLaplacianPlancherel.fourierL2.symm (schwartzToL2 (𝓕 f))
    rw [← Brockian.FreeLaplacianPlancherel.fourierL2_schwartzToL2,
      LinearIsometryEquiv.symm_apply_apply]
  rw [hval, freeSymbolMaximal_schwartz (𝓕 f) _ rfl,
    Brockian.FreeLaplacianPlancherel.fourierL2_symm_schwartzToL2,
    fourierInv_freeSymbolMul_eq f, map_neg]

theorem freeSchrodingerPMap_le_spectralFreeLaplacian :
    freeSchrodingerPMap ≤ spectralFreeLaplacian := by
  constructor
  · intro u hu
    obtain ⟨f, rfl⟩ := (LinearMap.mem_range).mp hu
    exact schwartzToL2_mem_spectralFreeLaplacian_domain f
  · intro x y hxy
    obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
    have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
      Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
    have hyc : (y : L2R) = schwartzToL2 f := by rw [← hxy, ← hf]
    rw [hxe, freeSchrodingerPMap_toFun_ofInjective, freeCoreMap_apply,
      spectralFreeLaplacian_schwartz f y hyc]

end Brockian.Weyl.FreeLaplacianCorrected

/-
  Brockian/WeylSchrodingerMinimal.lean — the Schwartz core embedded in `L²(ℝ)`,
  the second-derivative operator on that core, and Schwartz integration by parts.

  This file reproduces, verbatim, the part of the supplied corpus module
  `Brockian.WeylSchrodingerMinimal` whose dependencies are Mathlib only, namely
  everything up to and including `kinetic_symm`:

    `H2`, `schwartzToL2`, `schwartzToL2_apply`, `coeFn_schwartzToL2`,
    `schwartzToL2_injective`, `D2`, `D2_apply`, `Lconj`, `Lconj_apply`,
    `schwartz_ibp1`, `schwartz_ibp2`, `inner_toLp`, `kinetic_symm`.

  The remaining declarations of that corpus module (the bounded potential term
  `potentialMulCLM`, `coreMap`, `schrodingerPMap` and their consequences) are
  phrased in terms of `mulLpCLM` / `isSelfAdjoint_mulLpCLM` / the
  `DeficiencyRepresentsODE` bridge, which live in corpus modules
  (`Brockian.SpectralGate1`, `Brockian.WeylBridge`,
  `Brockian.WeylSchrodingerESA`) that were not supplied here; they are therefore
  not reproduced. None of them is used downstream in this development.
-/
import Mathlib
import Brockian.WeylOperator

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace
open Brockian.Weyl.Operator

namespace Brockian.Weyl.SchrodingerMinimal

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-! ### The Schwartz core embedded in L² -/

/-- **The Schwartz core, embedded in `L²`.** The ℂ-linear map sending a Schwartz
function to its `L²` class. Its range is the (dense) domain of the minimal
operator. -/
noncomputable def schwartzToL2 : SchwartzMap ℝ ℂ →ₗ[ℂ] H2 :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap

theorem schwartzToL2_apply (f : SchwartzMap ℝ ℂ) :
    schwartzToL2 f = f.toLp 2 (volume : Measure ℝ) := rfl

theorem coeFn_schwartzToL2 (a : SchwartzMap ℝ ℂ) :
    (schwartzToL2 a : ℝ → ℂ) =ᵐ[volume] a := by
  rw [schwartzToL2_apply]
  exact a.coeFn_toLp 2 (volume : Measure ℝ)

/-- The Schwartz embedding into `L²` is injective (two Schwartz functions with the
same `L²` class agree a.e., hence everywhere by continuity). -/
theorem schwartzToL2_injective : Function.Injective schwartzToL2 := by
  intro a b hab
  have hae : (a : ℝ → ℂ) =ᵐ[volume] b := by
    calc (a : ℝ → ℂ) =ᵐ[volume] (schwartzToL2 a : ℝ → ℂ) := (coeFn_schwartzToL2 a).symm
      _ = (schwartzToL2 b : ℝ → ℂ) := by rw [hab]
      _ =ᵐ[volume] b := coeFn_schwartzToL2 b
  have hEq : (a : ℝ → ℂ) = b := (a.continuous.ae_eq_iff_eq volume b.continuous).mp hae
  exact DFunLike.coe_injective hEq

/-! ### The kinetic term: `−d²/dx²` and integration by parts -/

/-- The second-derivative operator on Schwartz space. -/
noncomputable def D2 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ).comp (SchwartzMap.derivCLM ℂ ℂ)

theorem D2_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) : D2 f x = deriv (deriv f) x := by
  have hc : (⇑(SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) = deriv (⇑f) :=
    funext fun y => SchwartzMap.derivCLM_apply ℂ f y
  simp only [D2, ContinuousLinearMap.comp_apply, SchwartzMap.derivCLM_apply, hc]

/-- The ℝ-bilinear pairing `(a, b) ↦ conj a · b` as a continuous linear map,
used to feed Mathlib's Schwartz integration-by-parts lemma. -/
noncomputable def Lconj : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ).comp (RCLike.conjCLE (K := ℂ)).toContinuousLinearMap

theorem Lconj_apply (a b : ℂ) : Lconj a b = conj a * b := by
  simp only [Lconj, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    RCLike.conjCLE_apply, ContinuousLinearMap.mul_apply']

/-- **Integration by parts (once) for Schwartz functions.**
`∫ conj(f)·g′ = −∫ conj(f′)·g`. -/
theorem schwartz_ibp1 (F G : SchwartzMap ℝ ℂ) :
    ∫ x, conj (F x) * deriv G x = -∫ x, conj (deriv F x) * G x := by
  have h := SchwartzMap.integral_bilinear_deriv_right_eq_neg_left F G Lconj
  simpa only [Lconj_apply] using h

/-- **Double integration by parts for Schwartz functions.**
`∫ conj(f″)·g = ∫ conj(f)·g″`. Boundary terms vanish by rapid decay. This is the
analytic heart of the symmetry of `−d²/dx²`. -/
theorem schwartz_ibp2 (f g : SchwartzMap ℝ ℂ) :
    ∫ x, conj (deriv (deriv f) x) * g x = ∫ x, conj (f x) * deriv (deriv g) x := by
  have hcf : (⇑(SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) = deriv (⇑f) :=
    funext fun y => SchwartzMap.derivCLM_apply ℂ f y
  have hcg : (⇑(SchwartzMap.derivCLM ℂ ℂ g) : ℝ → ℂ) = deriv (⇑g) :=
    funext fun y => SchwartzMap.derivCLM_apply ℂ g y
  have hA := schwartz_ibp1 f (SchwartzMap.derivCLM ℂ ℂ g)
  have hB := schwartz_ibp1 (SchwartzMap.derivCLM ℂ ℂ f) g
  rw [hcg] at hA
  rw [hcf] at hB
  linear_combination hB - hA

/-- The `L²` inner product of two Schwartz classes as an integral. -/
theorem inner_toLp (a b : SchwartzMap ℝ ℂ) :
    ⟪schwartzToL2 a, schwartzToL2 b⟫_ℂ = ∫ x, conj (a x) * b x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_schwartzToL2 a, coeFn_schwartzToL2 b] with x hax hbx
  rw [hax, hbx, RCLike.inner_apply']

/-- **Symmetry of the kinetic term.** `⟪−f″, g⟫ = ⟪f, −g″⟫` on the Schwartz core
(here without the sign, `⟪f″, g⟫ = ⟪f, g″⟫`). -/
theorem kinetic_symm (f g : SchwartzMap ℝ ℂ) :
    ⟪schwartzToL2 (D2 f), schwartzToL2 g⟫_ℂ = ⟪schwartzToL2 f, schwartzToL2 (D2 g)⟫_ℂ := by
  rw [inner_toLp, inner_toLp]
  simp only [D2_apply]
  exact schwartz_ibp2 f g

end Brockian.Weyl.SchrodingerMinimal

/-
  Brockian/FreeLaplacianPlancherel.lean — the Plancherel unitary on `L²(ℝ)`.

  The corpus module of this name was not supplied; this file provides the object
  `Brockian.FreeLaplacianPlancherel.fourierL2` used by
  `Brockian.WeylFreeLaplacianCorrected`: the Fourier transform as a unitary of
  `L²(ℝ)`, taken from Mathlib's `MeasureTheory.Lp.fourierTransformₗᵢ`, together
  with the two facts that it agrees with the Schwartz Fourier transform on the
  Schwartz core.
-/
import Mathlib
import Brockian.WeylSchrodingerMinimal

open MeasureTheory SchwartzMap
open scoped FourierTransform

namespace Brockian.FreeLaplacianPlancherel

open Brockian.Weyl.SchrodingerMinimal

/-- **The Plancherel unitary** `𝓕 : L²(ℝ) ≃ₗᵢ[ℂ] L²(ℝ)`. -/
noncomputable def fourierL2 : H2 ≃ₗᵢ[ℂ] H2 := MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

/-- On the Schwartz core the `L²` Fourier transform is the Schwartz Fourier
transform. -/
theorem fourierL2_schwartzToL2 (f : SchwartzMap ℝ ℂ) :
    fourierL2 (schwartzToL2 f) = schwartzToL2 (𝓕 f) := by
  show MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (f.toLp 2 (volume : Measure ℝ))
      = (𝓕 f).toLp 2 (volume : Measure ℝ)
  exact SchwartzMap.toLp_fourier_eq f

/-- The inverse Plancherel unitary on the Schwartz core. -/
theorem fourierL2_symm_schwartzToL2 (f : SchwartzMap ℝ ℂ) :
    fourierL2.symm (schwartzToL2 f) = schwartzToL2 (𝓕⁻ f) := by
  show (MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ).symm (f.toLp 2 (volume : Measure ℝ))
      = (𝓕⁻ f).toLp 2 (volume : Measure ℝ)
  exact SchwartzMap.toLp_fourierInv_eq f

end Brockian.FreeLaplacianPlancherel

