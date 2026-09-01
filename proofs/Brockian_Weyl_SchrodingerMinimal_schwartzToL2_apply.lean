/-
  Corpus declarations (reproduced verbatim from the Brockian modules, restricted to
  what is needed) together with the new bridge theorem

      freeSchrodingerPMap ≤ spectralFreeLaplacian.
-/
import Mathlib

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace ENNReal

/-! ## From `Brockian/WeylSchrodingerMinimal.lean` -/

namespace Brockian.Weyl.SchrodingerMinimal

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- **The Schwartz core, embedded in `L²`.** -/
noncomputable def schwartzToL2 : SchwartzMap ℝ ℂ →ₗ[ℂ] H2 :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap

theorem schwartzToL2_apply (f : SchwartzMap ℝ ℂ) :
    schwartzToL2 f = f.toLp 2 (volume : Measure ℝ) := rfl

theorem coeFn_schwartzToL2 (a : SchwartzMap ℝ ℂ) :
    (schwartzToL2 a : ℝ → ℂ) =ᵐ[volume] a := by
  rw [schwartzToL2_apply]
  exact a.coeFn_toLp 2 (volume : Measure ℝ)

theorem schwartzToL2_injective : Function.Injective schwartzToL2 := by
  intro a b hab
  have hae : (a : ℝ → ℂ) =ᵐ[volume] b := by
    calc (a : ℝ → ℂ) =ᵐ[volume] (schwartzToL2 a : ℝ → ℂ) := (coeFn_schwartzToL2 a).symm
      _ = (schwartzToL2 b : ℝ → ℂ) := by rw [hab]
      _ =ᵐ[volume] b := coeFn_schwartzToL2 b
  have hEq : (a : ℝ → ℂ) = b := (a.continuous.ae_eq_iff_eq volume b.continuous).mp hae
  exact DFunLike.coe_injective hEq

/-- The second-derivative operator on Schwartz space. -/
noncomputable def D2 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ).comp (SchwartzMap.derivCLM ℂ ℂ)

theorem D2_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) : D2 f x = deriv (deriv f) x := by
  have hc : (⇑(SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) = deriv (⇑f) :=
    funext fun y => SchwartzMap.derivCLM_apply ℂ f y
  simp only [D2, ContinuousLinearMap.comp_apply, SchwartzMap.derivCLM_apply, hc]

end Brockian.Weyl.SchrodingerMinimal

/-! ## From `Brockian/WeylSchrodingerGate1Final.lean` -/

namespace Brockian.Weyl.SchrodingerGate1Final

open Brockian.Weyl.SchrodingerMinimal

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- The free kinetic action `f |-> -f''` on Schwartz functions, valued in L2. -/
noncomputable def freeCoreMap : SchwartzMap ℝ ℂ →ₗ[ℂ] L2R :=
  -(schwartzToL2.comp
    (D2 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ).toLinearMap)

@[simp] theorem freeCoreMap_apply (f : SchwartzMap ℝ ℂ) :
    freeCoreMap f = -(schwartzToL2 (D2 f)) := by
  simp [freeCoreMap]

/-- The genuine minimal free Laplacian `-d^2/dx^2` on the Schwartz core. -/
noncomputable def freeSchrodingerPMap : L2R →ₗ.[ℂ] L2R where
  domain := LinearMap.range schwartzToL2
  toFun := freeCoreMap.comp
    (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap

@[simp] theorem freeSchrodingerPMap_domain :
    freeSchrodingerPMap.domain = LinearMap.range schwartzToL2 :=
  rfl

/-- The free operator acts as `-f''` on an embedded Schwartz function. -/
theorem freeSchrodingerPMap_toFun_ofInjective (f : SchwartzMap ℝ ℂ) :
    freeSchrodingerPMap
        (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
      = freeCoreMap f := by
  show freeCoreMap.comp
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
    = freeCoreMap f
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

end Brockian.Weyl.SchrodingerGate1Final

/-! ## From `Brockian/WeylMaximalMultiplication.lean` -/

namespace Brockian.Weyl.MaximalMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

noncomputable def maximalMulDomain (g : α → ℂ) :
    Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {f | MemLp (g * (f : α → ℂ)) 2 μ}
  zero_mem' := by
    refine (MemLp.zero' : MemLp (0 : α → ℂ) 2 μ).ae_eq ?_
    filter_upwards [Lp.coeFn_zero (α := α) (E := ℂ) (p := 2) (μ := μ)] with x hx
    simp only [Pi.mul_apply]
    rw [hx]
    simp
  add_mem' := by
    intro f h hf hh
    refine (hf.add hh).ae_eq ?_
    filter_upwards [Lp.coeFn_add f h] with x hx
    simp only [Pi.add_apply, Pi.mul_apply] at hx ⊢
    rw [hx]
    ring
  smul_mem' := by
    intro c f hf
    refine (hf.const_smul c).ae_eq ?_
    filter_upwards [Lp.coeFn_smul c f] with x hx
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at hx ⊢
    rw [hx]
    ring

noncomputable def maximalMulValue (g : α → ℂ)
    (f : maximalMulDomain (μ := μ) g) : Lp ℂ 2 μ :=
  (show MemLp (g * ((f : Lp ℂ 2 μ) : α → ℂ)) 2 μ from f.2).toLp
    (g * ((f : Lp ℂ 2 μ) : α → ℂ))

theorem coeFn_maximalMulValue (g : α → ℂ)
    (f : maximalMulDomain (μ := μ) g) :
    (maximalMulValue g f : α → ℂ) =ᵐ[μ]
      g * ((f : Lp ℂ 2 μ) : α → ℂ) :=
  MemLp.coeFn_toLp _

noncomputable def maximalMul (g : α → ℂ) :
    Lp ℂ 2 μ →ₗ.[ℂ] Lp ℂ 2 μ where
  domain := maximalMulDomain (μ := μ) g
  toFun :=
    { toFun := maximalMulValue g
      map_add' := by
        intro f h
        apply Lp.ext
        have ein : (((f + h : maximalMulDomain (μ := μ) g) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
            ((f : Lp ℂ 2 μ) : α → ℂ) + ((h : Lp ℂ 2 μ) : α → ℂ) := by
          simpa using Lp.coeFn_add (f : Lp ℂ 2 μ) (h : Lp ℂ 2 μ)
        filter_upwards [coeFn_maximalMulValue g (f + h), coeFn_maximalMulValue g f,
          coeFn_maximalMulValue g h,
          Lp.coeFn_add (maximalMulValue g f) (maximalMulValue g h), ein]
            with x e0 e1 e2 esum einx
        simp only [Pi.add_apply, Pi.mul_apply] at e0 e1 e2 esum einx ⊢
        rw [e0, einx, esum, e1, e2]
        ring
      map_smul' := by
        intro c f
        apply Lp.ext
        have ein : (((c • f : maximalMulDomain (μ := μ) g) : Lp ℂ 2 μ) : α → ℂ) =ᵐ[μ]
            c • ((f : Lp ℂ 2 μ) : α → ℂ) := by
          simpa using Lp.coeFn_smul c (f : Lp ℂ 2 μ)
        filter_upwards [coeFn_maximalMulValue g (c • f), coeFn_maximalMulValue g f,
          Lp.coeFn_smul c (maximalMulValue g f), ein] with x e0 e1 esr einx
        simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, RingHom.id_apply]
          at e0 e1 esr einx ⊢
        rw [e0, einx, esr, e1]
        ring }

@[simp] theorem maximalMul_domain (g : α → ℂ) :
    (maximalMul (μ := μ) g).domain = maximalMulDomain (μ := μ) g := rfl

theorem coeFn_maximalMul (g : α → ℂ)
    (f : (maximalMul (μ := μ) g).domain) :
    (maximalMul (μ := μ) g f : α → ℂ) =ᵐ[μ]
      g * ((f : Lp ℂ 2 μ) : α → ℂ) :=
  coeFn_maximalMulValue g f

namespace Plancherel

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

noncomputable def conjugateDomainEmbedding (U : H ≃ₗᵢ[ℂ] K)
    (T : H →ₗ.[ℂ] H) : T.domain →ₗ[ℂ] K :=
  U.toLinearMap.comp T.domain.subtype

theorem conjugateDomainEmbedding_injective (U : H ≃ₗᵢ[ℂ] K)
    (T : H →ₗ.[ℂ] H) : Function.Injective (conjugateDomainEmbedding U T) := by
  intro x y hxy
  apply Subtype.ext
  exact U.injective hxy

noncomputable def conjugateDomainEquiv (U : H ≃ₗᵢ[ℂ] K)
    (T : H →ₗ.[ℂ] H) :
    T.domain ≃ₗ[ℂ] LinearMap.range (conjugateDomainEmbedding U T) :=
  LinearEquiv.ofInjective (conjugateDomainEmbedding U T)
    (conjugateDomainEmbedding_injective U T)

noncomputable def conjugatePMap (U : H ≃ₗᵢ[ℂ] K)
    (T : H →ₗ.[ℂ] H) : K →ₗ.[ℂ] K where
  domain := LinearMap.range (conjugateDomainEmbedding U T)
  toFun := (U.toLinearMap.comp T.toFun).comp
    (conjugateDomainEquiv U T).symm.toLinearMap

@[simp] theorem conjugatePMap_domain (U : H ≃ₗᵢ[ℂ] K)
    (T : H →ₗ.[ℂ] H) :
    (conjugatePMap U T).domain = T.domain.map U.toLinearMap := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.property, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem conjugatePMap_apply (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H)
    (x : T.domain) :
    conjugatePMap U T (conjugateDomainEquiv U T x) = U (T x) := by
  simp [conjugatePMap, conjugateDomainEquiv]

end Plancherel

end Brockian.Weyl.MaximalMultiplication

/-! ## From `Brockian/FreeLaplacianPlancherel.lean` -/

namespace Brockian.FreeLaplacianPlancherel

open MeasureTheory

/-- `L²(ℝ; ℂ)` with the Lebesgue `volume` measure. -/
noncomputable abbrev L2R : Type := Lp (α := ℝ) ℂ 2

/-- **The Fourier transform on `L²(ℝ; ℂ)` as a concrete unitary.** -/
noncomputable def fourierL2 : L2R ≃ₗᵢ[ℂ] L2R :=
  MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ

theorem fourierL2_norm_map (f : L2R) : ‖fourierL2 f‖ = ‖f‖ :=
  (fourierL2).norm_map f

theorem fourierL2_inner_map (f g : L2R) :
    (inner ℂ (fourierL2 f) (fourierL2 g)) = inner ℂ f g :=
  (fourierL2).inner_map_map f g

end Brockian.FreeLaplacianPlancherel

/-! ## From `Brockian/WeylFreeLaplacianCorrected.lean` -/

namespace Brockian.Weyl.FreeLaplacianCorrected

open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.SchrodingerGate1Final
open Brockian.Weyl.MaximalMultiplication
open Brockian.Weyl.MaximalMultiplication.Plancherel

noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- The physical Fourier symbol for `-d^2/dx^2` under Mathlib's
`exp(-2*pi*i*x*xi)` convention. -/
noncomputable def freeSymbol (xi : Real) : Complex :=
  Complex.ofReal (4 * Real.pi ^ 2 * xi ^ 2)

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

/-- The normalized spectral free Laplacian `F^{-1} M_{4*pi^2*xi^2} F`. -/
noncomputable def spectralFreeLaplacian : L2R →ₗ.[Complex] L2R :=
  conjugatePMap Brockian.FreeLaplacianPlancherel.fourierL2.symm freeSymbolMaximal

/-! ### The bridge theorem -/

open FourierTransform in
/-- The Fourier transform of a Schwartz function, as a Schwartz function. -/
private noncomputable def fourierSchwartz (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.fourierTransformCLM ℂ f

open FourierTransform in
private theorem coeFn_fourierSchwartz (f : SchwartzMap ℝ ℂ) :
    (⇑(fourierSchwartz f) : ℝ → ℂ) = 𝓕 (⇑f) := by
  rw [fourierSchwartz, SchwartzMap.fourierTransformCLM_apply]
  exact SchwartzMap.fourier_coe f

open FourierTransform in
/-- The Fourier transform of the second derivative of a Schwartz function is
multiplication by `-(4 π² ξ²)`. -/
private theorem fourier_deriv_deriv (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    𝓕 (deriv (deriv ⇑f)) x = -(4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2) * 𝓕 (⇑f) x := by
  have hc : (⇑(SchwartzMap.derivCLM ℂ ℂ f) : ℝ → ℂ) = deriv (⇑f) :=
    funext fun y => SchwartzMap.derivCLM_apply ℂ f y
  have hc2 : (⇑(SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)) : ℝ → ℂ)
      = deriv (deriv (⇑f)) := by
    rw [funext fun y => SchwartzMap.derivCLM_apply ℂ (SchwartzMap.derivCLM ℂ ℂ f) y, hc]
  have hi1 : Integrable (deriv ⇑f) volume := by
    simpa [hc] using (SchwartzMap.derivCLM ℂ ℂ f).integrable (μ := volume)
  have hi2 : Integrable (deriv (deriv ⇑f)) volume := by
    simpa [hc2] using
      (SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.derivCLM ℂ ℂ f)).integrable (μ := volume)
  have hd1 : Differentiable ℝ (deriv ⇑f) := by
    simpa [hc] using (SchwartzMap.derivCLM ℂ ℂ f).differentiable
  rw [Real.fourier_deriv hi1 hd1 hi2, Real.fourier_deriv f.integrable f.differentiable hi1]
  simp only [smul_eq_mul]
  linear_combination (4 * (Real.pi : ℂ) ^ 2 * (x : ℂ) ^ 2 * 𝓕 (⇑f) x) * Complex.I_sq

/-- Pointwise: the free symbol times `𝓕 f` is `-𝓕 (f'')`. -/
private theorem freeSymbol_mul_fourierSchwartz (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    freeSymbol x * fourierSchwartz f x = -(fourierSchwartz (D2 f) x) := by
  have hD2 : (⇑(D2 f) : ℝ → ℂ) = deriv (deriv (⇑f)) := funext fun y => D2_apply f y
  rw [coeFn_fourierSchwartz, coeFn_fourierSchwartz, hD2, fourier_deriv_deriv f x, freeSymbol]
  push_cast
  ring

/-- The `L²` Fourier transform sends the class of a Schwartz function to the class of its
Fourier transform (Plancherel's unitary agrees with the Schwartz Fourier transform). -/
private theorem fourierL2_schwartzToL2 (f : SchwartzMap ℝ ℂ) :
    Brockian.FreeLaplacianPlancherel.fourierL2 (schwartzToL2 f)
      = schwartzToL2 (fourierSchwartz f) := by
  show MeasureTheory.Lp.fourierTransformₗᵢ ℝ ℂ (schwartzToL2 f) = _
  rw [schwartzToL2_apply, schwartzToL2_apply, fourierSchwartz,
    SchwartzMap.fourierTransformCLM_apply]
  exact SchwartzMap.toLp_fourier_eq f

private theorem fourierL2_symm_schwartzToL2 (f : SchwartzMap ℝ ℂ) :
    Brockian.FreeLaplacianPlancherel.fourierL2.symm (schwartzToL2 (fourierSchwartz f))
      = schwartzToL2 f := by
  rw [← fourierL2_schwartzToL2 f, LinearIsometryEquiv.symm_apply_apply]

/-- Value of a conjugated operator at an element of its domain, described by its
underlying vector. -/
private theorem conjugatePMap_apply_of_coe {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (U : H ≃ₗᵢ[ℂ] K) (T : H →ₗ.[ℂ] H) (x : T.domain) (y : (conjugatePMap U T).domain)
    (hy : (y : K) = U (x : H)) : conjugatePMap U T y = U (T x) := by
  have hy' : y = conjugateDomainEquiv U T x := Subtype.ext hy
  rw [hy', conjugatePMap_apply]

/-- Multiplication by the free symbol turns `𝓕 f` into `-𝓕 (f'')`, at the level of `L²`. -/
private theorem freeSymbolMaximal_apply_fourierSchwartz (f : SchwartzMap ℝ ℂ)
    (v : freeSymbolMaximal.domain) (hv : (v : L2R) = schwartzToL2 (fourierSchwartz f)) :
    freeSymbolMaximal v = -(schwartzToL2 (fourierSchwartz (D2 f))) := by
  apply Lp.ext
  have hmul : (freeSymbolMaximal v : ℝ → ℂ) =ᵐ[volume]
      freeSymbol * ((v : L2R) : ℝ → ℂ) :=
    coeFn_maximalMul (μ := (volume : Measure ℝ)) freeSymbol v
  filter_upwards [hmul, hv ▸ coeFn_schwartzToL2 (fourierSchwartz f),
    Lp.coeFn_neg (schwartzToL2 (fourierSchwartz (D2 f))),
    coeFn_schwartzToL2 (fourierSchwartz (D2 f))] with x e0 e1 e2 e3
  simp only [Pi.mul_apply, Pi.neg_apply] at e0 e1 e2 e3 ⊢
  rw [e0, e1, e2, e3]
  exact freeSymbol_mul_fourierSchwartz f x

theorem freeSchrodingerPMap_le_spectralFreeLaplacian :
    freeSchrodingerPMap ≤ spectralFreeLaplacian := by
  have hdom : ∀ f : SchwartzMap ℝ ℂ,
      schwartzToL2 f ∈ spectralFreeLaplacian.domain := by
    intro f
    rw [spectralFreeLaplacian, conjugatePMap_domain]
    exact ⟨schwartzToL2 (fourierSchwartz f),
      schwartzToL2_mem_freeSymbolMaximal_domain (fourierSchwartz f),
      fourierL2_symm_schwartzToL2 f⟩
  refine ⟨?_, ?_⟩
  · rw [freeSchrodingerPMap_domain]
    rintro u ⟨f, rfl⟩
    exact hdom f
  · rintro x y hxy
    obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
    have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
      Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
    have hyv : (y : L2R) = Brockian.FreeLaplacianPlancherel.fourierL2.symm
        (schwartzToL2 (fourierSchwartz f)) := by
      rw [fourierL2_symm_schwartzToL2 f, hf, hxy]
    let v : freeSymbolMaximal.domain :=
      ⟨schwartzToL2 (fourierSchwartz f),
        schwartzToL2_mem_freeSymbolMaximal_domain (fourierSchwartz f)⟩
    have hvy : spectralFreeLaplacian y
        = Brockian.FreeLaplacianPlancherel.fourierL2.symm (freeSymbolMaximal v) :=
      conjugatePMap_apply_of_coe _ _ v y hyv
    rw [hxe, freeSchrodingerPMap_toFun_ofInjective, freeCoreMap_apply, hvy,
      freeSymbolMaximal_apply_fourierSchwartz f v rfl, map_neg,
      fourierL2_symm_schwartzToL2 (D2 f)]

end Brockian.Weyl.FreeLaplacianCorrected

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

