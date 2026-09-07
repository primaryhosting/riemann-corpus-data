/-
  Brockian/WeylHarmonicOscillator.lean

  A concrete confining Schrodinger operator on the Schwartz core:

      H f = -f'' + x^2 f.

  This module constructs the unbounded operator as a `LinearPMap` on `L2(R)`,
  proves that its Schwartz domain is dense, and proves symmetry by combining
  Schwartz integration by parts with the reality of the quadratic multiplier.

  It does not claim essential self-adjointness, compact resolvent, or a discrete
  spectrum.  Those are the next analytic steps.
-/
import Brockian.WeylSchrodingerMinimal
import Brockian.ConfiningSpectralShape

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator
open Brockian.Weyl.SchrodingerMinimal
open Brockian.Weyl.Confining
open Brockian.Weyl.ConfiningShape

/- A local alias avoids ambiguity when AXLE flattens imports that export other
`H2` abbreviations into the same source file. -/
noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-- Multiplication by `x^2` preserves Schwartz space. -/
noncomputable def quadraticMulSchwartz :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (x ^ 2 : ℂ))

theorem quadratic_hasTemperateGrowth :
    (fun x : ℝ => (x ^ 2 : ℂ)).HasTemperateGrowth := by
  fun_prop

@[simp] theorem quadraticMulSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    quadraticMulSchwartz f x = (x ^ 2 : ℂ) * f x := by
  rw [quadraticMulSchwartz]
  simpa [smul_eq_mul] using
    SchwartzMap.smulLeftCLM_apply_apply quadratic_hasTemperateGrowth f x

/-- The harmonic-oscillator action on Schwartz functions. -/
noncomputable def oscillatorSchwartz :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  -D2 + quadraticMulSchwartz

@[simp] theorem oscillatorSchwartz_apply (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    oscillatorSchwartz f x = -deriv (deriv f) x + (x ^ 2 : ℂ) * f x := by
  simp [oscillatorSchwartz, D2_apply]

/-- The harmonic-oscillator core action, valued in `L2(R)`. -/
noncomputable def oscillatorCoreMap : SchwartzMap ℝ ℂ →ₗ[ℂ] L2R :=
  schwartzToL2.comp oscillatorSchwartz.toLinearMap

@[simp] theorem oscillatorCoreMap_apply (f : SchwartzMap ℝ ℂ) :
    oscillatorCoreMap f = schwartzToL2 (oscillatorSchwartz f) := rfl

theorem oscillatorCoreMap_expanded (f : SchwartzMap ℝ ℂ) :
    oscillatorCoreMap f =
      -(schwartzToL2 (D2 f)) + schwartzToL2 (quadraticMulSchwartz f) := by
  simp [oscillatorCoreMap, oscillatorSchwartz]

/-- The minimal harmonic oscillator `-d^2/dx^2 + x^2` on the Schwartz core. -/
noncomputable def harmonicOscillatorPMap : L2R →ₗ.[ℂ] L2R where
  domain := LinearMap.range schwartzToL2
  toFun := oscillatorCoreMap.comp
    (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap

@[simp] theorem harmonicOscillatorPMap_domain :
    harmonicOscillatorPMap.domain = LinearMap.range schwartzToL2 := rfl

/-- Exact action on an embedded Schwartz function. -/
theorem harmonicOscillatorPMap_toFun_ofInjective (f : SchwartzMap ℝ ℂ) :
    harmonicOscillatorPMap
        (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
      = oscillatorCoreMap f := by
  show oscillatorCoreMap.comp
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
    = oscillatorCoreMap f
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.symm_apply_apply]

/-- The harmonic oscillator has the same dense Schwartz domain as the free core. -/
theorem harmonicOscillatorPMap_dense :
    Dense (harmonicOscillatorPMap.domain : Set L2R) := by
  have hfun : (schwartzToL2 : SchwartzMap ℝ ℂ → L2R)
      = (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) := by
    funext f
    rw [schwartzToL2_apply, SchwartzMap.toLpCLM_apply]
  rw [harmonicOscillatorPMap_domain, LinearMap.coe_range, hfun]
  exact SchwartzMap.denseRange_toLpCLM (by norm_num)

/-- Multiplication by the real function `x^2` is symmetric on the Schwartz core. -/
theorem quadraticMul_symm (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (schwartzToL2 (quadraticMulSchwartz f)) (schwartzToL2 g) =
      inner ℂ (schwartzToL2 f) (schwartzToL2 (quadraticMulSchwartz g)) := by
  rw [inner_toLp, inner_toLp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [quadraticMulSchwartz_apply, map_mul, map_pow, Complex.conj_ofReal]
  ring

/-- The full oscillator action is symmetric on Schwartz functions. -/
theorem oscillatorCoreMap_symm (f g : SchwartzMap ℝ ℂ) :
    inner ℂ (oscillatorCoreMap f) (schwartzToL2 g) =
      inner ℂ (schwartzToL2 f) (oscillatorCoreMap g) := by
  rw [oscillatorCoreMap_expanded, oscillatorCoreMap_expanded,
    inner_add_left, inner_add_right, inner_neg_left, inner_neg_right,
    kinetic_symm f g, quadraticMul_symm f g]

/-- The concrete minimal harmonic oscillator is symmetric. -/
theorem harmonicOscillatorPMap_isSymmetric :
    IsSymmetric harmonicOscillatorPMap := by
  intro x y
  obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
  obtain ⟨g, hg⟩ := (LinearMap.mem_range).mp y.2
  have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
  have hye : y = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective g :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hg.symm)
  rw [hxe, hye, harmonicOscillatorPMap_toFun_ofInjective,
    harmonicOscillatorPMap_toFun_ofInjective, LinearEquiv.ofInjective_apply,
    LinearEquiv.ofInjective_apply]
  exact oscillatorCoreMap_symm f g

/-- The concrete operator is paired with the already-proved confining shape of `x^2`. -/
theorem harmonicOscillator_confining_shape :
    CompactResolventShape (fun x : ℝ => x ^ 2) :=
  quadratic_compactResolventShape

/-- The machine-checked part of the harmonic-oscillator candidate: a dense,
symmetric unbounded core together with a continuous confining potential. -/
theorem harmonicOscillator_core_package :
    Dense (harmonicOscillatorPMap.domain : Set L2R) ∧
      IsSymmetric harmonicOscillatorPMap ∧
      CompactResolventShape (fun x : ℝ => x ^ 2) :=
  ⟨harmonicOscillatorPMap_dense, harmonicOscillatorPMap_isSymmetric,
    harmonicOscillator_confining_shape⟩

end Brockian.Weyl.HarmonicOscillator
