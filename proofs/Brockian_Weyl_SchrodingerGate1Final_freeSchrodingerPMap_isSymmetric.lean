/-
  Brockian/WeylSchrodingerGate1Final.lean

  Final, statement-faithful assembly for the concrete one-dimensional minimal
  Schrodinger operator on the Schwartz core.

  What this file closes:

  * `freeSchrodingerPMap` is the actual core operator `f |-> -f''`, with dense
    Schwartz domain and a proved symmetry theorem.
  * `schrodingerPMap_eq_perturb_free` identifies the already-defined concrete
    operator exactly as

        schrodingerPMap V = freeSchrodingerPMap + potentialMulCLM V.

    This is equality of `LinearPMap`s, including their domains and actions.
  * `schrodinger_essentiallySelfAdjoint_of_weakSolutionVanishing` is the direct
    Gate-1 assembly under the mathematically sharp remaining weak-PDE input:
    every non-real L2 weak solution vanishes.
  * `schrodinger_essentiallySelfAdjoint_of_katoTransfer` is the independent Kato
    assembly under the exact range-density transfer for the concrete bounded
    potential perturbation.

  What remains explicit and is NOT claimed here:

  1. `WeakSolutionVanishing V`.  Proving it from continuity and boundedness is
     the missing distributional regularity / energy argument.  The existing
     primitive and FTC layers then turn it into essential self-adjointness.
  2. `BoundedPerturbationTransfer freeSchrodingerPMap (potentialMulCLM V ...)`.
     For the minimal Schwartz-core operator, essential self-adjointness gives
     dense shifted ranges, not closed or surjective shifted ranges on the core.
     The closure has the resolvents.  A full Kato-Rellich proof must construct
     those closure resolvents and transfer density back to the common core.

  In particular, no closed-range hypothesis for the minimal core is silently
  asserted, and no conditional is relabelled as an unconditional theorem.
-/
import Mathlib
import Brockian.WeylSchrodingerMinimal
import Brockian.WeylWeakPrimitiveClassical
import Brockian.WeylKatoUnbounded

open MeasureTheory Complex SchwartzMap
open scoped InnerProductSpace

namespace Brockian.Weyl.SchrodingerGate1Final

open Brockian.Weyl.Operator
open Brockian.Weyl.KatoUnbounded
open Brockian.Weyl.SchrodingerMinimal
open Brockian.WeylWeakPrimitiveClassical
open Brockian.WeylWeakRegularityDischarge

/- A uniquely named local alias avoids ambiguity among older modules that each
export an `H2` abbreviation when AXLE flattens imports into one source file. -/
noncomputable abbrev L2R := Brockian.Weyl.SchrodingerMinimal.H2

/-! ### The concrete free operator on the same Schwartz core -/

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

/-- The Schwartz domain of the free operator is dense in L2. -/
theorem freeSchrodingerPMap_dense :
    Dense (freeSchrodingerPMap.domain : Set L2R) := by
  have hfun : (schwartzToL2 : SchwartzMap ℝ ℂ → L2R)
      = (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) := by
    funext f
    rw [schwartzToL2_apply, SchwartzMap.toLpCLM_apply]
  rw [freeSchrodingerPMap_domain, LinearMap.coe_range, hfun]
  exact SchwartzMap.denseRange_toLpCLM (by norm_num)

/-- The minimal free Laplacian is symmetric on the Schwartz core. -/
theorem freeSchrodingerPMap_isSymmetric :
    IsSymmetric freeSchrodingerPMap := by
  intro x y
  obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
  obtain ⟨g, hg⟩ := (LinearMap.mem_range).mp y.2
  have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
  have hye : y = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective g :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hg.symm)
  rw [hxe, hye, freeSchrodingerPMap_toFun_ofInjective,
    freeSchrodingerPMap_toFun_ofInjective, LinearEquiv.ofInjective_apply,
    LinearEquiv.ofInjective_apply, freeCoreMap_apply, freeCoreMap_apply,
    inner_neg_left, inner_neg_right]
  exact congrArg Neg.neg (kinetic_symm f g)

/-! ### Exact identification of `-d^2 + V` as a bounded perturbation -/

/-- The concrete minimal Schrodinger operator is exactly the free Schwartz-core
operator perturbed by bounded multiplication by `V`.  This pins the abstract
Kato lane to the same operator used by the weak-regularity lane. -/
theorem schrodingerPMap_eq_perturb_free
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    schrodingerPMap V hVc M hV =
      perturb freeSchrodingerPMap (potentialMulCLM V hVc M hV) := by
  unfold schrodingerPMap perturb freeSchrodingerPMap
  apply LinearPMap.ext'
  apply LinearMap.ext
  intro x
  let E := LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective
  let f : SchwartzMap ℝ ℂ := E.symm x
  have hx : schwartzToL2 f = (x : L2R) := by
    have he : E f = x := E.apply_symm_apply x
    exact congrArg Subtype.val he
  change coreMap V hVc M hV f =
    potentialMulCLM V hVc M hV (x : L2R) + freeCoreMap f
  rw [coreMap_apply, freeCoreMap_apply, ← hx]
  abel

/-! ### Final Gate-1 assemblies with the remaining inputs exposed -/

/-- **Direct final assembly.** If every non-real L2 weak solution for `V`
vanishes, then the concrete minimal `-d^2/dx^2 + V` on Schwartz space is
essentially self-adjoint.  `WeakSolutionVanishing V` is the sole remaining
analytic hypothesis in this route. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakSolutionVanishing
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hzero : WeakSolutionVanishing V) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) :=
  schrodinger_essentiallySelfAdjoint_of_weakToPrimitive V hVc M hV
    (weakToPrimitiveRegularity_of_weakSolutionVanishing hzero)

/-- Derivative-data version of the direct assembly.  This is useful when the
classical regularity theorem is supplied as a representative with two weak
derivatives rather than as a vanishing theorem. -/
theorem schrodinger_essentiallySelfAdjoint_of_distributionalPrimitiveIdentity
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hreg : DistributionalPrimitiveIdentity V) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) :=
  schrodinger_essentiallySelfAdjoint_of_weakToPrimitive V hVc M hV
    (weakToPrimitiveRegularity_of_distributionalPrimitiveIdentity hVc hreg)

/-- **Kato final assembly.** The exact range-density transfer for the bounded
potential perturbation implies ESA of the same concrete `schrodingerPMap`.
The equality theorem above ensures this is not an abstract surrogate operator.

This theorem intentionally assumes `BoundedPerturbationTransfer`: constructing
it from the closure resolvents is the remaining unbounded Kato-Rellich step. -/
theorem schrodinger_essentiallySelfAdjoint_of_katoTransfer
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hKato : BoundedPerturbationTransfer freeSchrodingerPMap
      (potentialMulCLM V hVc M hV)) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) := by
  rw [schrodingerPMap_eq_perturb_free]
  exact essentiallySelfAdjoint_perturb freeSchrodingerPMap_dense hKato

/-- The Kato hypothesis is exactly the pair of dense shifted ranges for the
concrete perturbation, recorded as an iff after the operator identification. -/
theorem schrodinger_essentiallySelfAdjoint_iff_katoTransfer
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) ↔
      BoundedPerturbationTransfer freeSchrodingerPMap
        (potentialMulCLM V hVc M hV) := by
  rw [schrodingerPMap_eq_perturb_free]
  exact essentiallySelfAdjoint_perturb_iff
    (potentialMulCLM V hVc M hV) freeSchrodingerPMap_dense

end Brockian.Weyl.SchrodingerGate1Final
