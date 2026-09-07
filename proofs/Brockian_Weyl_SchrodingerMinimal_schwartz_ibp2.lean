/-
  Brockian/WeylSchrodingerMinimal.lean — the **concrete** minimal Schrödinger
  operator `T = −d²/dx² + V` on `L²(ℝ)`, and the exact remaining Gate-1 obligation.

  ## What is proved (AXLE-verified, hole-free)

  This module turns the last Gate-1 gap from prose into a genuine `LinearPMap`:

  * `schwartzToL2` — the injective ℂ-linear embedding `𝓢(ℝ,ℂ) ↪ L²(ℝ)` (Schwartz
    functions as L² classes); `schwartzToL2_injective`.
  * `D2` — the second-derivative operator on Schwartz space; `D2_apply`.
  * `schwartz_ibp2` — **double integration by parts for Schwartz functions**:
    `∫ conj(f″)·g = ∫ conj(f)·g″`. Built from Mathlib's Schwartz IBP; boundary
    terms vanish by rapid decay. This is the analytic content of symmetry.
  * `potentialMulCLM` — multiplication by a bounded continuous real potential `V`
    as a bounded self-adjoint operator on `L²` (`isSelfAdjoint_potentialMulCLM`).
  * `schrodingerPMap V hVc M hV : L²(ℝ) →ₗ.[ℂ] L²(ℝ)` — the concrete minimal
    operator `f ↦ −f″ + V·f` on the dense core of Schwartz functions.
  * `schrodingerPMap_domain` — its domain is the range of `schwartzToL2`.
  * `schrodingerPMap_dense` — the domain is **dense** (Schwartz dense in `L²`).
  * `schrodingerPMap_isSymmetric` — it is **symmetric** (integration by parts; the
    potential term is self-adjoint, the kinetic term symmetric via `schwartz_ibp2`).

  ## The exact remaining obligation (stated precisely, not faked)

  * `deficiencyRepresentsODE_of_adjoint_eigenvector V hVc M hV` — the precise open
    statement: every non-real adjoint eigenvector of the concrete `T` is a.e. an
    L² classical solution of `−y″ + V y = z y`. This is elliptic regularity
    (weak ⇒ classical); it is `Weyl.SchrodingerESA.DeficiencyRepresentsODE` for
    THIS concrete operator. It is named, never `sorry`'d.

  ## The honest end-to-end conditional (Gate-1)

  * `schrodinger_essentiallySelfAdjoint_of_ode` — the concrete
    `T = −d²/dx² + V` (bounded continuous `V`) is essentially self-adjoint
    **given** `deficiencyRepresentsODE_of_adjoint_eigenvector`. Composes the
    construction above with `Weyl.Bridge.no_nonzero_L2_solution` and
    `Weyl.SchrodingerESA.essentiallySelfAdjoint_of_ode_bridge`.

  So Gate-1 is closed **conditional on elliptic regularity** for the same concrete
  operator; the only remaining step is the distributional-regularity core, pinned
  above as an explicit named statement.

  Verification (spec §2A): AXLE @ lean-4.32.0 and lean-4.28.0;
  axioms ⊆ {propext, Classical.choice, Quot.sound}.
-/
import Mathlib
import Brockian.WeylOperator
import Brockian.WeylBridge
import Brockian.WeylSchrodingerESA
import Brockian.SpectralGate1

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace
open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerESA Brockian.SpectralGate1

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

/-! ### The potential term: bounded multiplication by `V` -/

/-- **Multiplication by a bounded continuous real potential** as a bounded operator
on `L²`. -/
noncomputable def potentialMulCLM (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) : H2 →L[ℂ] H2 :=
  mulLpCLM (fun x => (V x : ℂ))
    (memLp_top_of_bound (Complex.continuous_ofReal.comp hVc).aestronglyMeasurable M
      (ae_of_all _ fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hV x))
    ((abs_nonneg (V 0)).trans (hV 0))
    (ae_of_all _ fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hV x)

/-- The potential term is bounded self-adjoint (real multiplier). -/
theorem isSelfAdjoint_potentialMulCLM (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) : IsSelfAdjoint (potentialMulCLM V hVc M hV) := by
  unfold potentialMulCLM
  exact isSelfAdjoint_mulLpCLM _ _ _ _ (ae_of_all _ fun x => Complex.conj_ofReal (V x))

/-- Symmetry of the potential term on the Schwartz core. -/
theorem potential_symm (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (f g : SchwartzMap ℝ ℂ) :
    ⟪potentialMulCLM V hVc M hV (schwartzToL2 f), schwartzToL2 g⟫_ℂ
      = ⟪schwartzToL2 f, potentialMulCLM V hVc M hV (schwartzToL2 g)⟫_ℂ := by
  have hsymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (isSelfAdjoint_potentialMulCLM V hVc M hV)
  exact hsymm (schwartzToL2 f) (schwartzToL2 g)

/-! ### The core linear map `f ↦ −f″ + V·f` -/

/-- The action of the minimal operator on the Schwartz core, as a ℂ-linear map. -/
noncomputable def coreMap (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] H2 :=
  -(schwartzToL2.comp (D2 : SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ).toLinearMap)
    + (potentialMulCLM V hVc M hV).toLinearMap.comp schwartzToL2

theorem coreMap_apply (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (f : SchwartzMap ℝ ℂ) :
    coreMap V hVc M hV f
      = -(schwartzToL2 (D2 f)) + potentialMulCLM V hVc M hV (schwartzToL2 f) := by
  simp only [coreMap, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    ContinuousLinearMap.coe_coe]

/-- **Symmetry of the full core action** `−f″ + V·f`: the potential term is
self-adjoint and the kinetic term is symmetric by double IBP. -/
theorem coreMap_symm (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (f g : SchwartzMap ℝ ℂ) :
    ⟪coreMap V hVc M hV f, schwartzToL2 g⟫_ℂ = ⟪schwartzToL2 f, coreMap V hVc M hV g⟫_ℂ := by
  rw [coreMap_apply, coreMap_apply, inner_add_left, inner_add_right, inner_neg_left,
    inner_neg_right, kinetic_symm f g, potential_symm V hVc M hV f g]

/-! ### The minimal operator as a `LinearPMap` -/

/-- **The minimal Schrödinger operator** `T = −d²/dx² + V` on `L²(ℝ)`, defined on
the dense core of Schwartz functions. -/
noncomputable def schrodingerPMap (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) : H2 →ₗ.[ℂ] H2 where
  domain := LinearMap.range schwartzToL2
  toFun := (coreMap V hVc M hV).comp
    (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap

/-- The domain of the minimal operator is the Schwartz core. -/
theorem schrodingerPMap_domain (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    (schrodingerPMap V hVc M hV).domain = LinearMap.range schwartzToL2 := rfl

/-- **Density of the core.** The domain of the minimal operator is dense in `L²`
(Schwartz functions are dense in `Lp`). -/
theorem schrodingerPMap_dense (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    Dense ((schrodingerPMap V hVc M hV).domain : Set H2) := by
  have hfun : (schwartzToL2 : SchwartzMap ℝ ℂ → H2)
      = (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure ℝ)) := by
    funext f; rw [schwartzToL2_apply, SchwartzMap.toLpCLM_apply]
  rw [schrodingerPMap_domain, LinearMap.coe_range, hfun]
  exact SchwartzMap.denseRange_toLpCLM (by norm_num)

/-- The minimal operator on a core element `T (schwartzToL2 f) = −f″ + V·f`. -/
theorem schrodingerPMap_toFun_ofInjective (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) (f : SchwartzMap ℝ ℂ) :
    (schrodingerPMap V hVc M hV)
        (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
      = coreMap V hVc M hV f := by
  show (coreMap V hVc M hV).comp
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective).symm.toLinearMap
      (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f)
    = coreMap V hVc M hV f
  rw [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]

/-- **Symmetry of the minimal operator.** `T = −d²/dx² + V` is symmetric on its
dense Schwartz core (integration by parts; boundary terms vanish by rapid decay). -/
theorem schrodingerPMap_isSymmetric (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) : IsSymmetric (schrodingerPMap V hVc M hV) := by
  intro x y
  obtain ⟨f, hf⟩ := (LinearMap.mem_range).mp x.2
  obtain ⟨g, hg⟩ := (LinearMap.mem_range).mp y.2
  have hxe : x = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective f :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hf.symm)
  have hye : y = LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective g :=
    Subtype.ext (by rw [LinearEquiv.ofInjective_apply]; exact hg.symm)
  rw [hxe, hye, schrodingerPMap_toFun_ofInjective, schrodingerPMap_toFun_ofInjective,
    LinearEquiv.ofInjective_apply, LinearEquiv.ofInjective_apply]
  exact coreMap_symm V hVc M hV f g

/-! ### The exact remaining Gate-1 obligation + honest conditional assembly -/

/-- **The exact remaining Gate-1 obligation** for the concrete minimal operator
`schrodingerPMap V = −d²/dx² + V`: every non-real adjoint eigenvector of `T` is
a.e. represented by a classical L² solution of the Schrödinger ODE. This is
elliptic regularity (weak ⇒ classical); it is the *only* undischarged step, stated
precisely as `SchrodingerESA.DeficiencyRepresentsODE` for this concrete `T`. -/
abbrev deficiencyRepresentsODE_of_adjoint_eigenvector
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) : Prop :=
  DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V

/-- **Gate-1 (conditional on elliptic regularity).** The concrete minimal operator
`T = −d²/dx² + V` for bounded continuous real `V` is essentially self-adjoint,
**given** `deficiencyRepresentsODE_of_adjoint_eigenvector`. This composes:
construction (dense + symmetric, above) + `Bridge.no_nonzero_L2_solution` +
`SchrodingerESA.essentiallySelfAdjoint_of_ode_bridge`. It is honest: it does not
claim unconditional ESA — the elliptic-regularity hypothesis is named, not hidden. -/
theorem schrodinger_essentiallySelfAdjoint_of_ode
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hode : deficiencyRepresentsODE_of_adjoint_eigenvector V hVc M hV) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) :=
  essentiallySelfAdjoint_of_ode_bridge (schrodingerPMap V hVc M hV)
    (schrodingerPMap_dense V hVc M hV) (schrodingerPMap_isSymmetric V hVc M hV)
    V hVc M hV hode

/-- Documentary packaging: the concrete Gate-1 state — constructed & symmetric &
dense, ESA reduced to a single named elliptic-regularity statement. -/
structure MinimalGate1Status (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) where
  /-- The core is dense. -/
  core_dense : Dense ((schrodingerPMap V hVc M hV).domain : Set H2)
  /-- The operator is symmetric. -/
  symmetric : IsSymmetric (schrodingerPMap V hVc M hV)
  /-- ESA holds once the (named) elliptic-regularity statement is discharged. -/
  esa_conditional : deficiencyRepresentsODE_of_adjoint_eigenvector V hVc M hV →
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV)

/-- The verified inhabitant: concrete `T` is dense + symmetric, ESA-conditional. -/
noncomputable def minimal_gate1_status (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ)
    (hV : ∀ x, |V x| ≤ M) : MinimalGate1Status V hVc M hV where
  core_dense := schrodingerPMap_dense V hVc M hV
  symmetric := schrodingerPMap_isSymmetric V hVc M hV
  esa_conditional := schrodinger_essentiallySelfAdjoint_of_ode V hVc M hV

end Brockian.Weyl.SchrodingerMinimal
