/-
  Brockian/WeylWeakRegularityCore.lean

  A small verified core for the remaining Gate-1 weak-regularity gap.

  The current scaffold isolates the hard analysis as
  `WeakSchrodingerEquation -> ClassicalL2Representative`.  This file inserts a
  genuinely smaller intermediate target: produce a continuous integral model.
  Once such a model exists, Mathlib's interval-integral FTC gives the two
  classical derivatives and the existing `IsL2Solution` package follows.
-/
import Brockian.WeylWeakRegularityScaffold

open MeasureTheory Complex intervalIntegral

namespace Brockian.WeylWeakRegularityCore

open Brockian.WeylWeakRegularityScaffold

/-- The pointwise right-hand side of the Schrödinger equation
`y'' = (V - z) y`. -/
noncomputable def schrodingerRHS (V : ℝ → ℝ) (z : ℂ) (y : ℝ → ℂ) : ℝ → ℂ :=
  fun x => ((V x : ℂ) - z) * y x

/-- Continuity of the pointwise Schrödinger right-hand side. -/
theorem continuous_schrodingerRHS
    {V : ℝ → ℝ} {z : ℂ} {y : ℝ → ℂ}
    (hVc : Continuous V) (hy : Continuous y) :
    Continuous (schrodingerRHS V z y) := by
  exact ((Complex.continuous_ofReal.comp hVc).sub continuous_const).mul hy

/-- An integral representative for the weak solution.  This is intentionally
below the final classical conclusion: it contains no derivative fields.  The
derivatives are recovered from the two interval-integral identities by FTC. -/
structure IntegralSchrodingerModel
    (V : ℝ → ℝ) (z : ℂ) (g : Brockian.WeylWeakRegularityScaffold.H2) (y y' : ℝ → ℂ) (a : ℝ) : Prop where
  continuous_y : Continuous y
  continuous_y' : Continuous y'
  y_integral : ∀ x, y x = y a + ∫ t in a..x, y' t
  y'_integral : ∀ x, y' x = y' a + ∫ t in a..x, schrodingerRHS V z y t
  memL2 : MemLp y 2 volume
  memL2' : MemLp y' 2 volume
  represents : (g : ℝ → ℂ) =ᵐ[volume] y

/-- The first integral identity gives `y'` as the derivative of `y`. -/
theorem integralModel_hasDerivAt_y
    {V : ℝ → ℝ} {z : ℂ} {g : Brockian.WeylWeakRegularityScaffold.H2} {y y' : ℝ → ℂ} {a x : ℝ}
    (hmodel : IntegralSchrodingerModel V z g y y' a) :
    HasDerivAt y (y' x) x := by
  have hfun : y = fun u => y a + ∫ t in a..u, y' t :=
    funext hmodel.y_integral
  rw [hfun]
  simpa using (hmodel.continuous_y'.integral_hasStrictDerivAt a x).hasDerivAt.const_add (y a)

/-- The second integral identity gives the derivative of `y'`. -/
theorem integralModel_hasDerivAt_yPrime
    {V : ℝ → ℝ} {z : ℂ} {g : Brockian.WeylWeakRegularityScaffold.H2} {y y' : ℝ → ℂ} {a x : ℝ}
    (hVc : Continuous V)
    (hmodel : IntegralSchrodingerModel V z g y y' a) :
    HasDerivAt y' (schrodingerRHS V z y x) x := by
  have hfun : y' = fun u => y' a + ∫ t in a..u, schrodingerRHS V z y t :=
    funext hmodel.y'_integral
  rw [hfun]
  have hcont : Continuous (schrodingerRHS V z y) :=
    continuous_schrodingerRHS hVc hmodel.continuous_y
  simpa using (hcont.integral_hasStrictDerivAt a x).hasDerivAt.const_add (y' a)

/-- An integral model gives the existing classical L² ODE solution package. -/
theorem integralModel_isL2Solution
    {V : ℝ → ℝ} {z : ℂ} {g : Brockian.WeylWeakRegularityScaffold.H2} {y y' : ℝ → ℂ} {a : ℝ}
    (hVc : Continuous V)
    (hmodel : IntegralSchrodingerModel V z g y y' a) :
    Brockian.Weyl.Bridge.IsL2Solution V z y y' (schrodingerRHS V z y) where
  deriv1 := fun x => integralModel_hasDerivAt_y hmodel
  deriv2 := fun x => integralModel_hasDerivAt_yPrime hVc hmodel
  eqn := fun x => rfl
  memL2 := hmodel.memL2
  memL2' := hmodel.memL2'

/-- An integral model gives the `ClassicalL2Representative` demanded by the
existing weak-regularity scaffold. -/
theorem classicalL2Representative_of_integralModel
    {V : ℝ → ℝ} {z : ℂ} {g : Brockian.WeylWeakRegularityScaffold.H2} {y y' : ℝ → ℂ} {a : ℝ}
    (hVc : Continuous V)
    (hmodel : IntegralSchrodingerModel V z g y y' a) :
    ClassicalL2Representative V z g :=
  ⟨y, y', schrodingerRHS V z y, integralModel_isL2Solution hVc hmodel,
    hmodel.represents⟩

/-- A sharper remaining regularity target: weak solutions have continuous
integral representatives.  This is weaker than asking for a classical ODE
representative because the derivative data are not assumed; they are recovered by
FTC in `classicalL2Representative_of_integralModel`. -/
def WeakToIntegralRegularity (V : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → ∀ g : Brockian.WeylWeakRegularityScaffold.H2,
    WeakSchrodingerEquation V z g →
      ∃ (a : ℝ) (y y' : ℝ → ℂ), IntegralSchrodingerModel V z g y y' a

/-- The integral-model target implies the existing weak-to-classical target. -/
theorem weakToClassicalRegularity_of_weakToIntegral
    {V : ℝ → ℝ} (hVc : Continuous V)
    (hreg : WeakToIntegralRegularity V) :
    WeakToClassicalRegularity V := by
  intro z hz g hweak
  obtain ⟨a, y, y', hmodel⟩ := hreg z hz g hweak
  exact classicalL2Representative_of_integralModel hVc hmodel

/-- Gate 1 reduced to the sharper integral-model regularity target. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakToIntegral
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hreg : WeakToIntegralRegularity V) :
    Brockian.Weyl.Operator.EssentiallySelfAdjoint
      (Brockian.Weyl.SchrodingerMinimal.schrodingerPMap V hVc M hV) :=
  schrodinger_essentiallySelfAdjoint_of_weakToClassical V hVc M hV
    (weakToClassicalRegularity_of_weakToIntegral hVc hreg)

/-- Continuous representatives of the same L² class agree pointwise. -/
theorem continuous_representatives_eq_of_ae
    {y w : ℝ → ℂ} (hy : Continuous y) (hw : Continuous w)
    (hyw : y =ᵐ[volume] w) :
    y = w :=
  (hy.ae_eq_iff_eq volume hw).mp hyw

/-- The classical representative in this lane is pointwise unique among
continuous representatives. -/
theorem integralModel_representative_unique
    {V : ℝ → ℝ} {z : ℂ} {g : Brockian.WeylWeakRegularityScaffold.H2}
    {y₁ y₁' y₂ y₂' : ℝ → ℂ} {a₁ a₂ : ℝ}
    (h₁ : IntegralSchrodingerModel V z g y₁ y₁' a₁)
    (h₂ : IntegralSchrodingerModel V z g y₂ y₂' a₂) :
    y₁ = y₂ := by
  refine continuous_representatives_eq_of_ae h₁.continuous_y h₂.continuous_y ?_
  exact h₁.represents.symm.trans h₂.represents

/-- Documentary packaging of the verified core: producing an integral model is
enough to recover the previous weak-to-classical scaffold and hence Gate 1. -/
structure WeakRegularityCoreStatus
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) : Prop where
  integral_to_classical :
    WeakToIntegralRegularity V → WeakToClassicalRegularity V
  integral_to_esa :
    WeakToIntegralRegularity V →
      Brockian.Weyl.Operator.EssentiallySelfAdjoint
        (Brockian.Weyl.SchrodingerMinimal.schrodingerPMap V hVc M hV)

/-- Verified inhabitant of the weak-regularity core status. -/
noncomputable def weakRegularityCoreStatus
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    WeakRegularityCoreStatus V hVc M hV where
  integral_to_classical := weakToClassicalRegularity_of_weakToIntegral hVc
  integral_to_esa := schrodinger_essentiallySelfAdjoint_of_weakToIntegral V hVc M hV

end Brockian.WeylWeakRegularityCore
