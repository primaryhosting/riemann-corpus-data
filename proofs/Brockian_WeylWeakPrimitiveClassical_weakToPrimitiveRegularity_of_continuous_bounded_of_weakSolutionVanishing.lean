/-
  Brockian/WeylWeakPrimitiveClassical.lean

  Classical-analysis interface for the remaining weak-regularity gap.

  The ambitious theorem

    `WeakSchrodingerEquation V z g -> PrimitiveSchrodingerModel V z g ...`

  is exactly the missing distributional/Sobolev regularity step.  Mathlib 4.32 has
  useful Schwartz/tempered-distribution APIs, but not the one-dimensional theorem
  connecting the raw weak Schrödinger identity used in this project to an
  absolutely-continuous primitive representative.

  This file therefore pins down the two honest routes below the missing theorem:

    * derivative-data route: a representative with pointwise derivative data gives
      the required primitive model by FTC;
    * vanishing route: if every non-real weak solution is zero, primitive regularity
      follows from the zero primitive model.

  Neither route proves the missing regularity theorem by fiat; both are reusable
  verified interfaces for the next attack.
-/
import Brockian.WeylWeakRegularityDischarge

open MeasureTheory Complex intervalIntegral
open scoped Topology ENNReal

namespace Brockian.WeylWeakPrimitiveClassical

open Brockian.WeylWeakRegularityScaffold
open Brockian.WeylWeakRegularityCore
open Brockian.WeylWeakRegularityDischarge

/-- A pointwise classical representative package below `PrimitiveSchrodingerModel`.
It asks for derivative data instead of primitive identities; the primitive
identities are recovered by interval-integral FTC. -/
structure DistributionalPrimitiveData
    (V : ℝ → ℝ) (z : ℂ) (g : Brockian.WeylWeakRegularityScaffold.H2) where
  a : ℝ
  y : ℝ → ℂ
  y' : ℝ → ℂ
  continuous_y : Continuous y
  continuous_y' : Continuous y'
  deriv_y : ∀ x, HasDerivAt y (y' x) x
  deriv_y' : ∀ x, HasDerivAt y' (schrodingerRHS V z y x) x
  memL2_y' : MemLp y' 2 volume
  represents : (g : ℝ → ℂ) =ᵐ[volume] y

/-- The precise external regularity theorem needed by the derivative-data route:
every weak non-real solution has a representative with pointwise derivative data. -/
def DistributionalPrimitiveIdentity (V : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → ∀ g : Brockian.WeylWeakRegularityScaffold.H2,
    WeakSchrodingerEquation V z g → Nonempty (DistributionalPrimitiveData V z g)

/-- The alternative external theorem needed by the vanishing route: every weak
non-real solution is zero in `L²`. -/
def WeakSolutionVanishing (V : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → ∀ g : Brockian.WeylWeakRegularityScaffold.H2,
    WeakSchrodingerEquation V z g → g = 0

/-- An a.e. representative of an `L²` element is again in `L²`. -/
theorem memLp_of_l2_representative
    (g : Brockian.WeylWeakRegularityScaffold.H2) {y : ℝ → ℂ}
    (hgy : (g : ℝ → ℂ) =ᵐ[volume] y) :
    MemLp y 2 volume :=
  (memLp_congr_ae hgy).mp (Lp.memLp g)

/-- FTC turns pointwise derivative data into the first primitive identity. -/
theorem integral_identity_of_hasDerivAt
    {y y' : ℝ → ℂ} {a x : ℝ}
    (hy'c : Continuous y') (hder : ∀ t, HasDerivAt y (y' t) t) :
    y x = y a + ∫ t in a..x, y' t := by
  have hftc :
      ∫ t in a..x, y' t = y x - y a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hder t) (hy'c.intervalIntegrable a x)
  rw [hftc]
  abel

/-- FTC turns pointwise derivative data into the second primitive identity. -/
theorem rhs_integral_identity_of_hasDerivAt
    {V : ℝ → ℝ} {z : ℂ} {y y' : ℝ → ℂ} {a x : ℝ}
    (hVc : Continuous V) (hyc : Continuous y)
    (hder : ∀ t, HasDerivAt y' (schrodingerRHS V z y t) t) :
    y' x = y' a + ∫ t in a..x, schrodingerRHS V z y t := by
  have hrhs : Continuous (schrodingerRHS V z y) :=
    continuous_schrodingerRHS hVc hyc
  have hftc :
      ∫ t in a..x, schrodingerRHS V z y t = y' x - y' a := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hder t) (hrhs.intervalIntegrable a x)
  rw [hftc]
  abel

/-- Derivative-data route: pointwise derivative data gives the existing primitive
model package. -/
theorem primitiveModel_of_distributionalPrimitiveData
    {V : ℝ → ℝ} {z : ℂ} {g : Brockian.WeylWeakRegularityScaffold.H2}
    (hVc : Continuous V) (hdata : DistributionalPrimitiveData V z g) :
    PrimitiveSchrodingerModel V z g hdata.y hdata.y' hdata.a where
  continuous_y := hdata.continuous_y
  continuous_y' := hdata.continuous_y'
  y_integral := fun x =>
    integral_identity_of_hasDerivAt hdata.continuous_y' hdata.deriv_y
  y'_integral := fun x =>
    rhs_integral_identity_of_hasDerivAt hVc hdata.continuous_y hdata.deriv_y'
  memL2 := memLp_of_l2_representative g hdata.represents
  memL2' := hdata.memL2_y'
  represents := hdata.represents

/-- The derivative-data identity discharges the project's
`WeakToPrimitiveRegularity` target. -/
theorem weakToPrimitiveRegularity_of_distributionalPrimitiveIdentity
    {V : ℝ → ℝ} (hVc : Continuous V)
    (hD : DistributionalPrimitiveIdentity V) :
    WeakToPrimitiveRegularity V := by
  intro z hz g hweak
  obtain ⟨hdata⟩ := hD z hz g hweak
  exact ⟨hdata.a, hdata.y, hdata.y',
    primitiveModel_of_distributionalPrimitiveData hVc hdata⟩

/-- Same bridge with the bounded-continuous hypotheses used elsewhere in the
Weyl pipeline.  The boundedness hypotheses are carried for statement alignment;
the derivative-data-to-primitive step only uses continuity. -/
theorem weakToPrimitiveRegularity_of_continuous_bounded_of_distributionalPrimitiveIdentity
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (_hV : ∀ x, |V x| ≤ M)
    (hD : DistributionalPrimitiveIdentity V) :
    WeakToPrimitiveRegularity V :=
  weakToPrimitiveRegularity_of_distributionalPrimitiveIdentity hVc hD

/-- The zero L² class has the zero primitive model. -/
theorem primitiveModel_zero
    (V : ℝ → ℝ) (z : ℂ) :
    PrimitiveSchrodingerModel V z (0 : Brockian.WeylWeakRegularityScaffold.H2)
      (fun _ : ℝ => (0 : ℂ)) (fun _ : ℝ => (0 : ℂ)) 0 where
  continuous_y := continuous_const
  continuous_y' := continuous_const
  y_integral := by simp
  y'_integral := by simp [schrodingerRHS]
  memL2 := MemLp.zero'
  memL2' := MemLp.zero'
  represents := by
    exact Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure ℝ))

/-- Vanishing route: if all non-real weak solutions vanish in `L²`, then primitive
regularity follows by the zero primitive model. -/
theorem weakToPrimitiveRegularity_of_weakSolutionVanishing
    {V : ℝ → ℝ} (hzero : WeakSolutionVanishing V) :
    WeakToPrimitiveRegularity V := by
  intro z hz g hweak
  have hg0 : g = 0 := hzero z hz g hweak
  subst hg0
  exact ⟨0, fun _ : ℝ => (0 : ℂ), fun _ : ℝ => (0 : ℂ), primitiveModel_zero V z⟩

/-- Bounded-continuous packaging of the vanishing route.  This is the most direct
way to close the requested theorem if the next proof establishes weak
deficiency-vector vanishing without constructing a full classical representative. -/
theorem weakToPrimitiveRegularity_of_continuous_bounded_of_weakSolutionVanishing
    (V : ℝ → ℝ) (_hVc : Continuous V) (M : ℝ) (_hV : ∀ x, |V x| ≤ M)
    (hzero : WeakSolutionVanishing V) :
    WeakToPrimitiveRegularity V :=
  weakToPrimitiveRegularity_of_weakSolutionVanishing hzero

/-- Status package for the classical weak-primitive interface. -/
structure WeakPrimitiveClassicalStatus (V : ℝ → ℝ)
    (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) : Prop where
  derivative_data_route :
    DistributionalPrimitiveIdentity V → WeakToPrimitiveRegularity V
  vanishing_route :
    WeakSolutionVanishing V → WeakToPrimitiveRegularity V
  primitive_to_esa :
    WeakToPrimitiveRegularity V →
      Brockian.Weyl.Operator.EssentiallySelfAdjoint
        (Brockian.Weyl.SchrodingerMinimal.schrodingerPMap V hVc M hV)

/-- Verified interface status for the weak-primitive classical layer. -/
noncomputable def weakPrimitiveClassicalStatus
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    WeakPrimitiveClassicalStatus V hVc M hV where
  derivative_data_route :=
    weakToPrimitiveRegularity_of_continuous_bounded_of_distributionalPrimitiveIdentity V hVc M hV
  vanishing_route :=
    weakToPrimitiveRegularity_of_continuous_bounded_of_weakSolutionVanishing V hVc M hV
  primitive_to_esa :=
    schrodinger_essentiallySelfAdjoint_of_weakToPrimitive V hVc M hV

end Brockian.WeylWeakPrimitiveClassical
