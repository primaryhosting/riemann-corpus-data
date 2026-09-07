/-
  Brockian/WeylWeakPrimitiveLocal.lean

  A local primitive interface for the remaining weak-regularity gap.

  This file does not assert the full distributional elliptic-regularity theorem.
  Instead it names a strictly sharper primitive identity for the canonical `L²`
  representative and proves that this identity is enough to discharge the
  existing `WeakToPrimitiveRegularity` target.
-/
import Brockian.WeylWeakRegularityDischarge

open MeasureTheory Complex intervalIntegral
open scoped Topology ENNReal

namespace Brockian.WeylWeakPrimitiveLocal

open Brockian.WeylWeakRegularityScaffold
open Brockian.WeylWeakRegularityCore
open Brockian.WeylWeakRegularityDischarge

/-- Primitive identities for the canonical `L²` representative `g` itself.

This is stronger and more concrete than `PrimitiveSchrodingerModel`: the first
component is fixed to be `(g : ℝ → ℂ)`, so the remaining analytic task is to
produce a continuous primitive derivative `y'` and the two interval identities
from the weak/distributional equation. -/
structure DistributionalPrimitiveIdentity
    (V : ℝ → ℝ) (z : ℂ)
    (g : Brockian.WeylWeakRegularityScaffold.H2) (a : ℝ) (y' : ℝ → ℂ) : Prop where
  continuous_coe : Continuous (g : ℝ → ℂ)
  continuous_y' : Continuous y'
  coe_integral : ∀ x, (g : ℝ → ℂ) x = (g : ℝ → ℂ) a + ∫ t in a..x, y' t
  y'_integral : ∀ x, y' x = y' a + ∫ t in a..x, schrodingerRHS V z (g : ℝ → ℂ) t
  memL2_y' : MemLp y' 2 volume

/-- The non-operator distributional primitive hypothesis needed to close the
current weak-regularity lane: every non-real weak solution has the canonical
primitive identity above. -/
def DistributionalPrimitiveHypothesis (V : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → ∀ g : Brockian.WeylWeakRegularityScaffold.H2,
    WeakSchrodingerEquation V z g →
      ∃ (a : ℝ) (y' : ℝ → ℂ), DistributionalPrimitiveIdentity V z g a y'

/-- A canonical primitive identity yields the existing primitive model by taking
`y = (g : ℝ → ℂ)`. -/
theorem primitiveModel_of_distributionalPrimitiveIdentity
    {V : ℝ → ℝ} {z : ℂ} {g : Brockian.WeylWeakRegularityScaffold.H2}
    {a : ℝ} {y' : ℝ → ℂ}
    (h : DistributionalPrimitiveIdentity V z g a y') :
    PrimitiveSchrodingerModel V z g (g : ℝ → ℂ) y' a where
  continuous_y := h.continuous_coe
  continuous_y' := h.continuous_y'
  y_integral := h.coe_integral
  y'_integral := h.y'_integral
  memL2 := Lp.memLp g
  memL2' := h.memL2_y'
  represents := EventuallyEq.rfl

/-- The distributional primitive hypothesis discharges
`WeakToPrimitiveRegularity`. -/
theorem weakToPrimitiveRegularity_of_distributional_primitives
    (V : ℝ → ℝ) (_hVc : Continuous V) (M : ℝ) (_hV : ∀ x, |V x| ≤ M)
    (H : DistributionalPrimitiveHypothesis V) :
    WeakToPrimitiveRegularity V := by
  intro z hz g hweak
  obtain ⟨a, y', hprim⟩ := H z hz g hweak
  exact ⟨a, (g : ℝ → ℂ), y',
    primitiveModel_of_distributionalPrimitiveIdentity hprim⟩

/-- The same primitive hypothesis gives the integral-model regularity target. -/
theorem weakToIntegralRegularity_of_distributional_primitives
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (H : DistributionalPrimitiveHypothesis V) :
    WeakToIntegralRegularity V :=
  weakToIntegralRegularity_of_weakToPrimitive
    (weakToPrimitiveRegularity_of_distributional_primitives V hVc M hV H)

/-- Gate 1 for the concrete minimal operator, reduced to the canonical
distributional primitive identity. -/
theorem schrodinger_essentiallySelfAdjoint_of_distributional_primitives
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (H : DistributionalPrimitiveHypothesis V) :
    Brockian.Weyl.Operator.EssentiallySelfAdjoint
      (Brockian.Weyl.SchrodingerMinimal.schrodingerPMap V hVc M hV) :=
  schrodinger_essentiallySelfAdjoint_of_weakToPrimitive V hVc M hV
    (weakToPrimitiveRegularity_of_distributional_primitives V hVc M hV H)

/-- Pointwise uniqueness of the canonical primitive representative among any
primitive model representing the same `L²` class. -/
theorem primitiveModel_y_eq_coe_of_canonical_continuous
    {V : ℝ → ℝ} {z : ℂ} {g : Brockian.WeylWeakRegularityScaffold.H2}
    {a : ℝ} {y y' : ℝ → ℂ}
    (hmodel : PrimitiveSchrodingerModel V z g y y' a)
    (hcont : Continuous (g : ℝ → ℂ)) :
    y = (g : ℝ → ℂ) :=
  (continuous_representatives_eq_of_ae hmodel.continuous_y hcont
    hmodel.represents.symm)

end Brockian.WeylWeakPrimitiveLocal
