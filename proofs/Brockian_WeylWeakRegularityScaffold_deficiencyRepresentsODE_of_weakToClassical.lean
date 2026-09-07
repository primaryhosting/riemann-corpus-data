/-
  Brockian/WeylWeakRegularityScaffold.lean — small, reusable scaffolding for the
  remaining weak-regularity/ODE-identification gap in Gate 1.

  The existing `WeylDeficiencyRegularity` module already reduces the concrete
  Schrödinger minimal operator to one classical analysis statement,
  `WeakSolutionRegularity`.  This file factors that statement into two smaller
  pieces:

    * `WeakSchrodingerEquation V z g`: the distributional/weak eigen-equation
      tested against every Schwartz function;
    * `ClassicalL2Representative V z g`: existence of a classical L² ODE solution
      representing the L² class `g` a.e.

  It also proves the reusable unconditional adjoint-unpacking lemma:

    * `deficiencyVector_weakSchrodingerEquation`: a concrete deficiency vector of
      the Schwartz-core Schrödinger operator satisfies `WeakSchrodingerEquation`.

  Thus future work can target the pure analytic implication
  `WeakSchrodingerEquation → ClassicalL2Representative`, without reopening the
  `LinearPMap` adjoint plumbing.
-/
import Brockian.WeylDeficiencyRegularity

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace
open Brockian.Weyl.Operator
open Brockian.Weyl.SchrodingerMinimal

namespace Brockian.WeylWeakRegularityScaffold

/-- L² space for the one-dimensional Schrödinger operator. -/
noncomputable abbrev H2 := Lp ℂ 2 (volume : Measure ℝ)

/-- The weak Schrödinger eigen-equation for an L² class `g`, tested against every
Schwartz function. This is the operator-free distributional statement extracted
from the adjoint eigenvector equation. -/
def WeakSchrodingerEquation (V : ℝ → ℝ) (z : ℂ) (g : H2) : Prop :=
  ∀ φ : SchwartzMap ℝ ℂ,
    conj z * ∫ x, conj ((g : ℝ → ℂ) x) * (φ : ℝ → ℂ) x
      = (-(∫ x, conj ((g : ℝ → ℂ) x) * deriv (deriv (φ : ℝ → ℂ)) x))
        + ∫ x, conj ((g : ℝ → ℂ) x) * ((V x : ℂ) * (φ : ℝ → ℂ) x)

/-- A classical L² ODE solution representing the L² class `g` a.e. -/
def ClassicalL2Representative (V : ℝ → ℝ) (z : ℂ) (g : H2) : Prop :=
  ∃ (y y' y'' : ℝ → ℂ),
    Brockian.Weyl.Bridge.IsL2Solution V z y y' y'' ∧
      (g : ℝ → ℂ) =ᵐ[volume] y

/-- The remaining regularity target in factored form: every non-real weak L²
solution has a classical L² representative. -/
def WeakToClassicalRegularity (V : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → ∀ g : H2,
    WeakSchrodingerEquation V z g → ClassicalL2Representative V z g

/-- The factored regularity target is definitionally the existing
`DeficiencyODE.WeakSolutionRegularity`, with only names added for the weak equation
and the representative conclusion. -/
theorem weakToClassicalRegularity_iff_existing (V : ℝ → ℝ) :
    WeakToClassicalRegularity V ↔ Brockian.Weyl.DeficiencyODE.WeakSolutionRegularity V :=
  Iff.rfl

/-- Convert the factored scaffold hypothesis to the existing Gate-1 regularity
hypothesis. -/
theorem existingWeakRegularity_of_weakToClassical (V : ℝ → ℝ)
    (h : WeakToClassicalRegularity V) :
    Brockian.Weyl.DeficiencyODE.WeakSolutionRegularity V :=
  (weakToClassicalRegularity_iff_existing V).mp h

/-- Convert the existing Gate-1 regularity hypothesis to the factored scaffold
form. -/
theorem weakToClassicalRegularity_of_existing (V : ℝ → ℝ)
    (h : Brockian.Weyl.DeficiencyODE.WeakSolutionRegularity V) :
    WeakToClassicalRegularity V :=
  (weakToClassicalRegularity_iff_existing V).mpr h

/-- A classical representative at a non-real spectral parameter is zero for a
bounded continuous real potential, by the already-proved Wronskian bridge. -/
theorem classicalL2Representative_eq_zero_of_bounded_nonreal
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    {z : ℂ} (hz : z.im ≠ 0) {g : H2}
    (hrep : ClassicalL2Representative V z g) :
    g = 0 := by
  obtain ⟨y, y', y'', hsol, hgy⟩ := hrep
  have hy0 : ∀ x, y x = 0 :=
    Brockian.Weyl.Bridge.no_nonzero_L2_solution V hVc M hV z hz y y' y'' hsol
  apply Lp.ext
  filter_upwards [hgy, Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure ℝ))] with x hx hz0
  rw [hx, hy0 x, hz0, Pi.zero_apply]

/-- **Unconditional adjoint unpacking.** A deficiency vector of the concrete
minimal Schrödinger operator satisfies the weak Schrödinger equation. This is the
operator-theoretic half of `WeakSolutionRegularity`, factored out so the remaining
target is pure weak-to-classical regularity. -/
theorem deficiencyVector_weakSchrodingerEquation
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    {z : ℂ} (g : (schrodingerPMap V hVc M hV).adjoint.domain)
    (hg : g ∈ deficiencySpace (schrodingerPMap V hVc M hV) z) :
    WeakSchrodingerEquation V z (g : H2) := by
  intro φ
  have heig : (schrodingerPMap V hVc M hV).adjoint g = z • ((g : H2)) :=
    (mem_deficiencySpace_iff (schrodingerPMap V hVc M hV) z g).mp hg
  have hdense := schrodingerPMap_dense V hVc M hV
  have hFA := LinearPMap.adjoint_isFormalAdjoint hdense g
    (LinearEquiv.ofInjective schwartzToL2 schwartzToL2_injective φ)
  rw [heig, inner_smul_left, schrodingerPMap_toFun_ofInjective,
    LinearEquiv.ofInjective_apply, coreMap_apply, inner_add_right, inner_neg_right] at hFA
  rw [Brockian.Weyl.DeficiencyODE.inner_g_schwartz (g : H2) φ,
    Brockian.Weyl.DeficiencyODE.inner_g_schwartz_D2 (g : H2) φ,
    Brockian.Weyl.DeficiencyODE.inner_g_potential V hVc M hV (g : H2) φ] at hFA
  exact hFA

/-- The factored regularity scaffold implies the exact concrete ODE-identification
obligation used by `WeylSchrodingerMinimal`. -/
theorem deficiencyRepresentsODE_of_weakToClassical
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hreg : WeakToClassicalRegularity V) :
    Brockian.Weyl.SchrodingerESA.DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V := by
  intro z hz g hg
  obtain ⟨y, y', y'', hsol, hgy⟩ :=
    hreg z hz (g : H2) (deficiencyVector_weakSchrodingerEquation V hVc M hV g hg)
  refine ⟨y, y', y'', hsol, ?_⟩
  intro hy0
  apply Lp.ext
  filter_upwards [hgy, Lp.coeFn_zero (E := ℂ) (p := (2 : ENNReal))
      (μ := (volume : Measure ℝ))] with x hx hz0
  rw [hx, hy0 x, hz0, Pi.zero_apply]

/-- Gate 1 for the concrete minimal operator, reduced to the factored weak-to-
classical regularity target. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakToClassical
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hreg : WeakToClassicalRegularity V) :
    EssentiallySelfAdjoint (schrodingerPMap V hVc M hV) :=
  schrodinger_essentiallySelfAdjoint_of_ode V hVc M hV
    (deficiencyRepresentsODE_of_weakToClassical V hVc M hV hreg)

/-- Documentary packaging for the current weak-regularity pipeline. -/
structure WeakRegularityPipelineStatus (V : ℝ → ℝ)
    (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) where
  /-- Deficiency vectors of the concrete minimal operator satisfy the weak equation. -/
  deficiency_to_weak :
    ∀ {z : ℂ} (g : (schrodingerPMap V hVc M hV).adjoint.domain),
      g ∈ deficiencySpace (schrodingerPMap V hVc M hV) z →
        WeakSchrodingerEquation V z (g : H2)
  /-- The factored regularity target implies the ODE-identification hypothesis. -/
  weak_to_ode :
    WeakToClassicalRegularity V →
      Brockian.Weyl.SchrodingerESA.DeficiencyRepresentsODE (schrodingerPMap V hVc M hV) V
  /-- The factored regularity target implies essential self-adjointness. -/
  weak_to_esa :
    WeakToClassicalRegularity V → EssentiallySelfAdjoint (schrodingerPMap V hVc M hV)

/-- Verified inhabitant of the weak-regularity pipeline scaffold. -/
noncomputable def weakRegularityPipelineStatus
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    WeakRegularityPipelineStatus V hVc M hV where
  deficiency_to_weak := fun g hg =>
    deficiencyVector_weakSchrodingerEquation V hVc M hV g hg
  weak_to_ode := deficiencyRepresentsODE_of_weakToClassical V hVc M hV
  weak_to_esa := schrodinger_essentiallySelfAdjoint_of_weakToClassical V hVc M hV

end Brockian.WeylWeakRegularityScaffold
