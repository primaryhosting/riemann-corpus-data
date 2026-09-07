/-
  Brockian/WeylWeakRegularityDischarge.lean

  Verified local-analytic plumbing for the Gate-1 weak-regularity gap.

  This does not prove the missing distributional/Sobolev regularity theorem.
  Instead it discharges the parts that Mathlib 4.32 already supports:

  * every `L²(ℝ)` representative is locally integrable;
  * for bounded continuous real `V`, the pointwise Schrödinger RHS
    `((V : ℂ) - z) * g` is locally integrable for every `g ∈ L²`;
  * locally integrable functions have continuous interval-integral primitives;
  * if the weak equation supplies those primitives as representatives, the existing
    `WeakToIntegralRegularity` and hence Gate-1 conditional route follows.

  The remaining theorem is now the strictly smaller
  `WeakToPrimitiveRegularity`: distributional weak solutions must be represented
  by the two primitive identities.  No `sorry`, no `axiom`, and no vacuity.
-/
import Brockian.WeylWeakRegularityCore

open MeasureTheory Complex intervalIntegral
open scoped Topology ENNReal

namespace Brockian.WeylWeakRegularityDischarge

open Brockian.WeylWeakRegularityScaffold
open Brockian.WeylWeakRegularityCore

/-- The coefficient-space representative of an `L²(ℝ)` vector is locally integrable. -/
theorem coeFn_locallyIntegrable (g : Brockian.WeylWeakRegularityScaffold.H2) :
    LocallyIntegrable (g : ℝ → ℂ) volume :=
  (Lp.memLp g).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)

/-- In particular, an `L²` representative is integrable on every compact interval. -/
theorem coeFn_integrableOn_Icc (g : Brockian.WeylWeakRegularityScaffold.H2) (a b : ℝ) :
    IntegrableOn (g : ℝ → ℂ) (Set.Icc a b) volume :=
  (coeFn_locallyIntegrable g).integrableOn_isCompact isCompact_Icc

/-- Local integrability on `ℝ` gives interval-integrability between any two points. -/
theorem locallyIntegrable_intervalIntegrable
    {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  intervalIntegrable_iff.mpr
    ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

/-- A locally integrable function has a continuous interval-integral primitive. -/
theorem locallyIntegrable_continuous_primitive
    {f : ℝ → ℂ} (hf : LocallyIntegrable f volume) (a : ℝ) :
    Continuous fun x => ∫ t in a..x, f t :=
  intervalIntegral.continuous_primitive (fun x y => locallyIntegrable_intervalIntegrable hf x y) a

/-- A bounded continuous potential makes the pointwise Schrödinger RHS of an `L²`
representative locally integrable. -/
theorem schrodingerRHS_coeFn_locallyIntegrable
    {V : ℝ → ℝ} (hVc : Continuous V) {M : ℝ} (hV : ∀ x, |V x| ≤ M)
    (z : ℂ) (g : Brockian.WeylWeakRegularityScaffold.H2) :
    LocallyIntegrable (schrodingerRHS V z (g : ℝ → ℂ)) volume := by
  have hg : LocallyIntegrable (g : ℝ → ℂ) volume := coeFn_locallyIntegrable g
  have hMnonneg : 0 ≤ M := by
    exact (abs_nonneg (V 0)).trans (hV 0)
  have hCnonneg : 0 ≤ M + ‖z‖ := add_nonneg hMnonneg (norm_nonneg z)
  let C : ℂ := (M + ‖z‖ : ℝ)
  have hCg : LocallyIntegrable (fun x : ℝ => C • ((g : ℝ → ℂ) x)) volume :=
    hg.smul C
  refine hCg.mono ?_ ?_
  · exact AEStronglyMeasurable.mul
      (((Complex.continuous_ofReal.comp hVc).sub continuous_const).aestronglyMeasurable)
      (Lp.aestronglyMeasurable g)
  · filter_upwards with x
    calc
      ‖schrodingerRHS V z (g : ℝ → ℂ) x‖
          = ‖((V x : ℂ) - z) * ((g : ℝ → ℂ) x)‖ := rfl
      _ = ‖(V x : ℂ) - z‖ * ‖((g : ℝ → ℂ) x)‖ := norm_mul _ _
      _ ≤ (‖(V x : ℂ)‖ + ‖z‖) * ‖((g : ℝ → ℂ) x)‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = (|V x| + ‖z‖) * ‖((g : ℝ → ℂ) x)‖ := by
        simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ (M + ‖z‖) * ‖((g : ℝ → ℂ) x)‖ := by
        gcongr
        exact hV x
      _ = ‖C • ((g : ℝ → ℂ) x)‖ := by
        have hCnorm : ‖C‖ = M + ‖z‖ := by
          change ‖((M + ‖z‖ : ℝ) : ℂ)‖ = M + ‖z‖
          rw [Complex.norm_real, Real.norm_of_nonneg hCnonneg]
        rw [norm_smul, hCnorm]

/-- The primitive of the Schrödinger RHS of an `L²` representative is continuous. -/
theorem continuous_rhs_primitive_of_coeFn
    {V : ℝ → ℝ} (hVc : Continuous V) {M : ℝ} (hV : ∀ x, |V x| ≤ M)
    (z : ℂ) (g : Brockian.WeylWeakRegularityScaffold.H2) (a : ℝ) :
    Continuous fun x => ∫ t in a..x, schrodingerRHS V z (g : ℝ → ℂ) t :=
  locallyIntegrable_continuous_primitive
    (schrodingerRHS_coeFn_locallyIntegrable hVc hV z g) a

/-- A primitive-level model: the weak solution has an `L²` representative `y` and
first primitive `y'`, with both primitive identities.  This is the exact place where
distributional regularity still enters; everything below it is verified. -/
structure PrimitiveSchrodingerModel
    (V : ℝ → ℝ) (z : ℂ) (g : Brockian.WeylWeakRegularityScaffold.H2)
    (y y' : ℝ → ℂ) (a : ℝ) : Prop where
  continuous_y : Continuous y
  continuous_y' : Continuous y'
  y_integral : ∀ x, y x = y a + ∫ t in a..x, y' t
  y'_integral : ∀ x, y' x = y' a + ∫ t in a..x, schrodingerRHS V z y t
  memL2 : MemLp y 2 volume
  memL2' : MemLp y' 2 volume
  represents : (g : ℝ → ℂ) =ᵐ[volume] y

/-- A primitive model is exactly enough to produce the integral model used by the
existing weak-regularity core. -/
theorem integralModel_of_primitiveModel
    {V : ℝ → ℝ} {z : ℂ} {g : Brockian.WeylWeakRegularityScaffold.H2}
    {y y' : ℝ → ℂ} {a : ℝ}
    (hmodel : PrimitiveSchrodingerModel V z g y y' a) :
    IntegralSchrodingerModel V z g y y' a where
  continuous_y := hmodel.continuous_y
  continuous_y' := hmodel.continuous_y'
  y_integral := hmodel.y_integral
  y'_integral := hmodel.y'_integral
  memL2 := hmodel.memL2
  memL2' := hmodel.memL2'
  represents := hmodel.represents

/-- The sharpened remaining target: a weak solution admits the two primitive
identities.  Compared with `WeakToIntegralRegularity`, this name emphasizes that
the only missing step is distributional weak-solution regularity, not the FTC or
operator-theory plumbing. -/
def WeakToPrimitiveRegularity (V : ℝ → ℝ) : Prop :=
  ∀ z : ℂ, z.im ≠ 0 → ∀ g : Brockian.WeylWeakRegularityScaffold.H2,
    WeakSchrodingerEquation V z g →
      ∃ (a : ℝ) (y y' : ℝ → ℂ), PrimitiveSchrodingerModel V z g y y' a

/-- Primitive regularity implies the existing integral-model regularity target. -/
theorem weakToIntegralRegularity_of_weakToPrimitive
    {V : ℝ → ℝ} (hreg : WeakToPrimitiveRegularity V) :
    WeakToIntegralRegularity V := by
  intro z hz g hweak
  obtain ⟨a, y, y', hprim⟩ := hreg z hz g hweak
  exact ⟨a, y, y', integralModel_of_primitiveModel hprim⟩

/-- Primitive regularity implies the existing weak-to-classical target. -/
theorem weakToClassicalRegularity_of_weakToPrimitive
    {V : ℝ → ℝ} (hVc : Continuous V) (hreg : WeakToPrimitiveRegularity V) :
    WeakToClassicalRegularity V :=
  weakToClassicalRegularity_of_weakToIntegral hVc
    (weakToIntegralRegularity_of_weakToPrimitive hreg)

/-- Gate 1 for the concrete minimal operator, reduced to primitive regularity. -/
theorem schrodinger_essentiallySelfAdjoint_of_weakToPrimitive
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M)
    (hreg : WeakToPrimitiveRegularity V) :
    Brockian.Weyl.Operator.EssentiallySelfAdjoint
      (Brockian.Weyl.SchrodingerMinimal.schrodingerPMap V hVc M hV) :=
  Brockian.WeylWeakRegularityCore.schrodinger_essentiallySelfAdjoint_of_weakToIntegral
    V hVc M hV (weakToIntegralRegularity_of_weakToPrimitive hreg)

/-- Status package for the discharge layer: Mathlib proves the local-integrability
and primitive-continuity plumbing; only `WeakToPrimitiveRegularity` remains. -/
structure WeakRegularityDischargeStatus
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) : Prop where
  coeFn_local :
    ∀ g : Brockian.WeylWeakRegularityScaffold.H2, LocallyIntegrable (g : ℝ → ℂ) volume
  rhs_local :
    ∀ z : ℂ, ∀ g : Brockian.WeylWeakRegularityScaffold.H2,
      LocallyIntegrable (schrodingerRHS V z (g : ℝ → ℂ)) volume
  primitive_to_integral :
    WeakToPrimitiveRegularity V → WeakToIntegralRegularity V
  primitive_to_esa :
    WeakToPrimitiveRegularity V →
      Brockian.Weyl.Operator.EssentiallySelfAdjoint
        (Brockian.Weyl.SchrodingerMinimal.schrodingerPMap V hVc M hV)

/-- Verified inhabitant of the weak-regularity discharge status. -/
noncomputable def weakRegularityDischargeStatus
    (V : ℝ → ℝ) (hVc : Continuous V) (M : ℝ) (hV : ∀ x, |V x| ≤ M) :
    WeakRegularityDischargeStatus V hVc M hV where
  coeFn_local := coeFn_locallyIntegrable
  rhs_local := fun z g => schrodingerRHS_coeFn_locallyIntegrable hVc hV z g
  primitive_to_integral := weakToIntegralRegularity_of_weakToPrimitive
  primitive_to_esa := schrodinger_essentiallySelfAdjoint_of_weakToPrimitive V hVc M hV

end Brockian.WeylWeakRegularityDischarge
