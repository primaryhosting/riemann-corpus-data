/-
  Brockian/WeylWeakRegularityClosed.lean

  The unconditional distributional content of `WeakSchrodingerEquation`.

  The project's weak equation is not malformed: after conjugating the `L2`
  representative, it says exactly that its second tempered-distribution
  derivative is the `L2` function `((V : C) - conj z) * conj g`.  This file
  proves that statement without adding a regularity hypothesis.

  The downstream energy module uses this exact distributional identity directly;
  no pointwise weak-to-classical regularity hypothesis is needed.
-/
import Mathlib
import Brockian.WeylWeakRegularityScaffold

open MeasureTheory Complex
open scoped ENNReal SchwartzMap Laplacian

namespace Brockian.WeylWeakRegularityClosed

open Brockian.WeylWeakRegularityScaffold

/-- The scaffold's one-dimensional complex `L2` space, named explicitly so
flattened independent checks cannot confuse it with sibling `H2` abbreviations. -/
noncomputable abbrev L2R := Brockian.WeylWeakRegularityScaffold.H2

/-- The pointwise conjugate of the canonical representative of an `L2` class. -/
noncomputable def conjugateRepresentative (g : L2R) : Real -> Complex :=
  fun x => conj ((g : Real -> Complex) x)

/-- Conjugating an `L2` representative preserves `L2`. -/
theorem conjugateRepresentative_memLp (g : L2R) :
    MemLp (conjugateRepresentative g) 2 volume := by
  refine (Lp.memLp g).star.ae_eq ?_
  filter_upwards with x
  rfl

/-- The conjugated right-hand side of the weak Schrodinger equation. -/
noncomputable def conjugateRHS (V : Real -> Real) (z : Complex) (g : L2R) :
    Real -> Complex :=
  fun x => ((V x : Complex) - conj z) * conjugateRepresentative g x

/-- For bounded real `V`, the conjugated right-hand side belongs to `L2`. -/
theorem conjugateRHS_memLp
    {V : Real -> Real} (hVc : Continuous V)
    {M : Real} (hV : forall x, |V x| <= M)
    (z : Complex) (g : L2R) :
    MemLp (conjugateRHS V z g) 2 volume := by
  have hMnonneg : 0 <= M :=
    (abs_nonneg (V 0)).trans (hV 0)
  have hmeas : AEStronglyMeasurable (conjugateRHS V z g) volume := by
    exact AEStronglyMeasurable.mul
      (((Complex.continuous_ofReal.comp hVc).sub continuous_const).aestronglyMeasurable)
      (conjugateRepresentative_memLp g).aestronglyMeasurable
  refine (conjugateRepresentative_memLp g).of_le_mul
    (c := M + norm z) hmeas ?_
  filter_upwards with x
  calc
    norm (conjugateRHS V z g x)
        = norm ((V x : Complex) - conj z) * norm (conjugateRepresentative g x) :=
          norm_mul _ _
    _ <= (norm (V x : Complex) + norm (conj z)) *
        norm (conjugateRepresentative g x) := by
          gcongr
          exact norm_sub_le _ _
    _ <= (M + norm z) * norm (conjugateRepresentative g x) := by
          rw [norm_conj]
          gcongr
          simpa [Complex.norm_real, Real.norm_eq_abs] using hV x

/-- The conjugated `L2` class, represented by `conjugateRepresentative`. -/
noncomputable def conjugateLp (g : L2R) : L2R :=
  (conjugateRepresentative_memLp g).toLp (conjugateRepresentative g)

/-- The conjugated right-hand side as an `L2` class. -/
noncomputable def conjugateRHSLp
    (V : Real -> Real) (hVc : Continuous V) (z : Complex) (g : L2R) {M : Real}
    (hV : forall x, |V x| <= M) : L2R :=
  (conjugateRHS_memLp hVc hV z g).toLp (conjugateRHS V z g)

theorem conjugateLp_coeFn (g : L2R) :
    (conjugateLp g : Real -> Complex) =ᵐ[volume] conjugateRepresentative g :=
  (conjugateRepresentative_memLp g).coeFn_toLp

theorem conjugateRHSLp_coeFn
    {V : Real -> Real} {z : Complex} {g : L2R} {M : Real}
    (hVc : Continuous V) (hV : forall x, |V x| <= M) :
    (conjugateRHSLp V hVc z g hV : Real -> Complex) =ᵐ[volume]
      conjugateRHS V z g :=
  (conjugateRHS_memLp hVc hV z g).coeFn_toLp

/-- Evaluation of the tempered distribution associated to `conjugateLp`. -/
theorem conjugateLp_toTemperedDistribution_apply (g : L2R)
    (phi : SchwartzMap Real Complex) :
    (conjugateLp g : TemperedDistribution Real Complex) phi =
      MeasureTheory.integral volume
        (fun x => conjugateRepresentative g x * phi x) := by
  rw [Lp.toTemperedDistribution_apply]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [conjugateLp_coeFn g] with x hx
  rw [hx]
  exact mul_comm _ _

/-- Evaluation of the `L2` right-hand side as a tempered distribution. -/
theorem conjugateRHSLp_toTemperedDistribution_apply
    {V : Real -> Real} {z : Complex} {g : L2R} {M : Real}
    (hVc : Continuous V) (hV : forall x, |V x| <= M)
    (phi : SchwartzMap Real Complex) :
    (conjugateRHSLp V hVc z g hV : TemperedDistribution Real Complex) phi =
      MeasureTheory.integral volume (fun x => conjugateRHS V z g x * phi x) := by
  rw [Lp.toTemperedDistribution_apply]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [conjugateRHSLp_coeFn hVc hV] with x hx
  rw [hx]
  exact mul_comm _ _

/-- In one dimension, line differentiation in direction one is ordinary
distributional differentiation. -/
theorem lineDeriv_one_eq_deriv (u : TemperedDistribution Real Complex) :
    LineDeriv.lineDerivOp (1 : Real) u =
      TemperedDistribution.derivCLM Complex u := by
  ext phi
  rw [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.derivCLM_apply_apply]
  congr 2

/-- In one real dimension the distributional Laplacian is the iterated
one-dimensional distributional derivative. -/
theorem laplacian_eq_secondDeriv (u : TemperedDistribution Real Complex) :
    Laplacian.laplacian u =
      TemperedDistribution.derivCLM Complex
        (TemperedDistribution.derivCLM Complex u) := by
  rw [TemperedDistribution.laplacian_eq_sum
    (OrthonormalBasis.singleton (Fin 1) Real)]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    OrthonormalBasis.singleton_apply, Finset.sum_const, Finset.card_singleton,
    one_smul, lineDeriv_one_eq_deriv]

/-- `WeakSchrodingerEquation` has the exact expected distributional meaning:
the second distributional derivative of `conj g` is
`((V : C) - conj z) * conj g`, an actual `L2` function.

This is the strongest unconditional regularity statement obtainable directly
from the current weak equation using Mathlib's present distribution API. -/
theorem secondDeriv_conjugateLp_eq_conjugateRHSLp
    (V : Real -> Real) (hVc : Continuous V)
    {M : Real} (hV : forall x, |V x| <= M)
    (z : Complex) (g : L2R) (hweak : WeakSchrodingerEquation V z g) :
    TemperedDistribution.derivCLM Complex
        (TemperedDistribution.derivCLM Complex
          (conjugateLp g : TemperedDistribution Real Complex)) =
      (conjugateRHSLp V hVc z g hV : TemperedDistribution Real Complex) := by
  ext phi
  rw [TemperedDistribution.derivCLM_apply_apply,
    TemperedDistribution.derivCLM_apply_apply]
  rw [conjugateLp_toTemperedDistribution_apply,
    conjugateRHSLp_toTemperedDistribution_apply hVc hV]
  simp only [map_neg, neg_neg, SchwartzMap.derivCLM_apply]
  have hw := hweak phi
  change conj z * MeasureTheory.integral volume
      (fun x => conjugateRepresentative g x * phi x) =
      -MeasureTheory.integral volume
        (fun x => conjugateRepresentative g x * deriv (deriv phi) x) +
        MeasureTheory.integral volume
          (fun x => conjugateRepresentative g x * ((V x : Complex) * phi x)) at hw
  change MeasureTheory.integral volume
      (fun x => conjugateRepresentative g x * deriv (deriv phi) x) =
      MeasureTheory.integral volume (fun x =>
        (((V x : Complex) - conj z) * conjugateRepresentative g x) * phi x)
  have hPraw : Integrable
      (fun x => conjugateRHS V 0 g x * phi x) volume :=
    ((conjugateRHS_memLp hVc hV 0 g).integrable_mul
      (phi.memLp 2 volume))
  have hP : Integrable (fun x =>
      conjugateRepresentative g x * ((V x : Complex) * phi x)) volume := by
    apply hPraw.congr
    filter_upwards with x
    simp only [conjugateRHS, map_zero, Pi.zero_apply, sub_zero]
    ring
  have hC : Integrable (fun x =>
      conjugateRepresentative g x * phi x) volume :=
    ((conjugateRepresentative_memLp g).integrable_mul
      (phi.memLp 2 volume))
  have hpot : MeasureTheory.integral volume (fun x =>
      (((V x : Complex) - conj z) * conjugateRepresentative g x) * phi x) =
        MeasureTheory.integral volume
          (fun x => conjugateRepresentative g x * ((V x : Complex) * phi x)) -
          conj z * MeasureTheory.integral volume
            (fun x => conjugateRepresentative g x * phi x) := by
    calc
      MeasureTheory.integral volume (fun x =>
          (((V x : Complex) - conj z) * conjugateRepresentative g x) * phi x) =
          MeasureTheory.integral volume (fun x =>
            conjugateRepresentative g x * ((V x : Complex) * phi x) -
              conj z * (conjugateRepresentative g x * phi x)) := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with x
                ring
      _ = MeasureTheory.integral volume
            (fun x => conjugateRepresentative g x * ((V x : Complex) * phi x)) -
          MeasureTheory.integral volume
            (fun x => conj z * (conjugateRepresentative g x * phi x)) :=
        MeasureTheory.integral_sub hP (hC.const_mul _)
      _ = MeasureTheory.integral volume
            (fun x => conjugateRepresentative g x * ((V x : Complex) * phi x)) -
          conj z * MeasureTheory.integral volume
            (fun x => conjugateRepresentative g x * phi x) := by
        rw [MeasureTheory.integral_const_mul]
  calc
    MeasureTheory.integral volume
        (fun x => conjugateRepresentative g x * deriv (deriv phi) x) =
        MeasureTheory.integral volume
          (fun x => conjugateRepresentative g x * ((V x : Complex) * phi x)) -
          conj z * MeasureTheory.integral volume
            (fun x => conjugateRepresentative g x * phi x) := by
              linear_combination hw
    _ = MeasureTheory.integral volume (fun x =>
        (((V x : Complex) - conj z) * conjugateRepresentative g x) * phi x) :=
      hpot.symm


end Brockian.WeylWeakRegularityClosed
