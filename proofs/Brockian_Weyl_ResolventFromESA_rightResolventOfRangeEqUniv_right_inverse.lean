/-
  Brockian/WeylResolventFromESA.lean

  Resolvent construction for the Kato--Rellich lane.

  The tempting theorem "ESA T gives bounded right resolvents for `T ± i` on the
  original domain" is too strong for an arbitrary essentially self-adjoint core:
  ESA gives dense shifted ranges for the core, while the everywhere-defined
  resolvents live on the self-adjoint closure.  This file proves the honest
  closed-range version needed by the existing Neumann/Kato transfer:

    * ESA + closed shifted ranges -> shifted ranges are all of H;
    * all shifted ranges + symmetry -> bounded right resolvents with norm <= 1.

  No inverse is postulated.  The inverse is obtained from the surjective shifted
  linear map on `T.domain`, and the `|Im z| * ‖v‖ <= ‖(T-z)v‖` inequality gives
  the norm bound needed to package it as a `ContinuousLinearMap`.
-/
import Mathlib
import Brockian.WeylCayley
import Brockian.WeylClosedRange
import Brockian.WeylKatoRellichScaffold
import Brockian.WeylKatoRellichTransfer
import Brockian.WeylKatoResolventPackage
import Brockian.WeylKatoRangeDensity
import Brockian.WeylOperator

namespace Brockian.Weyl.ResolventFromESA

open scoped InnerProductSpace
open Brockian.Weyl.Operator
open Brockian.Weyl.Cayley
open Brockian.Weyl.ClosedRange
open Brockian.Weyl.KatoRellichScaffold
open Brockian.Weyl.KatoResolventPackage
open Brockian.Weyl.KatoUnbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Shifted maps and their inverse bounds -/

/-- The honest linear map `v ↦ T v - w v` on `T.domain`. -/
noncomputable def shiftedMap (T : H →ₗ.[ℂ] H) (w : ℂ) : T.domain →ₗ[ℂ] H :=
  T.toFun - w • T.domain.subtype

@[simp] theorem shiftedMap_apply (T : H →ₗ.[ℂ] H) (w : ℂ) (v : T.domain) :
    shiftedMap T w v = T v - w • (v : H) :=
  rfl

/-- Set-level surjectivity of `rangeSMulSub T w` is the same as surjectivity of
the shifted linear map on the domain. -/
theorem shiftedMap_surjective_of_range_eq_univ
    {T : H →ₗ.[ℂ] H} {w : ℂ}
    (hrange : (rangeSMulSub T w : Set H) = Set.univ) :
    Function.Surjective (shiftedMap T w) := by
  intro y
  have hy : y ∈ (rangeSMulSub T w : Set H) := by
    rw [hrange]
    exact Set.mem_univ y
  obtain ⟨v, hv⟩ := mem_rangeSMulSub.mp hy
  exact ⟨v, by simpa [shiftedMap] using hv⟩

/-- For non-real `w`, symmetry bounds the inverse of the shifted map on its
range.  At `w = ±i`, this is the sharp `‖v‖ <= ‖(T-w)v‖` estimate. -/
theorem norm_le_inv_im_mul_norm_shifted
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T) {w : ℂ} (hw : w.im ≠ 0)
    (v : T.domain) :
    ‖(v : H)‖ ≤ |w.im|⁻¹ * ‖shiftedMap T w v‖ := by
  have hineq := hT.norm_sub_smul_ge v w
  have hpos : 0 < |w.im| := abs_pos.mpr hw
  have hnonneg : 0 ≤ ‖(v : H)‖ := norm_nonneg _
  have hdiv : ‖(v : H)‖ ≤ ‖T v - w • (v : H)‖ / |w.im| := by
    exact (le_div_iff₀' hpos).mpr hineq
  calc
    ‖(v : H)‖ ≤ ‖T v - w • (v : H)‖ / |w.im| := hdiv
    _ = |w.im|⁻¹ * ‖shiftedMap T w v‖ := by
      rw [shiftedMap_apply, div_eq_inv_mul, mul_comm]

/-- A surjective shifted map has a linear right inverse. -/
noncomputable def shiftedRightInverseLinearMap
    (T : H →ₗ.[ℂ] H) (w : ℂ)
    (hsurj : Function.Surjective (shiftedMap T w)) : H →ₗ[ℂ] T.domain :=
  Classical.choose ((shiftedMap T w).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj))

/-- The chosen linear inverse right-inverts the shifted map. -/
theorem shiftedRightInverseLinearMap_spec
    (T : H →ₗ.[ℂ] H) (w : ℂ)
    (hsurj : Function.Surjective (shiftedMap T w)) :
    (shiftedMap T w).comp (shiftedRightInverseLinearMap T w hsurj) = LinearMap.id :=
  Classical.choose_spec ((shiftedMap T w).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj))

/-- The chosen inverse, as an `H`-valued linear map. -/
noncomputable def shiftedResolventLinearMap
    (T : H →ₗ.[ℂ] H) (w : ℂ)
    (hsurj : Function.Surjective (shiftedMap T w)) : H →ₗ[ℂ] H :=
  T.domain.subtype.comp (shiftedRightInverseLinearMap T w hsurj)

/-- The `H`-valued inverse lands in `T.domain`. -/
theorem shiftedResolventLinearMap_maps_domain
    (T : H →ₗ.[ℂ] H) (w : ℂ)
    (hsurj : Function.Surjective (shiftedMap T w)) (y : H) :
    shiftedResolventLinearMap T w hsurj y ∈ T.domain :=
  (shiftedRightInverseLinearMap T w hsurj y).2

/-- The `H`-valued inverse is a right inverse for `T - w`. -/
theorem shiftedResolventLinearMap_right_inverse
    (T : H →ₗ.[ℂ] H) (w : ℂ)
    (hsurj : Function.Surjective (shiftedMap T w)) (y : H) :
    T ⟨shiftedResolventLinearMap T w hsurj y,
        shiftedResolventLinearMap_maps_domain T w hsurj y⟩
      - w • shiftedResolventLinearMap T w hsurj y = y := by
  have hspec := congrArg (fun f : H →ₗ[ℂ] H => f y)
    (shiftedRightInverseLinearMap_spec T w hsurj)
  simpa [shiftedResolventLinearMap, shiftedMap] using hspec

/-- The inverse has operator bound `1 / |Im w|`. -/
theorem shiftedResolventLinearMap_bound
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T) {w : ℂ} (hw : w.im ≠ 0)
    (hsurj : Function.Surjective (shiftedMap T w)) (y : H) :
    ‖shiftedResolventLinearMap T w hsurj y‖ ≤ |w.im|⁻¹ * ‖y‖ := by
  have hbound := norm_le_inv_im_mul_norm_shifted hT hw
    (shiftedRightInverseLinearMap T w hsurj y)
  have hright : shiftedMap T w (shiftedRightInverseLinearMap T w hsurj y) = y := by
    have hspec := congrArg (fun f : H →ₗ[ℂ] H => f y)
      (shiftedRightInverseLinearMap_spec T w hsurj)
    simpa using hspec
  simpa [shiftedResolventLinearMap, hright] using hbound

/-- The bounded right resolvent for `T - w`, provided the shifted range is all of
`H`.  Its norm is bounded by `1 / |Im w|`. -/
noncomputable def rightResolventOfRangeEqUniv
    (T : H →ₗ.[ℂ] H) (hT : IsSymmetric T) (w : ℂ) (hw : w.im ≠ 0)
    (hrange : (rangeSMulSub T w : Set H) = Set.univ) : H →L[ℂ] H :=
  let hsurj := shiftedMap_surjective_of_range_eq_univ (T := T) (w := w) hrange
  (shiftedResolventLinearMap T w hsurj).mkContinuous |w.im|⁻¹
    (shiftedResolventLinearMap_bound hT hw hsurj)

/-- The constructed bounded map lands in the domain. -/
theorem rightResolventOfRangeEqUniv_maps_domain
    (T : H →ₗ.[ℂ] H) (hT : IsSymmetric T) (w : ℂ) (hw : w.im ≠ 0)
    (hrange : (rangeSMulSub T w : Set H) = Set.univ) (y : H) :
    rightResolventOfRangeEqUniv T hT w hw hrange y ∈ T.domain :=
  shiftedResolventLinearMap_maps_domain T w
    (shiftedMap_surjective_of_range_eq_univ (T := T) (w := w) hrange) y

/-- The constructed bounded map right-inverts `T - w`. -/
theorem rightResolventOfRangeEqUniv_right_inverse
    (T : H →ₗ.[ℂ] H) (hT : IsSymmetric T) (w : ℂ) (hw : w.im ≠ 0)
    (hrange : (rangeSMulSub T w : Set H) = Set.univ) (y : H) :
    T ⟨rightResolventOfRangeEqUniv T hT w hw hrange y,
        rightResolventOfRangeEqUniv_maps_domain T hT w hw hrange y⟩
      - w • rightResolventOfRangeEqUniv T hT w hw hrange y = y :=
  shiftedResolventLinearMap_right_inverse T w
    (shiftedMap_surjective_of_range_eq_univ (T := T) (w := w) hrange) y

/-- The constructed bounded map has the expected norm bound. -/
theorem norm_rightResolventOfRangeEqUniv_le
    (T : H →ₗ.[ℂ] H) (hT : IsSymmetric T) (w : ℂ) (hw : w.im ≠ 0)
    (hrange : (rangeSMulSub T w : Set H) = Set.univ) :
    ‖rightResolventOfRangeEqUniv T hT w hw hrange‖ ≤ |w.im|⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr (abs_nonneg _))
    (shiftedResolventLinearMap_bound hT hw
      (shiftedMap_surjective_of_range_eq_univ (T := T) (w := w) hrange))

/-- Packaging: full shifted range gives a bounded right resolvent. -/
theorem exists_rightResolvent_of_range_eq_univ
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T) {w : ℂ} (hw : w.im ≠ 0)
    (hrange : (rangeSMulSub T w : Set H) = Set.univ) :
    ∃ R : H →L[ℂ] H,
      RightResolvent T w R ∧ ‖R‖ ≤ |w.im|⁻¹ := by
  refine ⟨rightResolventOfRangeEqUniv T hT w hw hrange, ?_, ?_⟩
  · exact
      { maps_domain := rightResolventOfRangeEqUniv_maps_domain T hT w hw hrange
        right_inverse := rightResolventOfRangeEqUniv_right_inverse T hT w hw hrange }
  · exact norm_rightResolventOfRangeEqUniv_le T hT w hw hrange

/-! ### The `± i` resolvents used by the Kato lane -/

/-- If both shifted ranges are all of `H`, then `T ± i` have bounded right
resolvents with norm at most `1`. -/
theorem rightResolvents_of_surjective_shifted_ranges
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hadd : (rangeAddI T : Set H) = Set.univ)
    (hsub : (rangeSubI T : Set H) = Set.univ) :
    ∃ Radd Rsub : H →L[ℂ] H,
      RightResolvent T (-Complex.I) Radd ∧
      RightResolvent T Complex.I Rsub ∧
      ‖Radd‖ ≤ 1 ∧ ‖Rsub‖ ≤ 1 := by
  have hwadd : (-Complex.I).im ≠ 0 := by
    rw [Complex.neg_im, Complex.I_im]
    exact neg_ne_zero.mpr one_ne_zero
  have hwsub : Complex.I.im ≠ 0 := by
    rw [Complex.I_im]
    exact one_ne_zero
  obtain ⟨Radd, hRadd, hnadd⟩ :=
    exists_rightResolvent_of_range_eq_univ hT hwadd (by simpa [rangeAddI] using hadd)
  obtain ⟨Rsub, hRsub, hnsub⟩ :=
    exists_rightResolvent_of_range_eq_univ hT hwsub (by simpa [rangeSubI] using hsub)
  refine ⟨Radd, Rsub, hRadd, hRsub, ?_, ?_⟩
  · have hnorm : |(-Complex.I).im|⁻¹ = (1 : ℝ) := by norm_num [Complex.I_im]
    simpa [hnorm] using hnadd
  · have hnorm : |Complex.I.im|⁻¹ = (1 : ℝ) := by norm_num [Complex.I_im]
    simpa [hnorm] using hnsub

/-- ESA plus closed shifted ranges gives the bounded right resolvents required by
the Kato/Neumann transfer.  This is the honest closed-range form of the classical
resolvent construction for an essentially self-adjoint operator. -/
theorem rightResolvents_of_essentiallySelfAdjoint_of_isClosed_ranges
    {T : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H))
    (hT : IsSymmetric T) (hESA : EssentiallySelfAdjoint T)
    (hcl_add : IsClosed (rangeAddI T : Set H))
    (hcl_sub : IsClosed (rangeSubI T : Set H)) :
    ∃ Radd Rsub : H →L[ℂ] H,
      RightResolvent T (-Complex.I) Radd ∧
      RightResolvent T Complex.I Rsub ∧
      ‖Radd‖ ≤ 1 ∧ ‖Rsub‖ ≤ 1 := by
  have hranges :=
    range_eq_top_of_essentiallySelfAdjoint_of_isClosed_ranges hd hESA hcl_add hcl_sub
  exact rightResolvents_of_surjective_shifted_ranges hT hranges.1 hranges.2

/-! ### Packaging into the Kato resolvent API -/

/-- Surjective shifted ranges produce the `ResolventAtI` package used by the
norm-small Kato transfer.

This is a `def`, not a theorem: `ResolventAtI T` carries the actual bounded
operators, so it lives in `Type`. -/
noncomputable def resolventAtIOfSurjectiveShiftedRanges
    {T : H →ₗ.[ℂ] H} (hT : IsSymmetric T)
    (hadd : (rangeAddI T : Set H) = Set.univ)
    (hsub : (rangeSubI T : Set H) = Set.univ) :
    ResolventAtI T :=
  let hwadd : (-Complex.I).im ≠ 0 := by
    rw [Complex.neg_im, Complex.I_im]
    exact neg_ne_zero.mpr one_ne_zero
  let hwsub : Complex.I.im ≠ 0 := by
    rw [Complex.I_im]
    exact one_ne_zero
  let Radd := rightResolventOfRangeEqUniv T hT (-Complex.I) hwadd
    (by simpa [rangeAddI] using hadd)
  let Rsub := rightResolventOfRangeEqUniv T hT Complex.I hwsub
    (by simpa [rangeSubI] using hsub)
  { Radd := Radd
    Rsub := Rsub
    right_add :=
      { maps_domain :=
          rightResolventOfRangeEqUniv_maps_domain T hT (-Complex.I) hwadd
            (by simpa [rangeAddI] using hadd)
        right_inverse :=
          rightResolventOfRangeEqUniv_right_inverse T hT (-Complex.I) hwadd
            (by simpa [rangeAddI] using hadd) }
    right_sub :=
      { maps_domain :=
          rightResolventOfRangeEqUniv_maps_domain T hT Complex.I hwsub
            (by simpa [rangeSubI] using hsub)
        right_inverse :=
          rightResolventOfRangeEqUniv_right_inverse T hT Complex.I hwsub
            (by simpa [rangeSubI] using hsub) }
    norm_add := by
      have hn :=
        norm_rightResolventOfRangeEqUniv_le T hT (-Complex.I) hwadd
          (by simpa [rangeAddI] using hadd)
      have hnorm : |(-Complex.I).im|⁻¹ = (1 : ℝ) := by norm_num [Complex.I_im]
      simpa [Radd, hnorm] using hn
    norm_sub := by
      have hn :=
        norm_rightResolventOfRangeEqUniv_le T hT Complex.I hwsub
          (by simpa [rangeSubI] using hsub)
      have hnorm : |Complex.I.im|⁻¹ = (1 : ℝ) := by norm_num [Complex.I_im]
      simpa [Rsub, hnorm] using hn }

/-- ESA plus closed shifted ranges produces the `ResolventAtI` package.  The
closed-range hypotheses are the remaining classical unbounded-operator input. -/
noncomputable def resolventAtIOfEssentiallySelfAdjointOfIsClosedRanges
    {T : H →ₗ.[ℂ] H} (hd : Dense (T.domain : Set H))
    (hT : IsSymmetric T) (hESA : EssentiallySelfAdjoint T)
    (hcl_add : IsClosed (rangeAddI T : Set H))
    (hcl_sub : IsClosed (rangeSubI T : Set H)) :
    ResolventAtI T :=
  let hranges :=
    range_eq_top_of_essentiallySelfAdjoint_of_isClosed_ranges
      hd hESA hcl_add hcl_sub
  resolventAtIOfSurjectiveShiftedRanges hT hranges.1 hranges.2

/-- **Closed-range Kato transfer.** An essentially self-adjoint symmetric `T`
whose shifted ranges are closed admits the norm-small bounded perturbation
transfer.  This is the strongest Kato route currently supported without
Mathlib's self-adjoint-closure resolvent theorem. -/
theorem essentiallySelfAdjoint_perturb_of_essentiallySelfAdjoint_of_isClosed_ranges
    {T : H →ₗ.[ℂ] H} {B : H →L[ℂ] H}
    (hd : Dense (T.domain : Set H))
    (hT : IsSymmetric T) (hESA : EssentiallySelfAdjoint T)
    (hcl_add : IsClosed (rangeAddI T : Set H))
    (hcl_sub : IsClosed (rangeSubI T : Set H))
    (hBsmall : ‖B‖ < 1) :
    EssentiallySelfAdjoint (perturb T B) :=
  essentiallySelfAdjoint_perturb_of_resolventAtI hd
    (resolventAtIOfEssentiallySelfAdjointOfIsClosedRanges
      hd hT hESA hcl_add hcl_sub)
    hBsmall

end Brockian.Weyl.ResolventFromESA
