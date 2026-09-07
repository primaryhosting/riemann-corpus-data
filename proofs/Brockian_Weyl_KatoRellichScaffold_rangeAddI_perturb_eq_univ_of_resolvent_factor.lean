/-
  Brockian/WeylKatoRellichScaffold.lean — resolvent/range packaging for the
  Kato--Rellich lane.

  This file does not prove the full unbounded Kato--Rellich theorem.  It records
  the honest algebraic part of the Neumann/resolvent route:

      if `R` is a right inverse for `T - w`, and `S` is a right inverse for
      `I + B R`, then `R S` is a right inverse for `(T+B) - w`.

  Consequently the shifted perturbed range is all of `H`, hence dense.  The
  missing analytic step is exactly the production of the bounded factor inverse
  `S` from small-norm/resolvent estimates for a genuinely unbounded operator.
-/
import Mathlib
import Brockian.WeylKatoUnbounded
import Brockian.WeylKatoRangeDensity

namespace Brockian.Weyl.KatoRellichScaffold

open scoped InnerProductSpace
open Brockian.Weyl.Cayley
open Brockian.Weyl.KatoUnbounded

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Right-resolvent and bounded-factor packaging -/

/-- A bounded right resolvent for the shifted partial operator `T - w`: the
bounded map `R` lands in `dom T` and solves `(T - w) (R y) = y` for every `y`.

This is intentionally one-sided.  It is the exact input needed to prove
surjectivity of the shifted range without asserting a full inverse or closed
operator theory. -/
structure RightResolvent (T : H →ₗ.[ℂ] H) (w : ℂ) (R : H →L[ℂ] H) : Prop where
  maps_domain : ∀ y : H, R y ∈ T.domain
  right_inverse : ∀ y : H, T ⟨R y, maps_domain y⟩ - w • R y = y

/-- A named right-inverse predicate for continuous linear maps. -/
def CLMRightInverse (L S : H →L[ℂ] H) : Prop :=
  ∀ y : H, L (S y) = y

/-- The bounded factor in the resolvent identity: `I + B R`. -/
noncomputable def katoFactor (B R : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 : H →L[ℂ] H) + B.comp R

/-! ### Algebraic resolvent transfer -/

/-- **Algebraic Kato resolvent step.** If `R` right-inverts `T - w` and `S`
right-inverts the bounded factor `I + B R`, then `R S` right-inverts
`(T+B) - w`.

This is the faithful Lean form of
`(T+B-w) R S = ((T-w)R + B R)S = (I + B R)S = I`. -/
theorem rightResolvent_perturb_of_factor_rightInverse
    {T : H →ₗ.[ℂ] H} {B R S : H →L[ℂ] H} {w : ℂ}
    (hR : RightResolvent T w R)
    (hS : CLMRightInverse (katoFactor B R) S) :
    RightResolvent (perturb T B) w (R.comp S) where
  maps_domain y := by
    rw [perturb_domain]
    exact hR.maps_domain (S y)
  right_inverse y := by
    have hbase := hR.right_inverse (S y)
    have hfactor := hS y
    change B (R (S y)) + T ⟨R (S y), _⟩ - w • R (S y) = y
    calc
      B (R (S y)) + T ⟨R (S y), _⟩ - w • R (S y)
          = (T ⟨R (S y), hR.maps_domain (S y)⟩ - w • R (S y)) + B (R (S y)) := by
            abel
      _ = S y + B (R (S y)) := by rw [hbase]
      _ = katoFactor B R (S y) := by
            simp [katoFactor, ContinuousLinearMap.comp_apply, add_comm]
      _ = y := hfactor

/-- A right resolvent makes the shifted range equal to the whole space. -/
theorem rangeSMulSub_eq_univ_of_rightResolvent
    {T : H →ₗ.[ℂ] H} {R : H →L[ℂ] H} {w : ℂ}
    (hR : RightResolvent T w R) :
    (rangeSMulSub T w : Set H) = Set.univ := by
  ext y
  constructor
  · intro _; exact Set.mem_univ y
  · intro _
    rw [SetLike.mem_coe, mem_rangeSMulSub]
    exact ⟨⟨R y, hR.maps_domain y⟩, hR.right_inverse y⟩

/-- A right resolvent gives dense shifted range. -/
theorem dense_rangeSMulSub_of_rightResolvent
    {T : H →ₗ.[ℂ] H} {R : H →L[ℂ] H} {w : ℂ}
    (hR : RightResolvent T w R) :
    Dense (rangeSMulSub T w : Set H) := by
  rw [rangeSMulSub_eq_univ_of_rightResolvent hR]
  exact dense_univ

/-! ### `± i` range consequences for the Kato lane -/

/-- Surjectivity of the perturbed `+i` range from a right resolvent for
`T + i` and a right inverse for the corresponding bounded factor. -/
theorem rangeAddI_perturb_eq_univ_of_resolvent_factor
    {T : H →ₗ.[ℂ] H} {B R S : H →L[ℂ] H}
    (hR : RightResolvent T (-Complex.I) R)
    (hS : CLMRightInverse (katoFactor B R) S) :
    (rangeAddI (perturb T B) : Set H) = Set.univ := by
  exact rangeSMulSub_eq_univ_of_rightResolvent
    (rightResolvent_perturb_of_factor_rightInverse (B := B) hR hS)

/-- Surjectivity of the perturbed `-i` range from a right resolvent for
`T - i` and a right inverse for the corresponding bounded factor. -/
theorem rangeSubI_perturb_eq_univ_of_resolvent_factor
    {T : H →ₗ.[ℂ] H} {B R S : H →L[ℂ] H}
    (hR : RightResolvent T Complex.I R)
    (hS : CLMRightInverse (katoFactor B R) S) :
    (rangeSubI (perturb T B) : Set H) = Set.univ := by
  exact rangeSMulSub_eq_univ_of_rightResolvent
    (rightResolvent_perturb_of_factor_rightInverse (B := B) hR hS)

/-- The Kato transfer hypothesis follows from right resolvents for `T ± i` plus
right inverses for the bounded factors `I + B R±`.  This is the range-density
form of the Neumann/resolvent route, with the analytic inverse construction left
as an explicit hypothesis. -/
theorem boundedPerturbationTransfer_of_resolvent_factors
    {T : H →ₗ.[ℂ] H} {B Radd Rsub Sadd Ssub : H →L[ℂ] H}
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hSadd : CLMRightInverse (katoFactor B Radd) Sadd)
    (hRsub : RightResolvent T Complex.I Rsub)
    (hSsub : CLMRightInverse (katoFactor B Rsub) Ssub) :
    BoundedPerturbationTransfer T B := by
  constructor
  · rw [rangeAddI_perturb_eq_univ_of_resolvent_factor hRadd hSadd]
    exact dense_univ
  · rw [rangeSubI_perturb_eq_univ_of_resolvent_factor hRsub hSsub]
    exact dense_univ

/-! ### Zero-factor sanity checks -/

/-- For the zero perturbation, the factor `I + 0 R` is right-inverted by `I`. -/
theorem factorRightInverse_zero (R : H →L[ℂ] H) :
    CLMRightInverse (katoFactor (0 : H →L[ℂ] H) R) (1 : H →L[ℂ] H) := by
  intro y
  simp [CLMRightInverse, katoFactor]

/-- If `T ± i` already have bounded right resolvents, then the zero perturbation
discharges `BoundedPerturbationTransfer`.  This is a base-case check for the
resolvent-factor packaging, not a Kato--Rellich theorem. -/
theorem boundedPerturbationTransfer_zero_of_rightResolvents
    {T : H →ₗ.[ℂ] H} {Radd Rsub : H →L[ℂ] H}
    (hRadd : RightResolvent T (-Complex.I) Radd)
    (hRsub : RightResolvent T Complex.I Rsub) :
    BoundedPerturbationTransfer T (0 : H →L[ℂ] H) :=
  boundedPerturbationTransfer_of_resolvent_factors
    hRadd (factorRightInverse_zero Radd) hRsub (factorRightInverse_zero Rsub)

end Brockian.Weyl.KatoRellichScaffold
