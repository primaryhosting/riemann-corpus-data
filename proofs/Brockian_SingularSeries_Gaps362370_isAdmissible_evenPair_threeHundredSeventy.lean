/-
  Brockian/SingularSeriesGaps362370.lean — even binary gaps n ∈ {362, 364, 366, 368, 370}.

  HONEST SCOPE: finite/local singular-series arithmetic only.
  Does NOT claim twin-prime / HL asymptotics / Goldbach transfer / infinitude.
-/
import Mathlib
import Brockian.SingularSeries
import Brockian.SingularSeriesWire
import Brockian.SingularSeriesExamples
import Brockian.SingularSeriesMoreExamples

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Classical
open Real Finset
open Brockian.SingularSeries
open Brockian.SingularSeries.Wire
open Brockian.SingularSeries.Examples
open Brockian.SingularSeries.MoreExamples

namespace Brockian.SingularSeries.Gaps362370

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_threeHundredSixtyTwo : (evenPair 362).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (362 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredSixtyFour : (evenPair 364).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (364 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredSixtySix : (evenPair 366).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (366 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredSixtyEight : (evenPair 368).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (368 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredSeventy : (evenPair 370).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (370 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_threeHundredSixtyTwo : IsAdmissible (evenPair 362) :=
  isAdmissible_evenPair (by decide : Even 362)

theorem isAdmissible_evenPair_threeHundredSixtyFour : IsAdmissible (evenPair 364) :=
  isAdmissible_evenPair (by decide : Even 364)

theorem isAdmissible_evenPair_threeHundredSixtySix : IsAdmissible (evenPair 366) :=
  isAdmissible_evenPair (by decide : Even 366)

theorem isAdmissible_evenPair_threeHundredSixtyEight : IsAdmissible (evenPair 368) :=
  isAdmissible_evenPair (by decide : Even 368)

theorem isAdmissible_evenPair_threeHundredSeventy : IsAdmissible (evenPair 370) :=
  isAdmissible_evenPair (by decide : Even 370)

theorem singular_series_pos_evenPair_threeHundredSixtyTwo : 0 < singularSeries (evenPair 362) :=
  singular_series_pos_evenPair (by decide : Even 362)

theorem singular_series_pos_evenPair_threeHundredSixtyFour : 0 < singularSeries (evenPair 364) :=
  singular_series_pos_evenPair (by decide : Even 364)

theorem singular_series_pos_evenPair_threeHundredSixtySix : 0 < singularSeries (evenPair 366) :=
  singular_series_pos_evenPair (by decide : Even 366)

theorem singular_series_pos_evenPair_threeHundredSixtyEight : 0 < singularSeries (evenPair 368) :=
  singular_series_pos_evenPair (by decide : Even 368)

theorem singular_series_pos_evenPair_threeHundredSeventy : 0 < singularSeries (evenPair 370) :=
  singular_series_pos_evenPair (by decide : Even 370)

theorem singular_series_finite_pos_evenPair_threeHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 362) P :=
  singular_series_finite_pos_evenPair (by decide : Even 362) P

theorem singular_series_finite_pos_evenPair_threeHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 364) P :=
  singular_series_finite_pos_evenPair (by decide : Even 364) P

theorem singular_series_finite_pos_evenPair_threeHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 366) P :=
  singular_series_finite_pos_evenPair (by decide : Even 366) P

theorem singular_series_finite_pos_evenPair_threeHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 368) P :=
  singular_series_finite_pos_evenPair (by decide : Even 368) P

theorem singular_series_finite_pos_evenPair_threeHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 370) P :=
  singular_series_finite_pos_evenPair (by decide : Even 370) P

theorem nu_p_threeHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 362) p = if p = 2 ∨ p ∣ 362 then 1 else 2 :=
  nu_p_evenPair (by decide : (362 : ℕ) ≠ 0) (by decide : Even 362) hp

theorem nu_p_threeHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 364) p = if p = 2 ∨ p ∣ 364 then 1 else 2 :=
  nu_p_evenPair (by decide : (364 : ℕ) ≠ 0) (by decide : Even 364) hp

theorem nu_p_threeHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 366) p = if p = 2 ∨ p ∣ 366 then 1 else 2 :=
  nu_p_evenPair (by decide : (366 : ℕ) ≠ 0) (by decide : Even 366) hp

theorem nu_p_threeHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 368) p = if p = 2 ∨ p ∣ 368 then 1 else 2 :=
  nu_p_evenPair (by decide : (368 : ℕ) ≠ 0) (by decide : Even 368) hp

theorem nu_p_threeHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 370) p = if p = 2 ∨ p ∣ 370 then 1 else 2 :=
  nu_p_evenPair (by decide : (370 : ℕ) ≠ 0) (by decide : Even 370) hp

theorem nu_p_threeHundredSixtyTwo_two : nu_p (evenPair 362) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 362)

theorem localFactor_threeHundredSixtyTwo_two : localFactor (evenPair 362) 2 = 2 :=
  localFactor_evenPair_two (by decide : (362 : ℕ) ≠ 0) (by decide : Even 362)

theorem nu_p_threeHundredSeventy_two : nu_p (evenPair 370) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 370)

theorem localFactor_threeHundredSeventy_two : localFactor (evenPair 370) 2 = 2 :=
  localFactor_evenPair_two (by decide : (370 : ℕ) ≠ 0) (by decide : Even 370)

end Brockian.SingularSeries.Gaps362370
