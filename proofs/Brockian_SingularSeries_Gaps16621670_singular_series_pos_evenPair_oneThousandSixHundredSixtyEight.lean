/-
  Brockian/SingularSeriesGaps16621670.lean — even binary gaps n ∈ {1662, 1664, 1666, 1668, 1670}.

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

namespace Brockian.SingularSeries.Gaps16621670

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixHundredSixtyTwo : (evenPair 1662).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1662 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredSixtyFour : (evenPair 1664).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1664 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredSixtySix : (evenPair 1666).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1666 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredSixtyEight : (evenPair 1668).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1668 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredSeventy : (evenPair 1670).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1670 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixHundredSixtyTwo : IsAdmissible (evenPair 1662) :=
  isAdmissible_evenPair (by decide : Even 1662)

theorem isAdmissible_evenPair_oneThousandSixHundredSixtyFour : IsAdmissible (evenPair 1664) :=
  isAdmissible_evenPair (by decide : Even 1664)

theorem isAdmissible_evenPair_oneThousandSixHundredSixtySix : IsAdmissible (evenPair 1666) :=
  isAdmissible_evenPair (by decide : Even 1666)

theorem isAdmissible_evenPair_oneThousandSixHundredSixtyEight : IsAdmissible (evenPair 1668) :=
  isAdmissible_evenPair (by decide : Even 1668)

theorem isAdmissible_evenPair_oneThousandSixHundredSeventy : IsAdmissible (evenPair 1670) :=
  isAdmissible_evenPair (by decide : Even 1670)

theorem singular_series_pos_evenPair_oneThousandSixHundredSixtyTwo : 0 < singularSeries (evenPair 1662) :=
  singular_series_pos_evenPair (by decide : Even 1662)

theorem singular_series_pos_evenPair_oneThousandSixHundredSixtyFour : 0 < singularSeries (evenPair 1664) :=
  singular_series_pos_evenPair (by decide : Even 1664)

theorem singular_series_pos_evenPair_oneThousandSixHundredSixtySix : 0 < singularSeries (evenPair 1666) :=
  singular_series_pos_evenPair (by decide : Even 1666)

theorem singular_series_pos_evenPair_oneThousandSixHundredSixtyEight : 0 < singularSeries (evenPair 1668) :=
  singular_series_pos_evenPair (by decide : Even 1668)

theorem singular_series_pos_evenPair_oneThousandSixHundredSeventy : 0 < singularSeries (evenPair 1670) :=
  singular_series_pos_evenPair (by decide : Even 1670)

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1662) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1662) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1664) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1664) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1666) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1666) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1668) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1668) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1670) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1670) P

theorem nu_p_oneThousandSixHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1662) p = if p = 2 ∨ p ∣ 1662 then 1 else 2 :=
  nu_p_evenPair (by decide : (1662 : ℕ) ≠ 0) (by decide : Even 1662) hp

theorem nu_p_oneThousandSixHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1664) p = if p = 2 ∨ p ∣ 1664 then 1 else 2 :=
  nu_p_evenPair (by decide : (1664 : ℕ) ≠ 0) (by decide : Even 1664) hp

theorem nu_p_oneThousandSixHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1666) p = if p = 2 ∨ p ∣ 1666 then 1 else 2 :=
  nu_p_evenPair (by decide : (1666 : ℕ) ≠ 0) (by decide : Even 1666) hp

theorem nu_p_oneThousandSixHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1668) p = if p = 2 ∨ p ∣ 1668 then 1 else 2 :=
  nu_p_evenPair (by decide : (1668 : ℕ) ≠ 0) (by decide : Even 1668) hp

theorem nu_p_oneThousandSixHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1670) p = if p = 2 ∨ p ∣ 1670 then 1 else 2 :=
  nu_p_evenPair (by decide : (1670 : ℕ) ≠ 0) (by decide : Even 1670) hp

theorem nu_p_oneThousandSixHundredSixtyTwo_two : nu_p (evenPair 1662) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1662)

theorem localFactor_oneThousandSixHundredSixtyTwo_two : localFactor (evenPair 1662) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1662 : ℕ) ≠ 0) (by decide : Even 1662)

theorem nu_p_oneThousandSixHundredSeventy_two : nu_p (evenPair 1670) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1670)

theorem localFactor_oneThousandSixHundredSeventy_two : localFactor (evenPair 1670) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1670 : ℕ) ≠ 0) (by decide : Even 1670)

end Brockian.SingularSeries.Gaps16621670
