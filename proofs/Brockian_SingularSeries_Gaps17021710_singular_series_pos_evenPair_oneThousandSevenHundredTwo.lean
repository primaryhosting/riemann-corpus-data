/-
  Brockian/SingularSeriesGaps17021710.lean — even binary gaps n ∈ {1702, 1704, 1706, 1708, 1710}.

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

namespace Brockian.SingularSeries.Gaps17021710

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSevenHundredTwo : (evenPair 1702).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1702 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredFour : (evenPair 1704).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1704 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredSix : (evenPair 1706).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1706 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredEight : (evenPair 1708).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1708 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredTen : (evenPair 1710).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1710 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSevenHundredTwo : IsAdmissible (evenPair 1702) :=
  isAdmissible_evenPair (by decide : Even 1702)

theorem isAdmissible_evenPair_oneThousandSevenHundredFour : IsAdmissible (evenPair 1704) :=
  isAdmissible_evenPair (by decide : Even 1704)

theorem isAdmissible_evenPair_oneThousandSevenHundredSix : IsAdmissible (evenPair 1706) :=
  isAdmissible_evenPair (by decide : Even 1706)

theorem isAdmissible_evenPair_oneThousandSevenHundredEight : IsAdmissible (evenPair 1708) :=
  isAdmissible_evenPair (by decide : Even 1708)

theorem isAdmissible_evenPair_oneThousandSevenHundredTen : IsAdmissible (evenPair 1710) :=
  isAdmissible_evenPair (by decide : Even 1710)

theorem singular_series_pos_evenPair_oneThousandSevenHundredTwo : 0 < singularSeries (evenPair 1702) :=
  singular_series_pos_evenPair (by decide : Even 1702)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFour : 0 < singularSeries (evenPair 1704) :=
  singular_series_pos_evenPair (by decide : Even 1704)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSix : 0 < singularSeries (evenPair 1706) :=
  singular_series_pos_evenPair (by decide : Even 1706)

theorem singular_series_pos_evenPair_oneThousandSevenHundredEight : 0 < singularSeries (evenPair 1708) :=
  singular_series_pos_evenPair (by decide : Even 1708)

theorem singular_series_pos_evenPair_oneThousandSevenHundredTen : 0 < singularSeries (evenPair 1710) :=
  singular_series_pos_evenPair (by decide : Even 1710)

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1702) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1702) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1704) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1704) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1706) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1706) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1708) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1708) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1710) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1710) P

theorem nu_p_oneThousandSevenHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1702) p = if p = 2 ∨ p ∣ 1702 then 1 else 2 :=
  nu_p_evenPair (by decide : (1702 : ℕ) ≠ 0) (by decide : Even 1702) hp

theorem nu_p_oneThousandSevenHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1704) p = if p = 2 ∨ p ∣ 1704 then 1 else 2 :=
  nu_p_evenPair (by decide : (1704 : ℕ) ≠ 0) (by decide : Even 1704) hp

theorem nu_p_oneThousandSevenHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1706) p = if p = 2 ∨ p ∣ 1706 then 1 else 2 :=
  nu_p_evenPair (by decide : (1706 : ℕ) ≠ 0) (by decide : Even 1706) hp

theorem nu_p_oneThousandSevenHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1708) p = if p = 2 ∨ p ∣ 1708 then 1 else 2 :=
  nu_p_evenPair (by decide : (1708 : ℕ) ≠ 0) (by decide : Even 1708) hp

theorem nu_p_oneThousandSevenHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1710) p = if p = 2 ∨ p ∣ 1710 then 1 else 2 :=
  nu_p_evenPair (by decide : (1710 : ℕ) ≠ 0) (by decide : Even 1710) hp

theorem nu_p_oneThousandSevenHundredTwo_two : nu_p (evenPair 1702) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1702)

theorem localFactor_oneThousandSevenHundredTwo_two : localFactor (evenPair 1702) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1702 : ℕ) ≠ 0) (by decide : Even 1702)

theorem nu_p_oneThousandSevenHundredTen_two : nu_p (evenPair 1710) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1710)

theorem localFactor_oneThousandSevenHundredTen_two : localFactor (evenPair 1710) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1710 : ℕ) ≠ 0) (by decide : Even 1710)

end Brockian.SingularSeries.Gaps17021710
