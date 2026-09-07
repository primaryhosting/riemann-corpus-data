/-
  Brockian/SingularSeriesGaps16021610.lean — even binary gaps n ∈ {1602, 1604, 1606, 1608, 1610}.

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

namespace Brockian.SingularSeries.Gaps16021610

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixHundredTwo : (evenPair 1602).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1602 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredFour : (evenPair 1604).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1604 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredSix : (evenPair 1606).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1606 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredEight : (evenPair 1608).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1608 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredTen : (evenPair 1610).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1610 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixHundredTwo : IsAdmissible (evenPair 1602) :=
  isAdmissible_evenPair (by decide : Even 1602)

theorem isAdmissible_evenPair_oneThousandSixHundredFour : IsAdmissible (evenPair 1604) :=
  isAdmissible_evenPair (by decide : Even 1604)

theorem isAdmissible_evenPair_oneThousandSixHundredSix : IsAdmissible (evenPair 1606) :=
  isAdmissible_evenPair (by decide : Even 1606)

theorem isAdmissible_evenPair_oneThousandSixHundredEight : IsAdmissible (evenPair 1608) :=
  isAdmissible_evenPair (by decide : Even 1608)

theorem isAdmissible_evenPair_oneThousandSixHundredTen : IsAdmissible (evenPair 1610) :=
  isAdmissible_evenPair (by decide : Even 1610)

theorem singular_series_pos_evenPair_oneThousandSixHundredTwo : 0 < singularSeries (evenPair 1602) :=
  singular_series_pos_evenPair (by decide : Even 1602)

theorem singular_series_pos_evenPair_oneThousandSixHundredFour : 0 < singularSeries (evenPair 1604) :=
  singular_series_pos_evenPair (by decide : Even 1604)

theorem singular_series_pos_evenPair_oneThousandSixHundredSix : 0 < singularSeries (evenPair 1606) :=
  singular_series_pos_evenPair (by decide : Even 1606)

theorem singular_series_pos_evenPair_oneThousandSixHundredEight : 0 < singularSeries (evenPair 1608) :=
  singular_series_pos_evenPair (by decide : Even 1608)

theorem singular_series_pos_evenPair_oneThousandSixHundredTen : 0 < singularSeries (evenPair 1610) :=
  singular_series_pos_evenPair (by decide : Even 1610)

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1602) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1602) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1604) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1604) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1606) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1606) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1608) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1608) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1610) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1610) P

theorem nu_p_oneThousandSixHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1602) p = if p = 2 ∨ p ∣ 1602 then 1 else 2 :=
  nu_p_evenPair (by decide : (1602 : ℕ) ≠ 0) (by decide : Even 1602) hp

theorem nu_p_oneThousandSixHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1604) p = if p = 2 ∨ p ∣ 1604 then 1 else 2 :=
  nu_p_evenPair (by decide : (1604 : ℕ) ≠ 0) (by decide : Even 1604) hp

theorem nu_p_oneThousandSixHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1606) p = if p = 2 ∨ p ∣ 1606 then 1 else 2 :=
  nu_p_evenPair (by decide : (1606 : ℕ) ≠ 0) (by decide : Even 1606) hp

theorem nu_p_oneThousandSixHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1608) p = if p = 2 ∨ p ∣ 1608 then 1 else 2 :=
  nu_p_evenPair (by decide : (1608 : ℕ) ≠ 0) (by decide : Even 1608) hp

theorem nu_p_oneThousandSixHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1610) p = if p = 2 ∨ p ∣ 1610 then 1 else 2 :=
  nu_p_evenPair (by decide : (1610 : ℕ) ≠ 0) (by decide : Even 1610) hp

theorem nu_p_oneThousandSixHundredTwo_two : nu_p (evenPair 1602) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1602)

theorem localFactor_oneThousandSixHundredTwo_two : localFactor (evenPair 1602) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1602 : ℕ) ≠ 0) (by decide : Even 1602)

theorem nu_p_oneThousandSixHundredTen_two : nu_p (evenPair 1610) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1610)

theorem localFactor_oneThousandSixHundredTen_two : localFactor (evenPair 1610) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1610 : ℕ) ≠ 0) (by decide : Even 1610)

end Brockian.SingularSeries.Gaps16021610
