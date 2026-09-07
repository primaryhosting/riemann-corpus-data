/-
  Brockian/SingularSeriesGaps16521660.lean — even binary gaps n ∈ {1652, 1654, 1656, 1658, 1660}.

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

namespace Brockian.SingularSeries.Gaps16521660

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixHundredFiftyTwo : (evenPair 1652).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1652 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredFiftyFour : (evenPair 1654).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1654 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredFiftySix : (evenPair 1656).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1656 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredFiftyEight : (evenPair 1658).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1658 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredSixty : (evenPair 1660).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1660 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixHundredFiftyTwo : IsAdmissible (evenPair 1652) :=
  isAdmissible_evenPair (by decide : Even 1652)

theorem isAdmissible_evenPair_oneThousandSixHundredFiftyFour : IsAdmissible (evenPair 1654) :=
  isAdmissible_evenPair (by decide : Even 1654)

theorem isAdmissible_evenPair_oneThousandSixHundredFiftySix : IsAdmissible (evenPair 1656) :=
  isAdmissible_evenPair (by decide : Even 1656)

theorem isAdmissible_evenPair_oneThousandSixHundredFiftyEight : IsAdmissible (evenPair 1658) :=
  isAdmissible_evenPair (by decide : Even 1658)

theorem isAdmissible_evenPair_oneThousandSixHundredSixty : IsAdmissible (evenPair 1660) :=
  isAdmissible_evenPair (by decide : Even 1660)

theorem singular_series_pos_evenPair_oneThousandSixHundredFiftyTwo : 0 < singularSeries (evenPair 1652) :=
  singular_series_pos_evenPair (by decide : Even 1652)

theorem singular_series_pos_evenPair_oneThousandSixHundredFiftyFour : 0 < singularSeries (evenPair 1654) :=
  singular_series_pos_evenPair (by decide : Even 1654)

theorem singular_series_pos_evenPair_oneThousandSixHundredFiftySix : 0 < singularSeries (evenPair 1656) :=
  singular_series_pos_evenPair (by decide : Even 1656)

theorem singular_series_pos_evenPair_oneThousandSixHundredFiftyEight : 0 < singularSeries (evenPair 1658) :=
  singular_series_pos_evenPair (by decide : Even 1658)

theorem singular_series_pos_evenPair_oneThousandSixHundredSixty : 0 < singularSeries (evenPair 1660) :=
  singular_series_pos_evenPair (by decide : Even 1660)

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1652) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1652) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1654) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1654) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1656) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1656) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1658) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1658) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1660) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1660) P

theorem nu_p_oneThousandSixHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1652) p = if p = 2 ∨ p ∣ 1652 then 1 else 2 :=
  nu_p_evenPair (by decide : (1652 : ℕ) ≠ 0) (by decide : Even 1652) hp

theorem nu_p_oneThousandSixHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1654) p = if p = 2 ∨ p ∣ 1654 then 1 else 2 :=
  nu_p_evenPair (by decide : (1654 : ℕ) ≠ 0) (by decide : Even 1654) hp

theorem nu_p_oneThousandSixHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1656) p = if p = 2 ∨ p ∣ 1656 then 1 else 2 :=
  nu_p_evenPair (by decide : (1656 : ℕ) ≠ 0) (by decide : Even 1656) hp

theorem nu_p_oneThousandSixHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1658) p = if p = 2 ∨ p ∣ 1658 then 1 else 2 :=
  nu_p_evenPair (by decide : (1658 : ℕ) ≠ 0) (by decide : Even 1658) hp

theorem nu_p_oneThousandSixHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1660) p = if p = 2 ∨ p ∣ 1660 then 1 else 2 :=
  nu_p_evenPair (by decide : (1660 : ℕ) ≠ 0) (by decide : Even 1660) hp

theorem nu_p_oneThousandSixHundredFiftyTwo_two : nu_p (evenPair 1652) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1652)

theorem localFactor_oneThousandSixHundredFiftyTwo_two : localFactor (evenPair 1652) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1652 : ℕ) ≠ 0) (by decide : Even 1652)

theorem nu_p_oneThousandSixHundredSixty_two : nu_p (evenPair 1660) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1660)

theorem localFactor_oneThousandSixHundredSixty_two : localFactor (evenPair 1660) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1660 : ℕ) ≠ 0) (by decide : Even 1660)

end Brockian.SingularSeries.Gaps16521660
