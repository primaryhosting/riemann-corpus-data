/-
  Brockian/SingularSeriesGaps17121720.lean — even binary gaps n ∈ {1712, 1714, 1716, 1718, 1720}.

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

namespace Brockian.SingularSeries.Gaps17121720

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSevenHundredTwelve : (evenPair 1712).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1712 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredFourteen : (evenPair 1714).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1714 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredSixteen : (evenPair 1716).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1716 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredEighteen : (evenPair 1718).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1718 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredTwenty : (evenPair 1720).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1720 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSevenHundredTwelve : IsAdmissible (evenPair 1712) :=
  isAdmissible_evenPair (by decide : Even 1712)

theorem isAdmissible_evenPair_oneThousandSevenHundredFourteen : IsAdmissible (evenPair 1714) :=
  isAdmissible_evenPair (by decide : Even 1714)

theorem isAdmissible_evenPair_oneThousandSevenHundredSixteen : IsAdmissible (evenPair 1716) :=
  isAdmissible_evenPair (by decide : Even 1716)

theorem isAdmissible_evenPair_oneThousandSevenHundredEighteen : IsAdmissible (evenPair 1718) :=
  isAdmissible_evenPair (by decide : Even 1718)

theorem isAdmissible_evenPair_oneThousandSevenHundredTwenty : IsAdmissible (evenPair 1720) :=
  isAdmissible_evenPair (by decide : Even 1720)

theorem singular_series_pos_evenPair_oneThousandSevenHundredTwelve : 0 < singularSeries (evenPair 1712) :=
  singular_series_pos_evenPair (by decide : Even 1712)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFourteen : 0 < singularSeries (evenPair 1714) :=
  singular_series_pos_evenPair (by decide : Even 1714)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSixteen : 0 < singularSeries (evenPair 1716) :=
  singular_series_pos_evenPair (by decide : Even 1716)

theorem singular_series_pos_evenPair_oneThousandSevenHundredEighteen : 0 < singularSeries (evenPair 1718) :=
  singular_series_pos_evenPair (by decide : Even 1718)

theorem singular_series_pos_evenPair_oneThousandSevenHundredTwenty : 0 < singularSeries (evenPair 1720) :=
  singular_series_pos_evenPair (by decide : Even 1720)

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1712) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1712) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1714) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1714) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1716) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1716) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1718) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1718) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1720) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1720) P

theorem nu_p_oneThousandSevenHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1712) p = if p = 2 ∨ p ∣ 1712 then 1 else 2 :=
  nu_p_evenPair (by decide : (1712 : ℕ) ≠ 0) (by decide : Even 1712) hp

theorem nu_p_oneThousandSevenHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1714) p = if p = 2 ∨ p ∣ 1714 then 1 else 2 :=
  nu_p_evenPair (by decide : (1714 : ℕ) ≠ 0) (by decide : Even 1714) hp

theorem nu_p_oneThousandSevenHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1716) p = if p = 2 ∨ p ∣ 1716 then 1 else 2 :=
  nu_p_evenPair (by decide : (1716 : ℕ) ≠ 0) (by decide : Even 1716) hp

theorem nu_p_oneThousandSevenHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1718) p = if p = 2 ∨ p ∣ 1718 then 1 else 2 :=
  nu_p_evenPair (by decide : (1718 : ℕ) ≠ 0) (by decide : Even 1718) hp

theorem nu_p_oneThousandSevenHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1720) p = if p = 2 ∨ p ∣ 1720 then 1 else 2 :=
  nu_p_evenPair (by decide : (1720 : ℕ) ≠ 0) (by decide : Even 1720) hp

theorem nu_p_oneThousandSevenHundredTwelve_two : nu_p (evenPair 1712) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1712)

theorem localFactor_oneThousandSevenHundredTwelve_two : localFactor (evenPair 1712) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1712 : ℕ) ≠ 0) (by decide : Even 1712)

theorem nu_p_oneThousandSevenHundredTwenty_two : nu_p (evenPair 1720) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1720)

theorem localFactor_oneThousandSevenHundredTwenty_two : localFactor (evenPair 1720) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1720 : ℕ) ≠ 0) (by decide : Even 1720)

end Brockian.SingularSeries.Gaps17121720
