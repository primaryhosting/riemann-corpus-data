/-
  Brockian/SingularSeriesGaps18121820.lean — even binary gaps n ∈ {1812, 1814, 1816, 1818, 1820}.

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

namespace Brockian.SingularSeries.Gaps18121820

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightHundredTwelve : (evenPair 1812).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1812 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredFourteen : (evenPair 1814).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1814 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredSixteen : (evenPair 1816).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1816 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredEighteen : (evenPair 1818).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1818 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredTwenty : (evenPair 1820).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1820 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightHundredTwelve : IsAdmissible (evenPair 1812) :=
  isAdmissible_evenPair (by decide : Even 1812)

theorem isAdmissible_evenPair_oneThousandEightHundredFourteen : IsAdmissible (evenPair 1814) :=
  isAdmissible_evenPair (by decide : Even 1814)

theorem isAdmissible_evenPair_oneThousandEightHundredSixteen : IsAdmissible (evenPair 1816) :=
  isAdmissible_evenPair (by decide : Even 1816)

theorem isAdmissible_evenPair_oneThousandEightHundredEighteen : IsAdmissible (evenPair 1818) :=
  isAdmissible_evenPair (by decide : Even 1818)

theorem isAdmissible_evenPair_oneThousandEightHundredTwenty : IsAdmissible (evenPair 1820) :=
  isAdmissible_evenPair (by decide : Even 1820)

theorem singular_series_pos_evenPair_oneThousandEightHundredTwelve : 0 < singularSeries (evenPair 1812) :=
  singular_series_pos_evenPair (by decide : Even 1812)

theorem singular_series_pos_evenPair_oneThousandEightHundredFourteen : 0 < singularSeries (evenPair 1814) :=
  singular_series_pos_evenPair (by decide : Even 1814)

theorem singular_series_pos_evenPair_oneThousandEightHundredSixteen : 0 < singularSeries (evenPair 1816) :=
  singular_series_pos_evenPair (by decide : Even 1816)

theorem singular_series_pos_evenPair_oneThousandEightHundredEighteen : 0 < singularSeries (evenPair 1818) :=
  singular_series_pos_evenPair (by decide : Even 1818)

theorem singular_series_pos_evenPair_oneThousandEightHundredTwenty : 0 < singularSeries (evenPair 1820) :=
  singular_series_pos_evenPair (by decide : Even 1820)

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1812) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1812) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1814) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1814) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1816) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1816) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1818) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1818) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1820) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1820) P

theorem nu_p_oneThousandEightHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1812) p = if p = 2 ∨ p ∣ 1812 then 1 else 2 :=
  nu_p_evenPair (by decide : (1812 : ℕ) ≠ 0) (by decide : Even 1812) hp

theorem nu_p_oneThousandEightHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1814) p = if p = 2 ∨ p ∣ 1814 then 1 else 2 :=
  nu_p_evenPair (by decide : (1814 : ℕ) ≠ 0) (by decide : Even 1814) hp

theorem nu_p_oneThousandEightHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1816) p = if p = 2 ∨ p ∣ 1816 then 1 else 2 :=
  nu_p_evenPair (by decide : (1816 : ℕ) ≠ 0) (by decide : Even 1816) hp

theorem nu_p_oneThousandEightHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1818) p = if p = 2 ∨ p ∣ 1818 then 1 else 2 :=
  nu_p_evenPair (by decide : (1818 : ℕ) ≠ 0) (by decide : Even 1818) hp

theorem nu_p_oneThousandEightHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1820) p = if p = 2 ∨ p ∣ 1820 then 1 else 2 :=
  nu_p_evenPair (by decide : (1820 : ℕ) ≠ 0) (by decide : Even 1820) hp

theorem nu_p_oneThousandEightHundredTwelve_two : nu_p (evenPair 1812) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1812)

theorem localFactor_oneThousandEightHundredTwelve_two : localFactor (evenPair 1812) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1812 : ℕ) ≠ 0) (by decide : Even 1812)

theorem nu_p_oneThousandEightHundredTwenty_two : nu_p (evenPair 1820) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1820)

theorem localFactor_oneThousandEightHundredTwenty_two : localFactor (evenPair 1820) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1820 : ℕ) ≠ 0) (by decide : Even 1820)

end Brockian.SingularSeries.Gaps18121820
