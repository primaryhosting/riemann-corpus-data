/-
  Brockian/SingularSeriesGaps19021910.lean — even binary gaps n ∈ {1902, 1904, 1906, 1908, 1910}.

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

namespace Brockian.SingularSeries.Gaps19021910

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNineHundredTwo : (evenPair 1902).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1902 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredFour : (evenPair 1904).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1904 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredSix : (evenPair 1906).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1906 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredEight : (evenPair 1908).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1908 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredTen : (evenPair 1910).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1910 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNineHundredTwo : IsAdmissible (evenPair 1902) :=
  isAdmissible_evenPair (by decide : Even 1902)

theorem isAdmissible_evenPair_oneThousandNineHundredFour : IsAdmissible (evenPair 1904) :=
  isAdmissible_evenPair (by decide : Even 1904)

theorem isAdmissible_evenPair_oneThousandNineHundredSix : IsAdmissible (evenPair 1906) :=
  isAdmissible_evenPair (by decide : Even 1906)

theorem isAdmissible_evenPair_oneThousandNineHundredEight : IsAdmissible (evenPair 1908) :=
  isAdmissible_evenPair (by decide : Even 1908)

theorem isAdmissible_evenPair_oneThousandNineHundredTen : IsAdmissible (evenPair 1910) :=
  isAdmissible_evenPair (by decide : Even 1910)

theorem singular_series_pos_evenPair_oneThousandNineHundredTwo : 0 < singularSeries (evenPair 1902) :=
  singular_series_pos_evenPair (by decide : Even 1902)

theorem singular_series_pos_evenPair_oneThousandNineHundredFour : 0 < singularSeries (evenPair 1904) :=
  singular_series_pos_evenPair (by decide : Even 1904)

theorem singular_series_pos_evenPair_oneThousandNineHundredSix : 0 < singularSeries (evenPair 1906) :=
  singular_series_pos_evenPair (by decide : Even 1906)

theorem singular_series_pos_evenPair_oneThousandNineHundredEight : 0 < singularSeries (evenPair 1908) :=
  singular_series_pos_evenPair (by decide : Even 1908)

theorem singular_series_pos_evenPair_oneThousandNineHundredTen : 0 < singularSeries (evenPair 1910) :=
  singular_series_pos_evenPair (by decide : Even 1910)

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1902) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1902) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1904) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1904) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1906) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1906) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1908) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1908) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1910) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1910) P

theorem nu_p_oneThousandNineHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1902) p = if p = 2 ∨ p ∣ 1902 then 1 else 2 :=
  nu_p_evenPair (by decide : (1902 : ℕ) ≠ 0) (by decide : Even 1902) hp

theorem nu_p_oneThousandNineHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1904) p = if p = 2 ∨ p ∣ 1904 then 1 else 2 :=
  nu_p_evenPair (by decide : (1904 : ℕ) ≠ 0) (by decide : Even 1904) hp

theorem nu_p_oneThousandNineHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1906) p = if p = 2 ∨ p ∣ 1906 then 1 else 2 :=
  nu_p_evenPair (by decide : (1906 : ℕ) ≠ 0) (by decide : Even 1906) hp

theorem nu_p_oneThousandNineHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1908) p = if p = 2 ∨ p ∣ 1908 then 1 else 2 :=
  nu_p_evenPair (by decide : (1908 : ℕ) ≠ 0) (by decide : Even 1908) hp

theorem nu_p_oneThousandNineHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1910) p = if p = 2 ∨ p ∣ 1910 then 1 else 2 :=
  nu_p_evenPair (by decide : (1910 : ℕ) ≠ 0) (by decide : Even 1910) hp

theorem nu_p_oneThousandNineHundredTwo_two : nu_p (evenPair 1902) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1902)

theorem localFactor_oneThousandNineHundredTwo_two : localFactor (evenPair 1902) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1902 : ℕ) ≠ 0) (by decide : Even 1902)

theorem nu_p_oneThousandNineHundredTen_two : nu_p (evenPair 1910) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1910)

theorem localFactor_oneThousandNineHundredTen_two : localFactor (evenPair 1910) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1910 : ℕ) ≠ 0) (by decide : Even 1910)

end Brockian.SingularSeries.Gaps19021910
