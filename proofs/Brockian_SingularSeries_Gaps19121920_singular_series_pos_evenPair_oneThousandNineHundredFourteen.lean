/-
  Brockian/SingularSeriesGaps19121920.lean — even binary gaps n ∈ {1912, 1914, 1916, 1918, 1920}.

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

namespace Brockian.SingularSeries.Gaps19121920

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNineHundredTwelve : (evenPair 1912).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1912 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredFourteen : (evenPair 1914).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1914 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredSixteen : (evenPair 1916).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1916 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredEighteen : (evenPair 1918).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1918 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredTwenty : (evenPair 1920).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1920 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNineHundredTwelve : IsAdmissible (evenPair 1912) :=
  isAdmissible_evenPair (by decide : Even 1912)

theorem isAdmissible_evenPair_oneThousandNineHundredFourteen : IsAdmissible (evenPair 1914) :=
  isAdmissible_evenPair (by decide : Even 1914)

theorem isAdmissible_evenPair_oneThousandNineHundredSixteen : IsAdmissible (evenPair 1916) :=
  isAdmissible_evenPair (by decide : Even 1916)

theorem isAdmissible_evenPair_oneThousandNineHundredEighteen : IsAdmissible (evenPair 1918) :=
  isAdmissible_evenPair (by decide : Even 1918)

theorem isAdmissible_evenPair_oneThousandNineHundredTwenty : IsAdmissible (evenPair 1920) :=
  isAdmissible_evenPair (by decide : Even 1920)

theorem singular_series_pos_evenPair_oneThousandNineHundredTwelve : 0 < singularSeries (evenPair 1912) :=
  singular_series_pos_evenPair (by decide : Even 1912)

theorem singular_series_pos_evenPair_oneThousandNineHundredFourteen : 0 < singularSeries (evenPair 1914) :=
  singular_series_pos_evenPair (by decide : Even 1914)

theorem singular_series_pos_evenPair_oneThousandNineHundredSixteen : 0 < singularSeries (evenPair 1916) :=
  singular_series_pos_evenPair (by decide : Even 1916)

theorem singular_series_pos_evenPair_oneThousandNineHundredEighteen : 0 < singularSeries (evenPair 1918) :=
  singular_series_pos_evenPair (by decide : Even 1918)

theorem singular_series_pos_evenPair_oneThousandNineHundredTwenty : 0 < singularSeries (evenPair 1920) :=
  singular_series_pos_evenPair (by decide : Even 1920)

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1912) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1912) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1914) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1914) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1916) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1916) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1918) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1918) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1920) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1920) P

theorem nu_p_oneThousandNineHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1912) p = if p = 2 ∨ p ∣ 1912 then 1 else 2 :=
  nu_p_evenPair (by decide : (1912 : ℕ) ≠ 0) (by decide : Even 1912) hp

theorem nu_p_oneThousandNineHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1914) p = if p = 2 ∨ p ∣ 1914 then 1 else 2 :=
  nu_p_evenPair (by decide : (1914 : ℕ) ≠ 0) (by decide : Even 1914) hp

theorem nu_p_oneThousandNineHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1916) p = if p = 2 ∨ p ∣ 1916 then 1 else 2 :=
  nu_p_evenPair (by decide : (1916 : ℕ) ≠ 0) (by decide : Even 1916) hp

theorem nu_p_oneThousandNineHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1918) p = if p = 2 ∨ p ∣ 1918 then 1 else 2 :=
  nu_p_evenPair (by decide : (1918 : ℕ) ≠ 0) (by decide : Even 1918) hp

theorem nu_p_oneThousandNineHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1920) p = if p = 2 ∨ p ∣ 1920 then 1 else 2 :=
  nu_p_evenPair (by decide : (1920 : ℕ) ≠ 0) (by decide : Even 1920) hp

theorem nu_p_oneThousandNineHundredTwelve_two : nu_p (evenPair 1912) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1912)

theorem localFactor_oneThousandNineHundredTwelve_two : localFactor (evenPair 1912) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1912 : ℕ) ≠ 0) (by decide : Even 1912)

theorem nu_p_oneThousandNineHundredTwenty_two : nu_p (evenPair 1920) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1920)

theorem localFactor_oneThousandNineHundredTwenty_two : localFactor (evenPair 1920) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1920 : ℕ) ≠ 0) (by decide : Even 1920)

end Brockian.SingularSeries.Gaps19121920
