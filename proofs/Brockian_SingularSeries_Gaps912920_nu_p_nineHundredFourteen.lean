/-
  Brockian/SingularSeriesGaps912920.lean — even binary gaps n ∈ {912, 914, 916, 918, 920}.

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

namespace Brockian.SingularSeries.Gaps912920

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_nineHundredTwelve : (evenPair 912).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (912 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredFourteen : (evenPair 914).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (914 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredSixteen : (evenPair 916).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (916 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredEighteen : (evenPair 918).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (918 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredTwenty : (evenPair 920).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (920 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_nineHundredTwelve : IsAdmissible (evenPair 912) :=
  isAdmissible_evenPair (by decide : Even 912)

theorem isAdmissible_evenPair_nineHundredFourteen : IsAdmissible (evenPair 914) :=
  isAdmissible_evenPair (by decide : Even 914)

theorem isAdmissible_evenPair_nineHundredSixteen : IsAdmissible (evenPair 916) :=
  isAdmissible_evenPair (by decide : Even 916)

theorem isAdmissible_evenPair_nineHundredEighteen : IsAdmissible (evenPair 918) :=
  isAdmissible_evenPair (by decide : Even 918)

theorem isAdmissible_evenPair_nineHundredTwenty : IsAdmissible (evenPair 920) :=
  isAdmissible_evenPair (by decide : Even 920)

theorem singular_series_pos_evenPair_nineHundredTwelve : 0 < singularSeries (evenPair 912) :=
  singular_series_pos_evenPair (by decide : Even 912)

theorem singular_series_pos_evenPair_nineHundredFourteen : 0 < singularSeries (evenPair 914) :=
  singular_series_pos_evenPair (by decide : Even 914)

theorem singular_series_pos_evenPair_nineHundredSixteen : 0 < singularSeries (evenPair 916) :=
  singular_series_pos_evenPair (by decide : Even 916)

theorem singular_series_pos_evenPair_nineHundredEighteen : 0 < singularSeries (evenPair 918) :=
  singular_series_pos_evenPair (by decide : Even 918)

theorem singular_series_pos_evenPair_nineHundredTwenty : 0 < singularSeries (evenPair 920) :=
  singular_series_pos_evenPair (by decide : Even 920)

theorem singular_series_finite_pos_evenPair_nineHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 912) P :=
  singular_series_finite_pos_evenPair (by decide : Even 912) P

theorem singular_series_finite_pos_evenPair_nineHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 914) P :=
  singular_series_finite_pos_evenPair (by decide : Even 914) P

theorem singular_series_finite_pos_evenPair_nineHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 916) P :=
  singular_series_finite_pos_evenPair (by decide : Even 916) P

theorem singular_series_finite_pos_evenPair_nineHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 918) P :=
  singular_series_finite_pos_evenPair (by decide : Even 918) P

theorem singular_series_finite_pos_evenPair_nineHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 920) P :=
  singular_series_finite_pos_evenPair (by decide : Even 920) P

theorem nu_p_nineHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 912) p = if p = 2 ∨ p ∣ 912 then 1 else 2 :=
  nu_p_evenPair (by decide : (912 : ℕ) ≠ 0) (by decide : Even 912) hp

theorem nu_p_nineHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 914) p = if p = 2 ∨ p ∣ 914 then 1 else 2 :=
  nu_p_evenPair (by decide : (914 : ℕ) ≠ 0) (by decide : Even 914) hp

theorem nu_p_nineHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 916) p = if p = 2 ∨ p ∣ 916 then 1 else 2 :=
  nu_p_evenPair (by decide : (916 : ℕ) ≠ 0) (by decide : Even 916) hp

theorem nu_p_nineHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 918) p = if p = 2 ∨ p ∣ 918 then 1 else 2 :=
  nu_p_evenPair (by decide : (918 : ℕ) ≠ 0) (by decide : Even 918) hp

theorem nu_p_nineHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 920) p = if p = 2 ∨ p ∣ 920 then 1 else 2 :=
  nu_p_evenPair (by decide : (920 : ℕ) ≠ 0) (by decide : Even 920) hp

theorem nu_p_nineHundredTwelve_two : nu_p (evenPair 912) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 912)

theorem localFactor_nineHundredTwelve_two : localFactor (evenPair 912) 2 = 2 :=
  localFactor_evenPair_two (by decide : (912 : ℕ) ≠ 0) (by decide : Even 912)

theorem nu_p_nineHundredTwenty_two : nu_p (evenPair 920) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 920)

theorem localFactor_nineHundredTwenty_two : localFactor (evenPair 920) 2 = 2 :=
  localFactor_evenPair_two (by decide : (920 : ℕ) ≠ 0) (by decide : Even 920)

end Brockian.SingularSeries.Gaps912920
