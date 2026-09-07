/-
  Brockian/SingularSeriesGaps312320.lean — even binary gaps n ∈ {312, 314, 316, 318, 320}.

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

namespace Brockian.SingularSeries.Gaps312320

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_threeHundredTwelve : (evenPair 312).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (312 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredFourteen : (evenPair 314).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (314 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredSixteen : (evenPair 316).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (316 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredEighteen : (evenPair 318).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (318 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredTwenty : (evenPair 320).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (320 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_threeHundredTwelve : IsAdmissible (evenPair 312) :=
  isAdmissible_evenPair (by decide : Even 312)

theorem isAdmissible_evenPair_threeHundredFourteen : IsAdmissible (evenPair 314) :=
  isAdmissible_evenPair (by decide : Even 314)

theorem isAdmissible_evenPair_threeHundredSixteen : IsAdmissible (evenPair 316) :=
  isAdmissible_evenPair (by decide : Even 316)

theorem isAdmissible_evenPair_threeHundredEighteen : IsAdmissible (evenPair 318) :=
  isAdmissible_evenPair (by decide : Even 318)

theorem isAdmissible_evenPair_threeHundredTwenty : IsAdmissible (evenPair 320) :=
  isAdmissible_evenPair (by decide : Even 320)

theorem singular_series_pos_evenPair_threeHundredTwelve : 0 < singularSeries (evenPair 312) :=
  singular_series_pos_evenPair (by decide : Even 312)

theorem singular_series_pos_evenPair_threeHundredFourteen : 0 < singularSeries (evenPair 314) :=
  singular_series_pos_evenPair (by decide : Even 314)

theorem singular_series_pos_evenPair_threeHundredSixteen : 0 < singularSeries (evenPair 316) :=
  singular_series_pos_evenPair (by decide : Even 316)

theorem singular_series_pos_evenPair_threeHundredEighteen : 0 < singularSeries (evenPair 318) :=
  singular_series_pos_evenPair (by decide : Even 318)

theorem singular_series_pos_evenPair_threeHundredTwenty : 0 < singularSeries (evenPair 320) :=
  singular_series_pos_evenPair (by decide : Even 320)

theorem singular_series_finite_pos_evenPair_threeHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 312) P :=
  singular_series_finite_pos_evenPair (by decide : Even 312) P

theorem singular_series_finite_pos_evenPair_threeHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 314) P :=
  singular_series_finite_pos_evenPair (by decide : Even 314) P

theorem singular_series_finite_pos_evenPair_threeHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 316) P :=
  singular_series_finite_pos_evenPair (by decide : Even 316) P

theorem singular_series_finite_pos_evenPair_threeHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 318) P :=
  singular_series_finite_pos_evenPair (by decide : Even 318) P

theorem singular_series_finite_pos_evenPair_threeHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 320) P :=
  singular_series_finite_pos_evenPair (by decide : Even 320) P

theorem nu_p_threeHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 312) p = if p = 2 ∨ p ∣ 312 then 1 else 2 :=
  nu_p_evenPair (by decide : (312 : ℕ) ≠ 0) (by decide : Even 312) hp

theorem nu_p_threeHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 314) p = if p = 2 ∨ p ∣ 314 then 1 else 2 :=
  nu_p_evenPair (by decide : (314 : ℕ) ≠ 0) (by decide : Even 314) hp

theorem nu_p_threeHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 316) p = if p = 2 ∨ p ∣ 316 then 1 else 2 :=
  nu_p_evenPair (by decide : (316 : ℕ) ≠ 0) (by decide : Even 316) hp

theorem nu_p_threeHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 318) p = if p = 2 ∨ p ∣ 318 then 1 else 2 :=
  nu_p_evenPair (by decide : (318 : ℕ) ≠ 0) (by decide : Even 318) hp

theorem nu_p_threeHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 320) p = if p = 2 ∨ p ∣ 320 then 1 else 2 :=
  nu_p_evenPair (by decide : (320 : ℕ) ≠ 0) (by decide : Even 320) hp

theorem nu_p_threeHundredTwelve_two : nu_p (evenPair 312) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 312)

theorem localFactor_threeHundredTwelve_two : localFactor (evenPair 312) 2 = 2 :=
  localFactor_evenPair_two (by decide : (312 : ℕ) ≠ 0) (by decide : Even 312)

theorem nu_p_threeHundredTwenty_two : nu_p (evenPair 320) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 320)

theorem localFactor_threeHundredTwenty_two : localFactor (evenPair 320) 2 = 2 :=
  localFactor_evenPair_two (by decide : (320 : ℕ) ≠ 0) (by decide : Even 320)

end Brockian.SingularSeries.Gaps312320
