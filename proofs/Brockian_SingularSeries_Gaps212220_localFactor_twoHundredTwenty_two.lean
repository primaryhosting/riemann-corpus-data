/-
  Brockian/SingularSeriesGaps212220.lean — even binary gaps n ∈ {212, 214, 216, 218, 220}.

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

namespace Brockian.SingularSeries.Gaps212220

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoHundredTwelve : (evenPair 212).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (212 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredFourteen : (evenPair 214).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (214 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredSixteen : (evenPair 216).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (216 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredEighteen : (evenPair 218).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (218 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredTwenty : (evenPair 220).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (220 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoHundredTwelve : IsAdmissible (evenPair 212) :=
  isAdmissible_evenPair (by decide : Even 212)

theorem isAdmissible_evenPair_twoHundredFourteen : IsAdmissible (evenPair 214) :=
  isAdmissible_evenPair (by decide : Even 214)

theorem isAdmissible_evenPair_twoHundredSixteen : IsAdmissible (evenPair 216) :=
  isAdmissible_evenPair (by decide : Even 216)

theorem isAdmissible_evenPair_twoHundredEighteen : IsAdmissible (evenPair 218) :=
  isAdmissible_evenPair (by decide : Even 218)

theorem isAdmissible_evenPair_twoHundredTwenty : IsAdmissible (evenPair 220) :=
  isAdmissible_evenPair (by decide : Even 220)

theorem singular_series_pos_evenPair_twoHundredTwelve : 0 < singularSeries (evenPair 212) :=
  singular_series_pos_evenPair (by decide : Even 212)

theorem singular_series_pos_evenPair_twoHundredFourteen : 0 < singularSeries (evenPair 214) :=
  singular_series_pos_evenPair (by decide : Even 214)

theorem singular_series_pos_evenPair_twoHundredSixteen : 0 < singularSeries (evenPair 216) :=
  singular_series_pos_evenPair (by decide : Even 216)

theorem singular_series_pos_evenPair_twoHundredEighteen : 0 < singularSeries (evenPair 218) :=
  singular_series_pos_evenPair (by decide : Even 218)

theorem singular_series_pos_evenPair_twoHundredTwenty : 0 < singularSeries (evenPair 220) :=
  singular_series_pos_evenPair (by decide : Even 220)

theorem singular_series_finite_pos_evenPair_twoHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 212) P :=
  singular_series_finite_pos_evenPair (by decide : Even 212) P

theorem singular_series_finite_pos_evenPair_twoHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 214) P :=
  singular_series_finite_pos_evenPair (by decide : Even 214) P

theorem singular_series_finite_pos_evenPair_twoHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 216) P :=
  singular_series_finite_pos_evenPair (by decide : Even 216) P

theorem singular_series_finite_pos_evenPair_twoHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 218) P :=
  singular_series_finite_pos_evenPair (by decide : Even 218) P

theorem singular_series_finite_pos_evenPair_twoHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 220) P :=
  singular_series_finite_pos_evenPair (by decide : Even 220) P

theorem nu_p_twoHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 212) p = if p = 2 ∨ p ∣ 212 then 1 else 2 :=
  nu_p_evenPair (by decide : (212 : ℕ) ≠ 0) (by decide : Even 212) hp

theorem nu_p_twoHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 214) p = if p = 2 ∨ p ∣ 214 then 1 else 2 :=
  nu_p_evenPair (by decide : (214 : ℕ) ≠ 0) (by decide : Even 214) hp

theorem nu_p_twoHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 216) p = if p = 2 ∨ p ∣ 216 then 1 else 2 :=
  nu_p_evenPair (by decide : (216 : ℕ) ≠ 0) (by decide : Even 216) hp

theorem nu_p_twoHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 218) p = if p = 2 ∨ p ∣ 218 then 1 else 2 :=
  nu_p_evenPair (by decide : (218 : ℕ) ≠ 0) (by decide : Even 218) hp

theorem nu_p_twoHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 220) p = if p = 2 ∨ p ∣ 220 then 1 else 2 :=
  nu_p_evenPair (by decide : (220 : ℕ) ≠ 0) (by decide : Even 220) hp

theorem nu_p_twoHundredTwelve_two : nu_p (evenPair 212) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 212)

theorem localFactor_twoHundredTwelve_two : localFactor (evenPair 212) 2 = 2 :=
  localFactor_evenPair_two (by decide : (212 : ℕ) ≠ 0) (by decide : Even 212)

theorem nu_p_twoHundredTwenty_two : nu_p (evenPair 220) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 220)

theorem localFactor_twoHundredTwenty_two : localFactor (evenPair 220) 2 = 2 :=
  localFactor_evenPair_two (by decide : (220 : ℕ) ≠ 0) (by decide : Even 220)

end Brockian.SingularSeries.Gaps212220
