/-
  Brockian/SingularSeriesGaps302310.lean — even binary gaps n ∈ {302, 304, 306, 308, 310}.

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

namespace Brockian.SingularSeries.Gaps302310

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_threeHundredTwo : (evenPair 302).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (302 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredFour : (evenPair 304).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (304 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredSix : (evenPair 306).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (306 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredEight : (evenPair 308).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (308 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredTen : (evenPair 310).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (310 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_threeHundredTwo : IsAdmissible (evenPair 302) :=
  isAdmissible_evenPair (by decide : Even 302)

theorem isAdmissible_evenPair_threeHundredFour : IsAdmissible (evenPair 304) :=
  isAdmissible_evenPair (by decide : Even 304)

theorem isAdmissible_evenPair_threeHundredSix : IsAdmissible (evenPair 306) :=
  isAdmissible_evenPair (by decide : Even 306)

theorem isAdmissible_evenPair_threeHundredEight : IsAdmissible (evenPair 308) :=
  isAdmissible_evenPair (by decide : Even 308)

theorem isAdmissible_evenPair_threeHundredTen : IsAdmissible (evenPair 310) :=
  isAdmissible_evenPair (by decide : Even 310)

theorem singular_series_pos_evenPair_threeHundredTwo : 0 < singularSeries (evenPair 302) :=
  singular_series_pos_evenPair (by decide : Even 302)

theorem singular_series_pos_evenPair_threeHundredFour : 0 < singularSeries (evenPair 304) :=
  singular_series_pos_evenPair (by decide : Even 304)

theorem singular_series_pos_evenPair_threeHundredSix : 0 < singularSeries (evenPair 306) :=
  singular_series_pos_evenPair (by decide : Even 306)

theorem singular_series_pos_evenPair_threeHundredEight : 0 < singularSeries (evenPair 308) :=
  singular_series_pos_evenPair (by decide : Even 308)

theorem singular_series_pos_evenPair_threeHundredTen : 0 < singularSeries (evenPair 310) :=
  singular_series_pos_evenPair (by decide : Even 310)

theorem singular_series_finite_pos_evenPair_threeHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 302) P :=
  singular_series_finite_pos_evenPair (by decide : Even 302) P

theorem singular_series_finite_pos_evenPair_threeHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 304) P :=
  singular_series_finite_pos_evenPair (by decide : Even 304) P

theorem singular_series_finite_pos_evenPair_threeHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 306) P :=
  singular_series_finite_pos_evenPair (by decide : Even 306) P

theorem singular_series_finite_pos_evenPair_threeHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 308) P :=
  singular_series_finite_pos_evenPair (by decide : Even 308) P

theorem singular_series_finite_pos_evenPair_threeHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 310) P :=
  singular_series_finite_pos_evenPair (by decide : Even 310) P

theorem nu_p_threeHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 302) p = if p = 2 ∨ p ∣ 302 then 1 else 2 :=
  nu_p_evenPair (by decide : (302 : ℕ) ≠ 0) (by decide : Even 302) hp

theorem nu_p_threeHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 304) p = if p = 2 ∨ p ∣ 304 then 1 else 2 :=
  nu_p_evenPair (by decide : (304 : ℕ) ≠ 0) (by decide : Even 304) hp

theorem nu_p_threeHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 306) p = if p = 2 ∨ p ∣ 306 then 1 else 2 :=
  nu_p_evenPair (by decide : (306 : ℕ) ≠ 0) (by decide : Even 306) hp

theorem nu_p_threeHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 308) p = if p = 2 ∨ p ∣ 308 then 1 else 2 :=
  nu_p_evenPair (by decide : (308 : ℕ) ≠ 0) (by decide : Even 308) hp

theorem nu_p_threeHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 310) p = if p = 2 ∨ p ∣ 310 then 1 else 2 :=
  nu_p_evenPair (by decide : (310 : ℕ) ≠ 0) (by decide : Even 310) hp

theorem nu_p_threeHundredTwo_two : nu_p (evenPair 302) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 302)

theorem localFactor_threeHundredTwo_two : localFactor (evenPair 302) 2 = 2 :=
  localFactor_evenPair_two (by decide : (302 : ℕ) ≠ 0) (by decide : Even 302)

theorem nu_p_threeHundredTen_two : nu_p (evenPair 310) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 310)

theorem localFactor_threeHundredTen_two : localFactor (evenPair 310) 2 = 2 :=
  localFactor_evenPair_two (by decide : (310 : ℕ) ≠ 0) (by decide : Even 310)

end Brockian.SingularSeries.Gaps302310
