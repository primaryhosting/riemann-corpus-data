/-
  Brockian/SingularSeriesGaps342350.lean — even binary gaps n ∈ {342, 344, 346, 348, 350}.

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

namespace Brockian.SingularSeries.Gaps342350

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_threeHundredFortyTwo : (evenPair 342).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (342 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredFortyFour : (evenPair 344).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (344 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredFortySix : (evenPair 346).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (346 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredFortyEight : (evenPair 348).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (348 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredFifty : (evenPair 350).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (350 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_threeHundredFortyTwo : IsAdmissible (evenPair 342) :=
  isAdmissible_evenPair (by decide : Even 342)

theorem isAdmissible_evenPair_threeHundredFortyFour : IsAdmissible (evenPair 344) :=
  isAdmissible_evenPair (by decide : Even 344)

theorem isAdmissible_evenPair_threeHundredFortySix : IsAdmissible (evenPair 346) :=
  isAdmissible_evenPair (by decide : Even 346)

theorem isAdmissible_evenPair_threeHundredFortyEight : IsAdmissible (evenPair 348) :=
  isAdmissible_evenPair (by decide : Even 348)

theorem isAdmissible_evenPair_threeHundredFifty : IsAdmissible (evenPair 350) :=
  isAdmissible_evenPair (by decide : Even 350)

theorem singular_series_pos_evenPair_threeHundredFortyTwo : 0 < singularSeries (evenPair 342) :=
  singular_series_pos_evenPair (by decide : Even 342)

theorem singular_series_pos_evenPair_threeHundredFortyFour : 0 < singularSeries (evenPair 344) :=
  singular_series_pos_evenPair (by decide : Even 344)

theorem singular_series_pos_evenPair_threeHundredFortySix : 0 < singularSeries (evenPair 346) :=
  singular_series_pos_evenPair (by decide : Even 346)

theorem singular_series_pos_evenPair_threeHundredFortyEight : 0 < singularSeries (evenPair 348) :=
  singular_series_pos_evenPair (by decide : Even 348)

theorem singular_series_pos_evenPair_threeHundredFifty : 0 < singularSeries (evenPair 350) :=
  singular_series_pos_evenPair (by decide : Even 350)

theorem singular_series_finite_pos_evenPair_threeHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 342) P :=
  singular_series_finite_pos_evenPair (by decide : Even 342) P

theorem singular_series_finite_pos_evenPair_threeHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 344) P :=
  singular_series_finite_pos_evenPair (by decide : Even 344) P

theorem singular_series_finite_pos_evenPair_threeHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 346) P :=
  singular_series_finite_pos_evenPair (by decide : Even 346) P

theorem singular_series_finite_pos_evenPair_threeHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 348) P :=
  singular_series_finite_pos_evenPair (by decide : Even 348) P

theorem singular_series_finite_pos_evenPair_threeHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 350) P :=
  singular_series_finite_pos_evenPair (by decide : Even 350) P

theorem nu_p_threeHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 342) p = if p = 2 ∨ p ∣ 342 then 1 else 2 :=
  nu_p_evenPair (by decide : (342 : ℕ) ≠ 0) (by decide : Even 342) hp

theorem nu_p_threeHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 344) p = if p = 2 ∨ p ∣ 344 then 1 else 2 :=
  nu_p_evenPair (by decide : (344 : ℕ) ≠ 0) (by decide : Even 344) hp

theorem nu_p_threeHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 346) p = if p = 2 ∨ p ∣ 346 then 1 else 2 :=
  nu_p_evenPair (by decide : (346 : ℕ) ≠ 0) (by decide : Even 346) hp

theorem nu_p_threeHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 348) p = if p = 2 ∨ p ∣ 348 then 1 else 2 :=
  nu_p_evenPair (by decide : (348 : ℕ) ≠ 0) (by decide : Even 348) hp

theorem nu_p_threeHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 350) p = if p = 2 ∨ p ∣ 350 then 1 else 2 :=
  nu_p_evenPair (by decide : (350 : ℕ) ≠ 0) (by decide : Even 350) hp

theorem nu_p_threeHundredFortyTwo_two : nu_p (evenPair 342) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 342)

theorem localFactor_threeHundredFortyTwo_two : localFactor (evenPair 342) 2 = 2 :=
  localFactor_evenPair_two (by decide : (342 : ℕ) ≠ 0) (by decide : Even 342)

theorem nu_p_threeHundredFifty_two : nu_p (evenPair 350) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 350)

theorem localFactor_threeHundredFifty_two : localFactor (evenPair 350) 2 = 2 :=
  localFactor_evenPair_two (by decide : (350 : ℕ) ≠ 0) (by decide : Even 350)

end Brockian.SingularSeries.Gaps342350
