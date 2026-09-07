/-
  Brockian/SingularSeriesGaps552560.lean — even binary gaps n ∈ {552, 554, 556, 558, 560}.

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

namespace Brockian.SingularSeries.Gaps552560

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiveHundredFiftyTwo : (evenPair 552).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (552 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredFiftyFour : (evenPair 554).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (554 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredFiftySix : (evenPair 556).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (556 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredFiftyEight : (evenPair 558).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (558 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredSixty : (evenPair 560).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (560 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiveHundredFiftyTwo : IsAdmissible (evenPair 552) :=
  isAdmissible_evenPair (by decide : Even 552)

theorem isAdmissible_evenPair_fiveHundredFiftyFour : IsAdmissible (evenPair 554) :=
  isAdmissible_evenPair (by decide : Even 554)

theorem isAdmissible_evenPair_fiveHundredFiftySix : IsAdmissible (evenPair 556) :=
  isAdmissible_evenPair (by decide : Even 556)

theorem isAdmissible_evenPair_fiveHundredFiftyEight : IsAdmissible (evenPair 558) :=
  isAdmissible_evenPair (by decide : Even 558)

theorem isAdmissible_evenPair_fiveHundredSixty : IsAdmissible (evenPair 560) :=
  isAdmissible_evenPair (by decide : Even 560)

theorem singular_series_pos_evenPair_fiveHundredFiftyTwo : 0 < singularSeries (evenPair 552) :=
  singular_series_pos_evenPair (by decide : Even 552)

theorem singular_series_pos_evenPair_fiveHundredFiftyFour : 0 < singularSeries (evenPair 554) :=
  singular_series_pos_evenPair (by decide : Even 554)

theorem singular_series_pos_evenPair_fiveHundredFiftySix : 0 < singularSeries (evenPair 556) :=
  singular_series_pos_evenPair (by decide : Even 556)

theorem singular_series_pos_evenPair_fiveHundredFiftyEight : 0 < singularSeries (evenPair 558) :=
  singular_series_pos_evenPair (by decide : Even 558)

theorem singular_series_pos_evenPair_fiveHundredSixty : 0 < singularSeries (evenPair 560) :=
  singular_series_pos_evenPair (by decide : Even 560)

theorem singular_series_finite_pos_evenPair_fiveHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 552) P :=
  singular_series_finite_pos_evenPair (by decide : Even 552) P

theorem singular_series_finite_pos_evenPair_fiveHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 554) P :=
  singular_series_finite_pos_evenPair (by decide : Even 554) P

theorem singular_series_finite_pos_evenPair_fiveHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 556) P :=
  singular_series_finite_pos_evenPair (by decide : Even 556) P

theorem singular_series_finite_pos_evenPair_fiveHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 558) P :=
  singular_series_finite_pos_evenPair (by decide : Even 558) P

theorem singular_series_finite_pos_evenPair_fiveHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 560) P :=
  singular_series_finite_pos_evenPair (by decide : Even 560) P

theorem nu_p_fiveHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 552) p = if p = 2 ∨ p ∣ 552 then 1 else 2 :=
  nu_p_evenPair (by decide : (552 : ℕ) ≠ 0) (by decide : Even 552) hp

theorem nu_p_fiveHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 554) p = if p = 2 ∨ p ∣ 554 then 1 else 2 :=
  nu_p_evenPair (by decide : (554 : ℕ) ≠ 0) (by decide : Even 554) hp

theorem nu_p_fiveHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 556) p = if p = 2 ∨ p ∣ 556 then 1 else 2 :=
  nu_p_evenPair (by decide : (556 : ℕ) ≠ 0) (by decide : Even 556) hp

theorem nu_p_fiveHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 558) p = if p = 2 ∨ p ∣ 558 then 1 else 2 :=
  nu_p_evenPair (by decide : (558 : ℕ) ≠ 0) (by decide : Even 558) hp

theorem nu_p_fiveHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 560) p = if p = 2 ∨ p ∣ 560 then 1 else 2 :=
  nu_p_evenPair (by decide : (560 : ℕ) ≠ 0) (by decide : Even 560) hp

theorem nu_p_fiveHundredFiftyTwo_two : nu_p (evenPair 552) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 552)

theorem localFactor_fiveHundredFiftyTwo_two : localFactor (evenPair 552) 2 = 2 :=
  localFactor_evenPair_two (by decide : (552 : ℕ) ≠ 0) (by decide : Even 552)

theorem nu_p_fiveHundredSixty_two : nu_p (evenPair 560) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 560)

theorem localFactor_fiveHundredSixty_two : localFactor (evenPair 560) 2 = 2 :=
  localFactor_evenPair_two (by decide : (560 : ℕ) ≠ 0) (by decide : Even 560)

end Brockian.SingularSeries.Gaps552560
