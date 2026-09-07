/-
  Brockian/SingularSeriesGaps452460.lean — even binary gaps n ∈ {452, 454, 456, 458, 460}.

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

namespace Brockian.SingularSeries.Gaps452460

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fourHundredFiftyTwo : (evenPair 452).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (452 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredFiftyFour : (evenPair 454).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (454 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredFiftySix : (evenPair 456).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (456 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredFiftyEight : (evenPair 458).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (458 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredSixty : (evenPair 460).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (460 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fourHundredFiftyTwo : IsAdmissible (evenPair 452) :=
  isAdmissible_evenPair (by decide : Even 452)

theorem isAdmissible_evenPair_fourHundredFiftyFour : IsAdmissible (evenPair 454) :=
  isAdmissible_evenPair (by decide : Even 454)

theorem isAdmissible_evenPair_fourHundredFiftySix : IsAdmissible (evenPair 456) :=
  isAdmissible_evenPair (by decide : Even 456)

theorem isAdmissible_evenPair_fourHundredFiftyEight : IsAdmissible (evenPair 458) :=
  isAdmissible_evenPair (by decide : Even 458)

theorem isAdmissible_evenPair_fourHundredSixty : IsAdmissible (evenPair 460) :=
  isAdmissible_evenPair (by decide : Even 460)

theorem singular_series_pos_evenPair_fourHundredFiftyTwo : 0 < singularSeries (evenPair 452) :=
  singular_series_pos_evenPair (by decide : Even 452)

theorem singular_series_pos_evenPair_fourHundredFiftyFour : 0 < singularSeries (evenPair 454) :=
  singular_series_pos_evenPair (by decide : Even 454)

theorem singular_series_pos_evenPair_fourHundredFiftySix : 0 < singularSeries (evenPair 456) :=
  singular_series_pos_evenPair (by decide : Even 456)

theorem singular_series_pos_evenPair_fourHundredFiftyEight : 0 < singularSeries (evenPair 458) :=
  singular_series_pos_evenPair (by decide : Even 458)

theorem singular_series_pos_evenPair_fourHundredSixty : 0 < singularSeries (evenPair 460) :=
  singular_series_pos_evenPair (by decide : Even 460)

theorem singular_series_finite_pos_evenPair_fourHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 452) P :=
  singular_series_finite_pos_evenPair (by decide : Even 452) P

theorem singular_series_finite_pos_evenPair_fourHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 454) P :=
  singular_series_finite_pos_evenPair (by decide : Even 454) P

theorem singular_series_finite_pos_evenPair_fourHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 456) P :=
  singular_series_finite_pos_evenPair (by decide : Even 456) P

theorem singular_series_finite_pos_evenPair_fourHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 458) P :=
  singular_series_finite_pos_evenPair (by decide : Even 458) P

theorem singular_series_finite_pos_evenPair_fourHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 460) P :=
  singular_series_finite_pos_evenPair (by decide : Even 460) P

theorem nu_p_fourHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 452) p = if p = 2 ∨ p ∣ 452 then 1 else 2 :=
  nu_p_evenPair (by decide : (452 : ℕ) ≠ 0) (by decide : Even 452) hp

theorem nu_p_fourHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 454) p = if p = 2 ∨ p ∣ 454 then 1 else 2 :=
  nu_p_evenPair (by decide : (454 : ℕ) ≠ 0) (by decide : Even 454) hp

theorem nu_p_fourHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 456) p = if p = 2 ∨ p ∣ 456 then 1 else 2 :=
  nu_p_evenPair (by decide : (456 : ℕ) ≠ 0) (by decide : Even 456) hp

theorem nu_p_fourHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 458) p = if p = 2 ∨ p ∣ 458 then 1 else 2 :=
  nu_p_evenPair (by decide : (458 : ℕ) ≠ 0) (by decide : Even 458) hp

theorem nu_p_fourHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 460) p = if p = 2 ∨ p ∣ 460 then 1 else 2 :=
  nu_p_evenPair (by decide : (460 : ℕ) ≠ 0) (by decide : Even 460) hp

theorem nu_p_fourHundredFiftyTwo_two : nu_p (evenPair 452) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 452)

theorem localFactor_fourHundredFiftyTwo_two : localFactor (evenPair 452) 2 = 2 :=
  localFactor_evenPair_two (by decide : (452 : ℕ) ≠ 0) (by decide : Even 452)

theorem nu_p_fourHundredSixty_two : nu_p (evenPair 460) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 460)

theorem localFactor_fourHundredSixty_two : localFactor (evenPair 460) 2 = 2 :=
  localFactor_evenPair_two (by decide : (460 : ℕ) ≠ 0) (by decide : Even 460)

end Brockian.SingularSeries.Gaps452460
