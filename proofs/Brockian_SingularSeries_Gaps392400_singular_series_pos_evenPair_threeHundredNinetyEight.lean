/-
  Brockian/SingularSeriesGaps392400.lean — even binary gaps n ∈ {392, 394, 396, 398, 400}.

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

namespace Brockian.SingularSeries.Gaps392400

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_threeHundredNinetyTwo : (evenPair 392).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (392 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredNinetyFour : (evenPair 394).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (394 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredNinetySix : (evenPair 396).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (396 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredNinetyEight : (evenPair 398).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (398 : ℕ) ≠ 0)

theorem evenPair_card_fourHundred : (evenPair 400).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (400 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_threeHundredNinetyTwo : IsAdmissible (evenPair 392) :=
  isAdmissible_evenPair (by decide : Even 392)

theorem isAdmissible_evenPair_threeHundredNinetyFour : IsAdmissible (evenPair 394) :=
  isAdmissible_evenPair (by decide : Even 394)

theorem isAdmissible_evenPair_threeHundredNinetySix : IsAdmissible (evenPair 396) :=
  isAdmissible_evenPair (by decide : Even 396)

theorem isAdmissible_evenPair_threeHundredNinetyEight : IsAdmissible (evenPair 398) :=
  isAdmissible_evenPair (by decide : Even 398)

theorem isAdmissible_evenPair_fourHundred : IsAdmissible (evenPair 400) :=
  isAdmissible_evenPair (by decide : Even 400)

theorem singular_series_pos_evenPair_threeHundredNinetyTwo : 0 < singularSeries (evenPair 392) :=
  singular_series_pos_evenPair (by decide : Even 392)

theorem singular_series_pos_evenPair_threeHundredNinetyFour : 0 < singularSeries (evenPair 394) :=
  singular_series_pos_evenPair (by decide : Even 394)

theorem singular_series_pos_evenPair_threeHundredNinetySix : 0 < singularSeries (evenPair 396) :=
  singular_series_pos_evenPair (by decide : Even 396)

theorem singular_series_pos_evenPair_threeHundredNinetyEight : 0 < singularSeries (evenPair 398) :=
  singular_series_pos_evenPair (by decide : Even 398)

theorem singular_series_pos_evenPair_fourHundred : 0 < singularSeries (evenPair 400) :=
  singular_series_pos_evenPair (by decide : Even 400)

theorem singular_series_finite_pos_evenPair_threeHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 392) P :=
  singular_series_finite_pos_evenPair (by decide : Even 392) P

theorem singular_series_finite_pos_evenPair_threeHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 394) P :=
  singular_series_finite_pos_evenPair (by decide : Even 394) P

theorem singular_series_finite_pos_evenPair_threeHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 396) P :=
  singular_series_finite_pos_evenPair (by decide : Even 396) P

theorem singular_series_finite_pos_evenPair_threeHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 398) P :=
  singular_series_finite_pos_evenPair (by decide : Even 398) P

theorem singular_series_finite_pos_evenPair_fourHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 400) P :=
  singular_series_finite_pos_evenPair (by decide : Even 400) P

theorem nu_p_threeHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 392) p = if p = 2 ∨ p ∣ 392 then 1 else 2 :=
  nu_p_evenPair (by decide : (392 : ℕ) ≠ 0) (by decide : Even 392) hp

theorem nu_p_threeHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 394) p = if p = 2 ∨ p ∣ 394 then 1 else 2 :=
  nu_p_evenPair (by decide : (394 : ℕ) ≠ 0) (by decide : Even 394) hp

theorem nu_p_threeHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 396) p = if p = 2 ∨ p ∣ 396 then 1 else 2 :=
  nu_p_evenPair (by decide : (396 : ℕ) ≠ 0) (by decide : Even 396) hp

theorem nu_p_threeHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 398) p = if p = 2 ∨ p ∣ 398 then 1 else 2 :=
  nu_p_evenPair (by decide : (398 : ℕ) ≠ 0) (by decide : Even 398) hp

theorem nu_p_fourHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 400) p = if p = 2 ∨ p ∣ 400 then 1 else 2 :=
  nu_p_evenPair (by decide : (400 : ℕ) ≠ 0) (by decide : Even 400) hp

theorem nu_p_threeHundredNinetyTwo_two : nu_p (evenPair 392) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 392)

theorem localFactor_threeHundredNinetyTwo_two : localFactor (evenPair 392) 2 = 2 :=
  localFactor_evenPair_two (by decide : (392 : ℕ) ≠ 0) (by decide : Even 392)

theorem nu_p_fourHundred_two : nu_p (evenPair 400) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 400)

theorem localFactor_fourHundred_two : localFactor (evenPair 400) 2 = 2 :=
  localFactor_evenPair_two (by decide : (400 : ℕ) ≠ 0) (by decide : Even 400)

end Brockian.SingularSeries.Gaps392400
