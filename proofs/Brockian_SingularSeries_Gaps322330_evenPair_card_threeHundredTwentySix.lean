/-
  Brockian/SingularSeriesGaps322330.lean — even binary gaps n ∈ {322, 324, 326, 328, 330}.

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

namespace Brockian.SingularSeries.Gaps322330

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_threeHundredTwentyTwo : (evenPair 322).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (322 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredTwentyFour : (evenPair 324).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (324 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredTwentySix : (evenPair 326).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (326 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredTwentyEight : (evenPair 328).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (328 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredThirty : (evenPair 330).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (330 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_threeHundredTwentyTwo : IsAdmissible (evenPair 322) :=
  isAdmissible_evenPair (by decide : Even 322)

theorem isAdmissible_evenPair_threeHundredTwentyFour : IsAdmissible (evenPair 324) :=
  isAdmissible_evenPair (by decide : Even 324)

theorem isAdmissible_evenPair_threeHundredTwentySix : IsAdmissible (evenPair 326) :=
  isAdmissible_evenPair (by decide : Even 326)

theorem isAdmissible_evenPair_threeHundredTwentyEight : IsAdmissible (evenPair 328) :=
  isAdmissible_evenPair (by decide : Even 328)

theorem isAdmissible_evenPair_threeHundredThirty : IsAdmissible (evenPair 330) :=
  isAdmissible_evenPair (by decide : Even 330)

theorem singular_series_pos_evenPair_threeHundredTwentyTwo : 0 < singularSeries (evenPair 322) :=
  singular_series_pos_evenPair (by decide : Even 322)

theorem singular_series_pos_evenPair_threeHundredTwentyFour : 0 < singularSeries (evenPair 324) :=
  singular_series_pos_evenPair (by decide : Even 324)

theorem singular_series_pos_evenPair_threeHundredTwentySix : 0 < singularSeries (evenPair 326) :=
  singular_series_pos_evenPair (by decide : Even 326)

theorem singular_series_pos_evenPair_threeHundredTwentyEight : 0 < singularSeries (evenPair 328) :=
  singular_series_pos_evenPair (by decide : Even 328)

theorem singular_series_pos_evenPair_threeHundredThirty : 0 < singularSeries (evenPair 330) :=
  singular_series_pos_evenPair (by decide : Even 330)

theorem singular_series_finite_pos_evenPair_threeHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 322) P :=
  singular_series_finite_pos_evenPair (by decide : Even 322) P

theorem singular_series_finite_pos_evenPair_threeHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 324) P :=
  singular_series_finite_pos_evenPair (by decide : Even 324) P

theorem singular_series_finite_pos_evenPair_threeHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 326) P :=
  singular_series_finite_pos_evenPair (by decide : Even 326) P

theorem singular_series_finite_pos_evenPair_threeHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 328) P :=
  singular_series_finite_pos_evenPair (by decide : Even 328) P

theorem singular_series_finite_pos_evenPair_threeHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 330) P :=
  singular_series_finite_pos_evenPair (by decide : Even 330) P

theorem nu_p_threeHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 322) p = if p = 2 ∨ p ∣ 322 then 1 else 2 :=
  nu_p_evenPair (by decide : (322 : ℕ) ≠ 0) (by decide : Even 322) hp

theorem nu_p_threeHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 324) p = if p = 2 ∨ p ∣ 324 then 1 else 2 :=
  nu_p_evenPair (by decide : (324 : ℕ) ≠ 0) (by decide : Even 324) hp

theorem nu_p_threeHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 326) p = if p = 2 ∨ p ∣ 326 then 1 else 2 :=
  nu_p_evenPair (by decide : (326 : ℕ) ≠ 0) (by decide : Even 326) hp

theorem nu_p_threeHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 328) p = if p = 2 ∨ p ∣ 328 then 1 else 2 :=
  nu_p_evenPair (by decide : (328 : ℕ) ≠ 0) (by decide : Even 328) hp

theorem nu_p_threeHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 330) p = if p = 2 ∨ p ∣ 330 then 1 else 2 :=
  nu_p_evenPair (by decide : (330 : ℕ) ≠ 0) (by decide : Even 330) hp

theorem nu_p_threeHundredTwentyTwo_two : nu_p (evenPair 322) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 322)

theorem localFactor_threeHundredTwentyTwo_two : localFactor (evenPair 322) 2 = 2 :=
  localFactor_evenPair_two (by decide : (322 : ℕ) ≠ 0) (by decide : Even 322)

theorem nu_p_threeHundredThirty_two : nu_p (evenPair 330) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 330)

theorem localFactor_threeHundredThirty_two : localFactor (evenPair 330) 2 = 2 :=
  localFactor_evenPair_two (by decide : (330 : ℕ) ≠ 0) (by decide : Even 330)

end Brockian.SingularSeries.Gaps322330
