/-
  Brockian/SingularSeriesGaps822830.lean — even binary gaps n ∈ {822, 824, 826, 828, 830}.

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

namespace Brockian.SingularSeries.Gaps822830

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightHundredTwentyTwo : (evenPair 822).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (822 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredTwentyFour : (evenPair 824).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (824 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredTwentySix : (evenPair 826).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (826 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredTwentyEight : (evenPair 828).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (828 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredThirty : (evenPair 830).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (830 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightHundredTwentyTwo : IsAdmissible (evenPair 822) :=
  isAdmissible_evenPair (by decide : Even 822)

theorem isAdmissible_evenPair_eightHundredTwentyFour : IsAdmissible (evenPair 824) :=
  isAdmissible_evenPair (by decide : Even 824)

theorem isAdmissible_evenPair_eightHundredTwentySix : IsAdmissible (evenPair 826) :=
  isAdmissible_evenPair (by decide : Even 826)

theorem isAdmissible_evenPair_eightHundredTwentyEight : IsAdmissible (evenPair 828) :=
  isAdmissible_evenPair (by decide : Even 828)

theorem isAdmissible_evenPair_eightHundredThirty : IsAdmissible (evenPair 830) :=
  isAdmissible_evenPair (by decide : Even 830)

theorem singular_series_pos_evenPair_eightHundredTwentyTwo : 0 < singularSeries (evenPair 822) :=
  singular_series_pos_evenPair (by decide : Even 822)

theorem singular_series_pos_evenPair_eightHundredTwentyFour : 0 < singularSeries (evenPair 824) :=
  singular_series_pos_evenPair (by decide : Even 824)

theorem singular_series_pos_evenPair_eightHundredTwentySix : 0 < singularSeries (evenPair 826) :=
  singular_series_pos_evenPair (by decide : Even 826)

theorem singular_series_pos_evenPair_eightHundredTwentyEight : 0 < singularSeries (evenPair 828) :=
  singular_series_pos_evenPair (by decide : Even 828)

theorem singular_series_pos_evenPair_eightHundredThirty : 0 < singularSeries (evenPair 830) :=
  singular_series_pos_evenPair (by decide : Even 830)

theorem singular_series_finite_pos_evenPair_eightHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 822) P :=
  singular_series_finite_pos_evenPair (by decide : Even 822) P

theorem singular_series_finite_pos_evenPair_eightHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 824) P :=
  singular_series_finite_pos_evenPair (by decide : Even 824) P

theorem singular_series_finite_pos_evenPair_eightHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 826) P :=
  singular_series_finite_pos_evenPair (by decide : Even 826) P

theorem singular_series_finite_pos_evenPair_eightHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 828) P :=
  singular_series_finite_pos_evenPair (by decide : Even 828) P

theorem singular_series_finite_pos_evenPair_eightHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 830) P :=
  singular_series_finite_pos_evenPair (by decide : Even 830) P

theorem nu_p_eightHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 822) p = if p = 2 ∨ p ∣ 822 then 1 else 2 :=
  nu_p_evenPair (by decide : (822 : ℕ) ≠ 0) (by decide : Even 822) hp

theorem nu_p_eightHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 824) p = if p = 2 ∨ p ∣ 824 then 1 else 2 :=
  nu_p_evenPair (by decide : (824 : ℕ) ≠ 0) (by decide : Even 824) hp

theorem nu_p_eightHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 826) p = if p = 2 ∨ p ∣ 826 then 1 else 2 :=
  nu_p_evenPair (by decide : (826 : ℕ) ≠ 0) (by decide : Even 826) hp

theorem nu_p_eightHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 828) p = if p = 2 ∨ p ∣ 828 then 1 else 2 :=
  nu_p_evenPair (by decide : (828 : ℕ) ≠ 0) (by decide : Even 828) hp

theorem nu_p_eightHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 830) p = if p = 2 ∨ p ∣ 830 then 1 else 2 :=
  nu_p_evenPair (by decide : (830 : ℕ) ≠ 0) (by decide : Even 830) hp

theorem nu_p_eightHundredTwentyTwo_two : nu_p (evenPair 822) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 822)

theorem localFactor_eightHundredTwentyTwo_two : localFactor (evenPair 822) 2 = 2 :=
  localFactor_evenPair_two (by decide : (822 : ℕ) ≠ 0) (by decide : Even 822)

theorem nu_p_eightHundredThirty_two : nu_p (evenPair 830) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 830)

theorem localFactor_eightHundredThirty_two : localFactor (evenPair 830) 2 = 2 :=
  localFactor_evenPair_two (by decide : (830 : ℕ) ≠ 0) (by decide : Even 830)

end Brockian.SingularSeries.Gaps822830
