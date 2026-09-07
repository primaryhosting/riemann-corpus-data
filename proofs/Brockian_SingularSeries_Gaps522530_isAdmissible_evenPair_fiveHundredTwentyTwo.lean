/-
  Brockian/SingularSeriesGaps522530.lean — even binary gaps n ∈ {522, 524, 526, 528, 530}.

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

namespace Brockian.SingularSeries.Gaps522530

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiveHundredTwentyTwo : (evenPair 522).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (522 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredTwentyFour : (evenPair 524).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (524 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredTwentySix : (evenPair 526).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (526 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredTwentyEight : (evenPair 528).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (528 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredThirty : (evenPair 530).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (530 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiveHundredTwentyTwo : IsAdmissible (evenPair 522) :=
  isAdmissible_evenPair (by decide : Even 522)

theorem isAdmissible_evenPair_fiveHundredTwentyFour : IsAdmissible (evenPair 524) :=
  isAdmissible_evenPair (by decide : Even 524)

theorem isAdmissible_evenPair_fiveHundredTwentySix : IsAdmissible (evenPair 526) :=
  isAdmissible_evenPair (by decide : Even 526)

theorem isAdmissible_evenPair_fiveHundredTwentyEight : IsAdmissible (evenPair 528) :=
  isAdmissible_evenPair (by decide : Even 528)

theorem isAdmissible_evenPair_fiveHundredThirty : IsAdmissible (evenPair 530) :=
  isAdmissible_evenPair (by decide : Even 530)

theorem singular_series_pos_evenPair_fiveHundredTwentyTwo : 0 < singularSeries (evenPair 522) :=
  singular_series_pos_evenPair (by decide : Even 522)

theorem singular_series_pos_evenPair_fiveHundredTwentyFour : 0 < singularSeries (evenPair 524) :=
  singular_series_pos_evenPair (by decide : Even 524)

theorem singular_series_pos_evenPair_fiveHundredTwentySix : 0 < singularSeries (evenPair 526) :=
  singular_series_pos_evenPair (by decide : Even 526)

theorem singular_series_pos_evenPair_fiveHundredTwentyEight : 0 < singularSeries (evenPair 528) :=
  singular_series_pos_evenPair (by decide : Even 528)

theorem singular_series_pos_evenPair_fiveHundredThirty : 0 < singularSeries (evenPair 530) :=
  singular_series_pos_evenPair (by decide : Even 530)

theorem singular_series_finite_pos_evenPair_fiveHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 522) P :=
  singular_series_finite_pos_evenPair (by decide : Even 522) P

theorem singular_series_finite_pos_evenPair_fiveHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 524) P :=
  singular_series_finite_pos_evenPair (by decide : Even 524) P

theorem singular_series_finite_pos_evenPair_fiveHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 526) P :=
  singular_series_finite_pos_evenPair (by decide : Even 526) P

theorem singular_series_finite_pos_evenPair_fiveHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 528) P :=
  singular_series_finite_pos_evenPair (by decide : Even 528) P

theorem singular_series_finite_pos_evenPair_fiveHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 530) P :=
  singular_series_finite_pos_evenPair (by decide : Even 530) P

theorem nu_p_fiveHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 522) p = if p = 2 ∨ p ∣ 522 then 1 else 2 :=
  nu_p_evenPair (by decide : (522 : ℕ) ≠ 0) (by decide : Even 522) hp

theorem nu_p_fiveHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 524) p = if p = 2 ∨ p ∣ 524 then 1 else 2 :=
  nu_p_evenPair (by decide : (524 : ℕ) ≠ 0) (by decide : Even 524) hp

theorem nu_p_fiveHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 526) p = if p = 2 ∨ p ∣ 526 then 1 else 2 :=
  nu_p_evenPair (by decide : (526 : ℕ) ≠ 0) (by decide : Even 526) hp

theorem nu_p_fiveHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 528) p = if p = 2 ∨ p ∣ 528 then 1 else 2 :=
  nu_p_evenPair (by decide : (528 : ℕ) ≠ 0) (by decide : Even 528) hp

theorem nu_p_fiveHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 530) p = if p = 2 ∨ p ∣ 530 then 1 else 2 :=
  nu_p_evenPair (by decide : (530 : ℕ) ≠ 0) (by decide : Even 530) hp

theorem nu_p_fiveHundredTwentyTwo_two : nu_p (evenPair 522) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 522)

theorem localFactor_fiveHundredTwentyTwo_two : localFactor (evenPair 522) 2 = 2 :=
  localFactor_evenPair_two (by decide : (522 : ℕ) ≠ 0) (by decide : Even 522)

theorem nu_p_fiveHundredThirty_two : nu_p (evenPair 530) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 530)

theorem localFactor_fiveHundredThirty_two : localFactor (evenPair 530) 2 = 2 :=
  localFactor_evenPair_two (by decide : (530 : ℕ) ≠ 0) (by decide : Even 530)

end Brockian.SingularSeries.Gaps522530
