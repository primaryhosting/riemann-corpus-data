/-
  Brockian/SingularSeriesGaps422430.lean — even binary gaps n ∈ {422, 424, 426, 428, 430}.

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

namespace Brockian.SingularSeries.Gaps422430

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fourHundredTwentyTwo : (evenPair 422).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (422 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredTwentyFour : (evenPair 424).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (424 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredTwentySix : (evenPair 426).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (426 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredTwentyEight : (evenPair 428).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (428 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredThirty : (evenPair 430).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (430 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fourHundredTwentyTwo : IsAdmissible (evenPair 422) :=
  isAdmissible_evenPair (by decide : Even 422)

theorem isAdmissible_evenPair_fourHundredTwentyFour : IsAdmissible (evenPair 424) :=
  isAdmissible_evenPair (by decide : Even 424)

theorem isAdmissible_evenPair_fourHundredTwentySix : IsAdmissible (evenPair 426) :=
  isAdmissible_evenPair (by decide : Even 426)

theorem isAdmissible_evenPair_fourHundredTwentyEight : IsAdmissible (evenPair 428) :=
  isAdmissible_evenPair (by decide : Even 428)

theorem isAdmissible_evenPair_fourHundredThirty : IsAdmissible (evenPair 430) :=
  isAdmissible_evenPair (by decide : Even 430)

theorem singular_series_pos_evenPair_fourHundredTwentyTwo : 0 < singularSeries (evenPair 422) :=
  singular_series_pos_evenPair (by decide : Even 422)

theorem singular_series_pos_evenPair_fourHundredTwentyFour : 0 < singularSeries (evenPair 424) :=
  singular_series_pos_evenPair (by decide : Even 424)

theorem singular_series_pos_evenPair_fourHundredTwentySix : 0 < singularSeries (evenPair 426) :=
  singular_series_pos_evenPair (by decide : Even 426)

theorem singular_series_pos_evenPair_fourHundredTwentyEight : 0 < singularSeries (evenPair 428) :=
  singular_series_pos_evenPair (by decide : Even 428)

theorem singular_series_pos_evenPair_fourHundredThirty : 0 < singularSeries (evenPair 430) :=
  singular_series_pos_evenPair (by decide : Even 430)

theorem singular_series_finite_pos_evenPair_fourHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 422) P :=
  singular_series_finite_pos_evenPair (by decide : Even 422) P

theorem singular_series_finite_pos_evenPair_fourHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 424) P :=
  singular_series_finite_pos_evenPair (by decide : Even 424) P

theorem singular_series_finite_pos_evenPair_fourHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 426) P :=
  singular_series_finite_pos_evenPair (by decide : Even 426) P

theorem singular_series_finite_pos_evenPair_fourHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 428) P :=
  singular_series_finite_pos_evenPair (by decide : Even 428) P

theorem singular_series_finite_pos_evenPair_fourHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 430) P :=
  singular_series_finite_pos_evenPair (by decide : Even 430) P

theorem nu_p_fourHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 422) p = if p = 2 ∨ p ∣ 422 then 1 else 2 :=
  nu_p_evenPair (by decide : (422 : ℕ) ≠ 0) (by decide : Even 422) hp

theorem nu_p_fourHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 424) p = if p = 2 ∨ p ∣ 424 then 1 else 2 :=
  nu_p_evenPair (by decide : (424 : ℕ) ≠ 0) (by decide : Even 424) hp

theorem nu_p_fourHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 426) p = if p = 2 ∨ p ∣ 426 then 1 else 2 :=
  nu_p_evenPair (by decide : (426 : ℕ) ≠ 0) (by decide : Even 426) hp

theorem nu_p_fourHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 428) p = if p = 2 ∨ p ∣ 428 then 1 else 2 :=
  nu_p_evenPair (by decide : (428 : ℕ) ≠ 0) (by decide : Even 428) hp

theorem nu_p_fourHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 430) p = if p = 2 ∨ p ∣ 430 then 1 else 2 :=
  nu_p_evenPair (by decide : (430 : ℕ) ≠ 0) (by decide : Even 430) hp

theorem nu_p_fourHundredTwentyTwo_two : nu_p (evenPair 422) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 422)

theorem localFactor_fourHundredTwentyTwo_two : localFactor (evenPair 422) 2 = 2 :=
  localFactor_evenPair_two (by decide : (422 : ℕ) ≠ 0) (by decide : Even 422)

theorem nu_p_fourHundredThirty_two : nu_p (evenPair 430) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 430)

theorem localFactor_fourHundredThirty_two : localFactor (evenPair 430) 2 = 2 :=
  localFactor_evenPair_two (by decide : (430 : ℕ) ≠ 0) (by decide : Even 430)

end Brockian.SingularSeries.Gaps422430
