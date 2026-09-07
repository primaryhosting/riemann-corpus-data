/-
  Brockian/SingularSeriesGaps14221430.lean — even binary gaps n ∈ {1422, 1424, 1426, 1428, 1430}.

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

namespace Brockian.SingularSeries.Gaps14221430

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFourHundredTwentyTwo : (evenPair 1422).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1422 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredTwentyFour : (evenPair 1424).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1424 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredTwentySix : (evenPair 1426).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1426 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredTwentyEight : (evenPair 1428).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1428 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredThirty : (evenPair 1430).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1430 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFourHundredTwentyTwo : IsAdmissible (evenPair 1422) :=
  isAdmissible_evenPair (by decide : Even 1422)

theorem isAdmissible_evenPair_oneThousandFourHundredTwentyFour : IsAdmissible (evenPair 1424) :=
  isAdmissible_evenPair (by decide : Even 1424)

theorem isAdmissible_evenPair_oneThousandFourHundredTwentySix : IsAdmissible (evenPair 1426) :=
  isAdmissible_evenPair (by decide : Even 1426)

theorem isAdmissible_evenPair_oneThousandFourHundredTwentyEight : IsAdmissible (evenPair 1428) :=
  isAdmissible_evenPair (by decide : Even 1428)

theorem isAdmissible_evenPair_oneThousandFourHundredThirty : IsAdmissible (evenPair 1430) :=
  isAdmissible_evenPair (by decide : Even 1430)

theorem singular_series_pos_evenPair_oneThousandFourHundredTwentyTwo : 0 < singularSeries (evenPair 1422) :=
  singular_series_pos_evenPair (by decide : Even 1422)

theorem singular_series_pos_evenPair_oneThousandFourHundredTwentyFour : 0 < singularSeries (evenPair 1424) :=
  singular_series_pos_evenPair (by decide : Even 1424)

theorem singular_series_pos_evenPair_oneThousandFourHundredTwentySix : 0 < singularSeries (evenPair 1426) :=
  singular_series_pos_evenPair (by decide : Even 1426)

theorem singular_series_pos_evenPair_oneThousandFourHundredTwentyEight : 0 < singularSeries (evenPair 1428) :=
  singular_series_pos_evenPair (by decide : Even 1428)

theorem singular_series_pos_evenPair_oneThousandFourHundredThirty : 0 < singularSeries (evenPair 1430) :=
  singular_series_pos_evenPair (by decide : Even 1430)

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1422) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1422) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1424) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1424) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1426) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1426) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1428) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1428) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1430) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1430) P

theorem nu_p_oneThousandFourHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1422) p = if p = 2 ∨ p ∣ 1422 then 1 else 2 :=
  nu_p_evenPair (by decide : (1422 : ℕ) ≠ 0) (by decide : Even 1422) hp

theorem nu_p_oneThousandFourHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1424) p = if p = 2 ∨ p ∣ 1424 then 1 else 2 :=
  nu_p_evenPair (by decide : (1424 : ℕ) ≠ 0) (by decide : Even 1424) hp

theorem nu_p_oneThousandFourHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1426) p = if p = 2 ∨ p ∣ 1426 then 1 else 2 :=
  nu_p_evenPair (by decide : (1426 : ℕ) ≠ 0) (by decide : Even 1426) hp

theorem nu_p_oneThousandFourHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1428) p = if p = 2 ∨ p ∣ 1428 then 1 else 2 :=
  nu_p_evenPair (by decide : (1428 : ℕ) ≠ 0) (by decide : Even 1428) hp

theorem nu_p_oneThousandFourHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1430) p = if p = 2 ∨ p ∣ 1430 then 1 else 2 :=
  nu_p_evenPair (by decide : (1430 : ℕ) ≠ 0) (by decide : Even 1430) hp

theorem nu_p_oneThousandFourHundredTwentyTwo_two : nu_p (evenPair 1422) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1422)

theorem localFactor_oneThousandFourHundredTwentyTwo_two : localFactor (evenPair 1422) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1422 : ℕ) ≠ 0) (by decide : Even 1422)

theorem nu_p_oneThousandFourHundredThirty_two : nu_p (evenPair 1430) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1430)

theorem localFactor_oneThousandFourHundredThirty_two : localFactor (evenPair 1430) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1430 : ℕ) ≠ 0) (by decide : Even 1430)

end Brockian.SingularSeries.Gaps14221430
