/-
  Brockian/SingularSeriesGaps14321440.lean — even binary gaps n ∈ {1432, 1434, 1436, 1438, 1440}.

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

namespace Brockian.SingularSeries.Gaps14321440

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFourHundredThirtyTwo : (evenPair 1432).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1432 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredThirtyFour : (evenPair 1434).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1434 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredThirtySix : (evenPair 1436).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1436 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredThirtyEight : (evenPair 1438).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1438 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredForty : (evenPair 1440).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1440 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFourHundredThirtyTwo : IsAdmissible (evenPair 1432) :=
  isAdmissible_evenPair (by decide : Even 1432)

theorem isAdmissible_evenPair_oneThousandFourHundredThirtyFour : IsAdmissible (evenPair 1434) :=
  isAdmissible_evenPair (by decide : Even 1434)

theorem isAdmissible_evenPair_oneThousandFourHundredThirtySix : IsAdmissible (evenPair 1436) :=
  isAdmissible_evenPair (by decide : Even 1436)

theorem isAdmissible_evenPair_oneThousandFourHundredThirtyEight : IsAdmissible (evenPair 1438) :=
  isAdmissible_evenPair (by decide : Even 1438)

theorem isAdmissible_evenPair_oneThousandFourHundredForty : IsAdmissible (evenPair 1440) :=
  isAdmissible_evenPair (by decide : Even 1440)

theorem singular_series_pos_evenPair_oneThousandFourHundredThirtyTwo : 0 < singularSeries (evenPair 1432) :=
  singular_series_pos_evenPair (by decide : Even 1432)

theorem singular_series_pos_evenPair_oneThousandFourHundredThirtyFour : 0 < singularSeries (evenPair 1434) :=
  singular_series_pos_evenPair (by decide : Even 1434)

theorem singular_series_pos_evenPair_oneThousandFourHundredThirtySix : 0 < singularSeries (evenPair 1436) :=
  singular_series_pos_evenPair (by decide : Even 1436)

theorem singular_series_pos_evenPair_oneThousandFourHundredThirtyEight : 0 < singularSeries (evenPair 1438) :=
  singular_series_pos_evenPair (by decide : Even 1438)

theorem singular_series_pos_evenPair_oneThousandFourHundredForty : 0 < singularSeries (evenPair 1440) :=
  singular_series_pos_evenPair (by decide : Even 1440)

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1432) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1432) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1434) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1434) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1436) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1436) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1438) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1438) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1440) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1440) P

theorem nu_p_oneThousandFourHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1432) p = if p = 2 ∨ p ∣ 1432 then 1 else 2 :=
  nu_p_evenPair (by decide : (1432 : ℕ) ≠ 0) (by decide : Even 1432) hp

theorem nu_p_oneThousandFourHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1434) p = if p = 2 ∨ p ∣ 1434 then 1 else 2 :=
  nu_p_evenPair (by decide : (1434 : ℕ) ≠ 0) (by decide : Even 1434) hp

theorem nu_p_oneThousandFourHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1436) p = if p = 2 ∨ p ∣ 1436 then 1 else 2 :=
  nu_p_evenPair (by decide : (1436 : ℕ) ≠ 0) (by decide : Even 1436) hp

theorem nu_p_oneThousandFourHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1438) p = if p = 2 ∨ p ∣ 1438 then 1 else 2 :=
  nu_p_evenPair (by decide : (1438 : ℕ) ≠ 0) (by decide : Even 1438) hp

theorem nu_p_oneThousandFourHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1440) p = if p = 2 ∨ p ∣ 1440 then 1 else 2 :=
  nu_p_evenPair (by decide : (1440 : ℕ) ≠ 0) (by decide : Even 1440) hp

theorem nu_p_oneThousandFourHundredThirtyTwo_two : nu_p (evenPair 1432) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1432)

theorem localFactor_oneThousandFourHundredThirtyTwo_two : localFactor (evenPair 1432) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1432 : ℕ) ≠ 0) (by decide : Even 1432)

theorem nu_p_oneThousandFourHundredForty_two : nu_p (evenPair 1440) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1440)

theorem localFactor_oneThousandFourHundredForty_two : localFactor (evenPair 1440) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1440 : ℕ) ≠ 0) (by decide : Even 1440)

end Brockian.SingularSeries.Gaps14321440
