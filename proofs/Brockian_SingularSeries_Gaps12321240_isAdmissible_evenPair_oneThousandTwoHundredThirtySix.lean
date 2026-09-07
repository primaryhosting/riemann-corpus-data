/-
  Brockian/SingularSeriesGaps12321240.lean — even binary gaps n ∈ {1232, 1234, 1236, 1238, 1240}.

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

namespace Brockian.SingularSeries.Gaps12321240

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwoHundredThirtyTwo : (evenPair 1232).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1232 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredThirtyFour : (evenPair 1234).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1234 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredThirtySix : (evenPair 1236).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1236 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredThirtyEight : (evenPair 1238).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1238 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwoHundredForty : (evenPair 1240).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1240 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwoHundredThirtyTwo : IsAdmissible (evenPair 1232) :=
  isAdmissible_evenPair (by decide : Even 1232)

theorem isAdmissible_evenPair_oneThousandTwoHundredThirtyFour : IsAdmissible (evenPair 1234) :=
  isAdmissible_evenPair (by decide : Even 1234)

theorem isAdmissible_evenPair_oneThousandTwoHundredThirtySix : IsAdmissible (evenPair 1236) :=
  isAdmissible_evenPair (by decide : Even 1236)

theorem isAdmissible_evenPair_oneThousandTwoHundredThirtyEight : IsAdmissible (evenPair 1238) :=
  isAdmissible_evenPair (by decide : Even 1238)

theorem isAdmissible_evenPair_oneThousandTwoHundredForty : IsAdmissible (evenPair 1240) :=
  isAdmissible_evenPair (by decide : Even 1240)

theorem singular_series_pos_evenPair_oneThousandTwoHundredThirtyTwo : 0 < singularSeries (evenPair 1232) :=
  singular_series_pos_evenPair (by decide : Even 1232)

theorem singular_series_pos_evenPair_oneThousandTwoHundredThirtyFour : 0 < singularSeries (evenPair 1234) :=
  singular_series_pos_evenPair (by decide : Even 1234)

theorem singular_series_pos_evenPair_oneThousandTwoHundredThirtySix : 0 < singularSeries (evenPair 1236) :=
  singular_series_pos_evenPair (by decide : Even 1236)

theorem singular_series_pos_evenPair_oneThousandTwoHundredThirtyEight : 0 < singularSeries (evenPair 1238) :=
  singular_series_pos_evenPair (by decide : Even 1238)

theorem singular_series_pos_evenPair_oneThousandTwoHundredForty : 0 < singularSeries (evenPair 1240) :=
  singular_series_pos_evenPair (by decide : Even 1240)

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1232) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1232) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1234) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1234) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1236) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1236) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1238) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1238) P

theorem singular_series_finite_pos_evenPair_oneThousandTwoHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1240) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1240) P

theorem nu_p_oneThousandTwoHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1232) p = if p = 2 ∨ p ∣ 1232 then 1 else 2 :=
  nu_p_evenPair (by decide : (1232 : ℕ) ≠ 0) (by decide : Even 1232) hp

theorem nu_p_oneThousandTwoHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1234) p = if p = 2 ∨ p ∣ 1234 then 1 else 2 :=
  nu_p_evenPair (by decide : (1234 : ℕ) ≠ 0) (by decide : Even 1234) hp

theorem nu_p_oneThousandTwoHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1236) p = if p = 2 ∨ p ∣ 1236 then 1 else 2 :=
  nu_p_evenPair (by decide : (1236 : ℕ) ≠ 0) (by decide : Even 1236) hp

theorem nu_p_oneThousandTwoHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1238) p = if p = 2 ∨ p ∣ 1238 then 1 else 2 :=
  nu_p_evenPair (by decide : (1238 : ℕ) ≠ 0) (by decide : Even 1238) hp

theorem nu_p_oneThousandTwoHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1240) p = if p = 2 ∨ p ∣ 1240 then 1 else 2 :=
  nu_p_evenPair (by decide : (1240 : ℕ) ≠ 0) (by decide : Even 1240) hp

theorem nu_p_oneThousandTwoHundredThirtyTwo_two : nu_p (evenPair 1232) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1232)

theorem localFactor_oneThousandTwoHundredThirtyTwo_two : localFactor (evenPair 1232) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1232 : ℕ) ≠ 0) (by decide : Even 1232)

theorem nu_p_oneThousandTwoHundredForty_two : nu_p (evenPair 1240) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1240)

theorem localFactor_oneThousandTwoHundredForty_two : localFactor (evenPair 1240) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1240 : ℕ) ≠ 0) (by decide : Even 1240)

end Brockian.SingularSeries.Gaps12321240
