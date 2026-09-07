/-
  Brockian/SingularSeriesGaps16321640.lean — even binary gaps n ∈ {1632, 1634, 1636, 1638, 1640}.

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

namespace Brockian.SingularSeries.Gaps16321640

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixHundredThirtyTwo : (evenPair 1632).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1632 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredThirtyFour : (evenPair 1634).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1634 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredThirtySix : (evenPair 1636).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1636 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredThirtyEight : (evenPair 1638).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1638 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredForty : (evenPair 1640).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1640 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixHundredThirtyTwo : IsAdmissible (evenPair 1632) :=
  isAdmissible_evenPair (by decide : Even 1632)

theorem isAdmissible_evenPair_oneThousandSixHundredThirtyFour : IsAdmissible (evenPair 1634) :=
  isAdmissible_evenPair (by decide : Even 1634)

theorem isAdmissible_evenPair_oneThousandSixHundredThirtySix : IsAdmissible (evenPair 1636) :=
  isAdmissible_evenPair (by decide : Even 1636)

theorem isAdmissible_evenPair_oneThousandSixHundredThirtyEight : IsAdmissible (evenPair 1638) :=
  isAdmissible_evenPair (by decide : Even 1638)

theorem isAdmissible_evenPair_oneThousandSixHundredForty : IsAdmissible (evenPair 1640) :=
  isAdmissible_evenPair (by decide : Even 1640)

theorem singular_series_pos_evenPair_oneThousandSixHundredThirtyTwo : 0 < singularSeries (evenPair 1632) :=
  singular_series_pos_evenPair (by decide : Even 1632)

theorem singular_series_pos_evenPair_oneThousandSixHundredThirtyFour : 0 < singularSeries (evenPair 1634) :=
  singular_series_pos_evenPair (by decide : Even 1634)

theorem singular_series_pos_evenPair_oneThousandSixHundredThirtySix : 0 < singularSeries (evenPair 1636) :=
  singular_series_pos_evenPair (by decide : Even 1636)

theorem singular_series_pos_evenPair_oneThousandSixHundredThirtyEight : 0 < singularSeries (evenPair 1638) :=
  singular_series_pos_evenPair (by decide : Even 1638)

theorem singular_series_pos_evenPair_oneThousandSixHundredForty : 0 < singularSeries (evenPair 1640) :=
  singular_series_pos_evenPair (by decide : Even 1640)

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1632) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1632) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1634) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1634) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1636) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1636) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1638) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1638) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1640) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1640) P

theorem nu_p_oneThousandSixHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1632) p = if p = 2 ∨ p ∣ 1632 then 1 else 2 :=
  nu_p_evenPair (by decide : (1632 : ℕ) ≠ 0) (by decide : Even 1632) hp

theorem nu_p_oneThousandSixHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1634) p = if p = 2 ∨ p ∣ 1634 then 1 else 2 :=
  nu_p_evenPair (by decide : (1634 : ℕ) ≠ 0) (by decide : Even 1634) hp

theorem nu_p_oneThousandSixHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1636) p = if p = 2 ∨ p ∣ 1636 then 1 else 2 :=
  nu_p_evenPair (by decide : (1636 : ℕ) ≠ 0) (by decide : Even 1636) hp

theorem nu_p_oneThousandSixHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1638) p = if p = 2 ∨ p ∣ 1638 then 1 else 2 :=
  nu_p_evenPair (by decide : (1638 : ℕ) ≠ 0) (by decide : Even 1638) hp

theorem nu_p_oneThousandSixHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1640) p = if p = 2 ∨ p ∣ 1640 then 1 else 2 :=
  nu_p_evenPair (by decide : (1640 : ℕ) ≠ 0) (by decide : Even 1640) hp

theorem nu_p_oneThousandSixHundredThirtyTwo_two : nu_p (evenPair 1632) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1632)

theorem localFactor_oneThousandSixHundredThirtyTwo_two : localFactor (evenPair 1632) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1632 : ℕ) ≠ 0) (by decide : Even 1632)

theorem nu_p_oneThousandSixHundredForty_two : nu_p (evenPair 1640) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1640)

theorem localFactor_oneThousandSixHundredForty_two : localFactor (evenPair 1640) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1640 : ℕ) ≠ 0) (by decide : Even 1640)

end Brockian.SingularSeries.Gaps16321640
