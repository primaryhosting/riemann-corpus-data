/-
  Brockian/SingularSeriesGaps20322040.lean — even binary gaps n ∈ {2032, 2034, 2036, 2038, 2040}.

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

namespace Brockian.SingularSeries.Gaps20322040

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandThirtyTwo : (evenPair 2032).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2032 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandThirtyFour : (evenPair 2034).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2034 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandThirtySix : (evenPair 2036).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2036 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandThirtyEight : (evenPair 2038).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2038 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandForty : (evenPair 2040).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2040 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandThirtyTwo : IsAdmissible (evenPair 2032) :=
  isAdmissible_evenPair (by decide : Even 2032)

theorem isAdmissible_evenPair_twoThousandThirtyFour : IsAdmissible (evenPair 2034) :=
  isAdmissible_evenPair (by decide : Even 2034)

theorem isAdmissible_evenPair_twoThousandThirtySix : IsAdmissible (evenPair 2036) :=
  isAdmissible_evenPair (by decide : Even 2036)

theorem isAdmissible_evenPair_twoThousandThirtyEight : IsAdmissible (evenPair 2038) :=
  isAdmissible_evenPair (by decide : Even 2038)

theorem isAdmissible_evenPair_twoThousandForty : IsAdmissible (evenPair 2040) :=
  isAdmissible_evenPair (by decide : Even 2040)

theorem singular_series_pos_evenPair_twoThousandThirtyTwo : 0 < singularSeries (evenPair 2032) :=
  singular_series_pos_evenPair (by decide : Even 2032)

theorem singular_series_pos_evenPair_twoThousandThirtyFour : 0 < singularSeries (evenPair 2034) :=
  singular_series_pos_evenPair (by decide : Even 2034)

theorem singular_series_pos_evenPair_twoThousandThirtySix : 0 < singularSeries (evenPair 2036) :=
  singular_series_pos_evenPair (by decide : Even 2036)

theorem singular_series_pos_evenPair_twoThousandThirtyEight : 0 < singularSeries (evenPair 2038) :=
  singular_series_pos_evenPair (by decide : Even 2038)

theorem singular_series_pos_evenPair_twoThousandForty : 0 < singularSeries (evenPair 2040) :=
  singular_series_pos_evenPair (by decide : Even 2040)

theorem singular_series_finite_pos_evenPair_twoThousandThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2032) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2032) P

theorem singular_series_finite_pos_evenPair_twoThousandThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2034) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2034) P

theorem singular_series_finite_pos_evenPair_twoThousandThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2036) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2036) P

theorem singular_series_finite_pos_evenPair_twoThousandThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2038) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2038) P

theorem singular_series_finite_pos_evenPair_twoThousandForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2040) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2040) P

theorem nu_p_twoThousandThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2032) p = if p = 2 ∨ p ∣ 2032 then 1 else 2 :=
  nu_p_evenPair (by decide : (2032 : ℕ) ≠ 0) (by decide : Even 2032) hp

theorem nu_p_twoThousandThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2034) p = if p = 2 ∨ p ∣ 2034 then 1 else 2 :=
  nu_p_evenPair (by decide : (2034 : ℕ) ≠ 0) (by decide : Even 2034) hp

theorem nu_p_twoThousandThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2036) p = if p = 2 ∨ p ∣ 2036 then 1 else 2 :=
  nu_p_evenPair (by decide : (2036 : ℕ) ≠ 0) (by decide : Even 2036) hp

theorem nu_p_twoThousandThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2038) p = if p = 2 ∨ p ∣ 2038 then 1 else 2 :=
  nu_p_evenPair (by decide : (2038 : ℕ) ≠ 0) (by decide : Even 2038) hp

theorem nu_p_twoThousandForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2040) p = if p = 2 ∨ p ∣ 2040 then 1 else 2 :=
  nu_p_evenPair (by decide : (2040 : ℕ) ≠ 0) (by decide : Even 2040) hp

theorem nu_p_twoThousandThirtyTwo_two : nu_p (evenPair 2032) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2032)

theorem localFactor_twoThousandThirtyTwo_two : localFactor (evenPair 2032) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2032 : ℕ) ≠ 0) (by decide : Even 2032)

theorem nu_p_twoThousandForty_two : nu_p (evenPair 2040) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2040)

theorem localFactor_twoThousandForty_two : localFactor (evenPair 2040) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2040 : ℕ) ≠ 0) (by decide : Even 2040)

end Brockian.SingularSeries.Gaps20322040
