/-
  Brockian/SingularSeriesGaps16221630.lean — even binary gaps n ∈ {1622, 1624, 1626, 1628, 1630}.

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

namespace Brockian.SingularSeries.Gaps16221630

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixHundredTwentyTwo : (evenPair 1622).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1622 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredTwentyFour : (evenPair 1624).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1624 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredTwentySix : (evenPair 1626).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1626 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredTwentyEight : (evenPair 1628).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1628 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredThirty : (evenPair 1630).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1630 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixHundredTwentyTwo : IsAdmissible (evenPair 1622) :=
  isAdmissible_evenPair (by decide : Even 1622)

theorem isAdmissible_evenPair_oneThousandSixHundredTwentyFour : IsAdmissible (evenPair 1624) :=
  isAdmissible_evenPair (by decide : Even 1624)

theorem isAdmissible_evenPair_oneThousandSixHundredTwentySix : IsAdmissible (evenPair 1626) :=
  isAdmissible_evenPair (by decide : Even 1626)

theorem isAdmissible_evenPair_oneThousandSixHundredTwentyEight : IsAdmissible (evenPair 1628) :=
  isAdmissible_evenPair (by decide : Even 1628)

theorem isAdmissible_evenPair_oneThousandSixHundredThirty : IsAdmissible (evenPair 1630) :=
  isAdmissible_evenPair (by decide : Even 1630)

theorem singular_series_pos_evenPair_oneThousandSixHundredTwentyTwo : 0 < singularSeries (evenPair 1622) :=
  singular_series_pos_evenPair (by decide : Even 1622)

theorem singular_series_pos_evenPair_oneThousandSixHundredTwentyFour : 0 < singularSeries (evenPair 1624) :=
  singular_series_pos_evenPair (by decide : Even 1624)

theorem singular_series_pos_evenPair_oneThousandSixHundredTwentySix : 0 < singularSeries (evenPair 1626) :=
  singular_series_pos_evenPair (by decide : Even 1626)

theorem singular_series_pos_evenPair_oneThousandSixHundredTwentyEight : 0 < singularSeries (evenPair 1628) :=
  singular_series_pos_evenPair (by decide : Even 1628)

theorem singular_series_pos_evenPair_oneThousandSixHundredThirty : 0 < singularSeries (evenPair 1630) :=
  singular_series_pos_evenPair (by decide : Even 1630)

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1622) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1622) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1624) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1624) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1626) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1626) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1628) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1628) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1630) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1630) P

theorem nu_p_oneThousandSixHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1622) p = if p = 2 ∨ p ∣ 1622 then 1 else 2 :=
  nu_p_evenPair (by decide : (1622 : ℕ) ≠ 0) (by decide : Even 1622) hp

theorem nu_p_oneThousandSixHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1624) p = if p = 2 ∨ p ∣ 1624 then 1 else 2 :=
  nu_p_evenPair (by decide : (1624 : ℕ) ≠ 0) (by decide : Even 1624) hp

theorem nu_p_oneThousandSixHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1626) p = if p = 2 ∨ p ∣ 1626 then 1 else 2 :=
  nu_p_evenPair (by decide : (1626 : ℕ) ≠ 0) (by decide : Even 1626) hp

theorem nu_p_oneThousandSixHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1628) p = if p = 2 ∨ p ∣ 1628 then 1 else 2 :=
  nu_p_evenPair (by decide : (1628 : ℕ) ≠ 0) (by decide : Even 1628) hp

theorem nu_p_oneThousandSixHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1630) p = if p = 2 ∨ p ∣ 1630 then 1 else 2 :=
  nu_p_evenPair (by decide : (1630 : ℕ) ≠ 0) (by decide : Even 1630) hp

theorem nu_p_oneThousandSixHundredTwentyTwo_two : nu_p (evenPair 1622) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1622)

theorem localFactor_oneThousandSixHundredTwentyTwo_two : localFactor (evenPair 1622) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1622 : ℕ) ≠ 0) (by decide : Even 1622)

theorem nu_p_oneThousandSixHundredThirty_two : nu_p (evenPair 1630) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1630)

theorem localFactor_oneThousandSixHundredThirty_two : localFactor (evenPair 1630) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1630 : ℕ) ≠ 0) (by decide : Even 1630)

end Brockian.SingularSeries.Gaps16221630
