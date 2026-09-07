/-
  Brockian/SingularSeriesGaps16721680.lean — even binary gaps n ∈ {1672, 1674, 1676, 1678, 1680}.

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

namespace Brockian.SingularSeries.Gaps16721680

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixHundredSeventyTwo : (evenPair 1672).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1672 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredSeventyFour : (evenPair 1674).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1674 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredSeventySix : (evenPair 1676).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1676 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredSeventyEight : (evenPair 1678).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1678 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredEighty : (evenPair 1680).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1680 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixHundredSeventyTwo : IsAdmissible (evenPair 1672) :=
  isAdmissible_evenPair (by decide : Even 1672)

theorem isAdmissible_evenPair_oneThousandSixHundredSeventyFour : IsAdmissible (evenPair 1674) :=
  isAdmissible_evenPair (by decide : Even 1674)

theorem isAdmissible_evenPair_oneThousandSixHundredSeventySix : IsAdmissible (evenPair 1676) :=
  isAdmissible_evenPair (by decide : Even 1676)

theorem isAdmissible_evenPair_oneThousandSixHundredSeventyEight : IsAdmissible (evenPair 1678) :=
  isAdmissible_evenPair (by decide : Even 1678)

theorem isAdmissible_evenPair_oneThousandSixHundredEighty : IsAdmissible (evenPair 1680) :=
  isAdmissible_evenPair (by decide : Even 1680)

theorem singular_series_pos_evenPair_oneThousandSixHundredSeventyTwo : 0 < singularSeries (evenPair 1672) :=
  singular_series_pos_evenPair (by decide : Even 1672)

theorem singular_series_pos_evenPair_oneThousandSixHundredSeventyFour : 0 < singularSeries (evenPair 1674) :=
  singular_series_pos_evenPair (by decide : Even 1674)

theorem singular_series_pos_evenPair_oneThousandSixHundredSeventySix : 0 < singularSeries (evenPair 1676) :=
  singular_series_pos_evenPair (by decide : Even 1676)

theorem singular_series_pos_evenPair_oneThousandSixHundredSeventyEight : 0 < singularSeries (evenPair 1678) :=
  singular_series_pos_evenPair (by decide : Even 1678)

theorem singular_series_pos_evenPair_oneThousandSixHundredEighty : 0 < singularSeries (evenPair 1680) :=
  singular_series_pos_evenPair (by decide : Even 1680)

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1672) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1672) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1674) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1674) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1676) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1676) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1678) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1678) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1680) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1680) P

theorem nu_p_oneThousandSixHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1672) p = if p = 2 ∨ p ∣ 1672 then 1 else 2 :=
  nu_p_evenPair (by decide : (1672 : ℕ) ≠ 0) (by decide : Even 1672) hp

theorem nu_p_oneThousandSixHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1674) p = if p = 2 ∨ p ∣ 1674 then 1 else 2 :=
  nu_p_evenPair (by decide : (1674 : ℕ) ≠ 0) (by decide : Even 1674) hp

theorem nu_p_oneThousandSixHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1676) p = if p = 2 ∨ p ∣ 1676 then 1 else 2 :=
  nu_p_evenPair (by decide : (1676 : ℕ) ≠ 0) (by decide : Even 1676) hp

theorem nu_p_oneThousandSixHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1678) p = if p = 2 ∨ p ∣ 1678 then 1 else 2 :=
  nu_p_evenPair (by decide : (1678 : ℕ) ≠ 0) (by decide : Even 1678) hp

theorem nu_p_oneThousandSixHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1680) p = if p = 2 ∨ p ∣ 1680 then 1 else 2 :=
  nu_p_evenPair (by decide : (1680 : ℕ) ≠ 0) (by decide : Even 1680) hp

theorem nu_p_oneThousandSixHundredSeventyTwo_two : nu_p (evenPair 1672) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1672)

theorem localFactor_oneThousandSixHundredSeventyTwo_two : localFactor (evenPair 1672) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1672 : ℕ) ≠ 0) (by decide : Even 1672)

theorem nu_p_oneThousandSixHundredEighty_two : nu_p (evenPair 1680) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1680)

theorem localFactor_oneThousandSixHundredEighty_two : localFactor (evenPair 1680) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1680 : ℕ) ≠ 0) (by decide : Even 1680)

end Brockian.SingularSeries.Gaps16721680
