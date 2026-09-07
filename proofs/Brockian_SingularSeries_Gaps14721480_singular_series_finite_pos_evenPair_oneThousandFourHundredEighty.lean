/-
  Brockian/SingularSeriesGaps14721480.lean — even binary gaps n ∈ {1472, 1474, 1476, 1478, 1480}.

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

namespace Brockian.SingularSeries.Gaps14721480

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFourHundredSeventyTwo : (evenPair 1472).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1472 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredSeventyFour : (evenPair 1474).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1474 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredSeventySix : (evenPair 1476).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1476 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredSeventyEight : (evenPair 1478).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1478 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredEighty : (evenPair 1480).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1480 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFourHundredSeventyTwo : IsAdmissible (evenPair 1472) :=
  isAdmissible_evenPair (by decide : Even 1472)

theorem isAdmissible_evenPair_oneThousandFourHundredSeventyFour : IsAdmissible (evenPair 1474) :=
  isAdmissible_evenPair (by decide : Even 1474)

theorem isAdmissible_evenPair_oneThousandFourHundredSeventySix : IsAdmissible (evenPair 1476) :=
  isAdmissible_evenPair (by decide : Even 1476)

theorem isAdmissible_evenPair_oneThousandFourHundredSeventyEight : IsAdmissible (evenPair 1478) :=
  isAdmissible_evenPair (by decide : Even 1478)

theorem isAdmissible_evenPair_oneThousandFourHundredEighty : IsAdmissible (evenPair 1480) :=
  isAdmissible_evenPair (by decide : Even 1480)

theorem singular_series_pos_evenPair_oneThousandFourHundredSeventyTwo : 0 < singularSeries (evenPair 1472) :=
  singular_series_pos_evenPair (by decide : Even 1472)

theorem singular_series_pos_evenPair_oneThousandFourHundredSeventyFour : 0 < singularSeries (evenPair 1474) :=
  singular_series_pos_evenPair (by decide : Even 1474)

theorem singular_series_pos_evenPair_oneThousandFourHundredSeventySix : 0 < singularSeries (evenPair 1476) :=
  singular_series_pos_evenPair (by decide : Even 1476)

theorem singular_series_pos_evenPair_oneThousandFourHundredSeventyEight : 0 < singularSeries (evenPair 1478) :=
  singular_series_pos_evenPair (by decide : Even 1478)

theorem singular_series_pos_evenPair_oneThousandFourHundredEighty : 0 < singularSeries (evenPair 1480) :=
  singular_series_pos_evenPair (by decide : Even 1480)

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1472) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1472) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1474) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1474) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1476) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1476) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1478) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1478) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1480) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1480) P

theorem nu_p_oneThousandFourHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1472) p = if p = 2 ∨ p ∣ 1472 then 1 else 2 :=
  nu_p_evenPair (by decide : (1472 : ℕ) ≠ 0) (by decide : Even 1472) hp

theorem nu_p_oneThousandFourHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1474) p = if p = 2 ∨ p ∣ 1474 then 1 else 2 :=
  nu_p_evenPair (by decide : (1474 : ℕ) ≠ 0) (by decide : Even 1474) hp

theorem nu_p_oneThousandFourHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1476) p = if p = 2 ∨ p ∣ 1476 then 1 else 2 :=
  nu_p_evenPair (by decide : (1476 : ℕ) ≠ 0) (by decide : Even 1476) hp

theorem nu_p_oneThousandFourHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1478) p = if p = 2 ∨ p ∣ 1478 then 1 else 2 :=
  nu_p_evenPair (by decide : (1478 : ℕ) ≠ 0) (by decide : Even 1478) hp

theorem nu_p_oneThousandFourHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1480) p = if p = 2 ∨ p ∣ 1480 then 1 else 2 :=
  nu_p_evenPair (by decide : (1480 : ℕ) ≠ 0) (by decide : Even 1480) hp

theorem nu_p_oneThousandFourHundredSeventyTwo_two : nu_p (evenPair 1472) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1472)

theorem localFactor_oneThousandFourHundredSeventyTwo_two : localFactor (evenPair 1472) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1472 : ℕ) ≠ 0) (by decide : Even 1472)

theorem nu_p_oneThousandFourHundredEighty_two : nu_p (evenPair 1480) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1480)

theorem localFactor_oneThousandFourHundredEighty_two : localFactor (evenPair 1480) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1480 : ℕ) ≠ 0) (by decide : Even 1480)

end Brockian.SingularSeries.Gaps14721480
