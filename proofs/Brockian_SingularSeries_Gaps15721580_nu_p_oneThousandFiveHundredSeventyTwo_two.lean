/-
  Brockian/SingularSeriesGaps15721580.lean — even binary gaps n ∈ {1572, 1574, 1576, 1578, 1580}.

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

namespace Brockian.SingularSeries.Gaps15721580

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiveHundredSeventyTwo : (evenPair 1572).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1572 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredSeventyFour : (evenPair 1574).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1574 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredSeventySix : (evenPair 1576).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1576 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredSeventyEight : (evenPair 1578).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1578 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredEighty : (evenPair 1580).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1580 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiveHundredSeventyTwo : IsAdmissible (evenPair 1572) :=
  isAdmissible_evenPair (by decide : Even 1572)

theorem isAdmissible_evenPair_oneThousandFiveHundredSeventyFour : IsAdmissible (evenPair 1574) :=
  isAdmissible_evenPair (by decide : Even 1574)

theorem isAdmissible_evenPair_oneThousandFiveHundredSeventySix : IsAdmissible (evenPair 1576) :=
  isAdmissible_evenPair (by decide : Even 1576)

theorem isAdmissible_evenPair_oneThousandFiveHundredSeventyEight : IsAdmissible (evenPair 1578) :=
  isAdmissible_evenPair (by decide : Even 1578)

theorem isAdmissible_evenPair_oneThousandFiveHundredEighty : IsAdmissible (evenPair 1580) :=
  isAdmissible_evenPair (by decide : Even 1580)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSeventyTwo : 0 < singularSeries (evenPair 1572) :=
  singular_series_pos_evenPair (by decide : Even 1572)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSeventyFour : 0 < singularSeries (evenPair 1574) :=
  singular_series_pos_evenPair (by decide : Even 1574)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSeventySix : 0 < singularSeries (evenPair 1576) :=
  singular_series_pos_evenPair (by decide : Even 1576)

theorem singular_series_pos_evenPair_oneThousandFiveHundredSeventyEight : 0 < singularSeries (evenPair 1578) :=
  singular_series_pos_evenPair (by decide : Even 1578)

theorem singular_series_pos_evenPair_oneThousandFiveHundredEighty : 0 < singularSeries (evenPair 1580) :=
  singular_series_pos_evenPair (by decide : Even 1580)

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1572) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1572) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1574) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1574) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1576) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1576) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1578) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1578) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1580) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1580) P

theorem nu_p_oneThousandFiveHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1572) p = if p = 2 ∨ p ∣ 1572 then 1 else 2 :=
  nu_p_evenPair (by decide : (1572 : ℕ) ≠ 0) (by decide : Even 1572) hp

theorem nu_p_oneThousandFiveHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1574) p = if p = 2 ∨ p ∣ 1574 then 1 else 2 :=
  nu_p_evenPair (by decide : (1574 : ℕ) ≠ 0) (by decide : Even 1574) hp

theorem nu_p_oneThousandFiveHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1576) p = if p = 2 ∨ p ∣ 1576 then 1 else 2 :=
  nu_p_evenPair (by decide : (1576 : ℕ) ≠ 0) (by decide : Even 1576) hp

theorem nu_p_oneThousandFiveHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1578) p = if p = 2 ∨ p ∣ 1578 then 1 else 2 :=
  nu_p_evenPair (by decide : (1578 : ℕ) ≠ 0) (by decide : Even 1578) hp

theorem nu_p_oneThousandFiveHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1580) p = if p = 2 ∨ p ∣ 1580 then 1 else 2 :=
  nu_p_evenPair (by decide : (1580 : ℕ) ≠ 0) (by decide : Even 1580) hp

theorem nu_p_oneThousandFiveHundredSeventyTwo_two : nu_p (evenPair 1572) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1572)

theorem localFactor_oneThousandFiveHundredSeventyTwo_two : localFactor (evenPair 1572) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1572 : ℕ) ≠ 0) (by decide : Even 1572)

theorem nu_p_oneThousandFiveHundredEighty_two : nu_p (evenPair 1580) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1580)

theorem localFactor_oneThousandFiveHundredEighty_two : localFactor (evenPair 1580) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1580 : ℕ) ≠ 0) (by decide : Even 1580)

end Brockian.SingularSeries.Gaps15721580
