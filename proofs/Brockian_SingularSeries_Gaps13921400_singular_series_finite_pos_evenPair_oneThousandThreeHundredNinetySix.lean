/-
  Brockian/SingularSeriesGaps13921400.lean — even binary gaps n ∈ {1392, 1394, 1396, 1398, 1400}.

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

namespace Brockian.SingularSeries.Gaps13921400

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThreeHundredNinetyTwo : (evenPair 1392).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1392 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredNinetyFour : (evenPair 1394).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1394 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredNinetySix : (evenPair 1396).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1396 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredNinetyEight : (evenPair 1398).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1398 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundred : (evenPair 1400).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1400 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThreeHundredNinetyTwo : IsAdmissible (evenPair 1392) :=
  isAdmissible_evenPair (by decide : Even 1392)

theorem isAdmissible_evenPair_oneThousandThreeHundredNinetyFour : IsAdmissible (evenPair 1394) :=
  isAdmissible_evenPair (by decide : Even 1394)

theorem isAdmissible_evenPair_oneThousandThreeHundredNinetySix : IsAdmissible (evenPair 1396) :=
  isAdmissible_evenPair (by decide : Even 1396)

theorem isAdmissible_evenPair_oneThousandThreeHundredNinetyEight : IsAdmissible (evenPair 1398) :=
  isAdmissible_evenPair (by decide : Even 1398)

theorem isAdmissible_evenPair_oneThousandFourHundred : IsAdmissible (evenPair 1400) :=
  isAdmissible_evenPair (by decide : Even 1400)

theorem singular_series_pos_evenPair_oneThousandThreeHundredNinetyTwo : 0 < singularSeries (evenPair 1392) :=
  singular_series_pos_evenPair (by decide : Even 1392)

theorem singular_series_pos_evenPair_oneThousandThreeHundredNinetyFour : 0 < singularSeries (evenPair 1394) :=
  singular_series_pos_evenPair (by decide : Even 1394)

theorem singular_series_pos_evenPair_oneThousandThreeHundredNinetySix : 0 < singularSeries (evenPair 1396) :=
  singular_series_pos_evenPair (by decide : Even 1396)

theorem singular_series_pos_evenPair_oneThousandThreeHundredNinetyEight : 0 < singularSeries (evenPair 1398) :=
  singular_series_pos_evenPair (by decide : Even 1398)

theorem singular_series_pos_evenPair_oneThousandFourHundred : 0 < singularSeries (evenPair 1400) :=
  singular_series_pos_evenPair (by decide : Even 1400)

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1392) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1392) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1394) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1394) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1396) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1396) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1398) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1398) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1400) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1400) P

theorem nu_p_oneThousandThreeHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1392) p = if p = 2 ∨ p ∣ 1392 then 1 else 2 :=
  nu_p_evenPair (by decide : (1392 : ℕ) ≠ 0) (by decide : Even 1392) hp

theorem nu_p_oneThousandThreeHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1394) p = if p = 2 ∨ p ∣ 1394 then 1 else 2 :=
  nu_p_evenPair (by decide : (1394 : ℕ) ≠ 0) (by decide : Even 1394) hp

theorem nu_p_oneThousandThreeHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1396) p = if p = 2 ∨ p ∣ 1396 then 1 else 2 :=
  nu_p_evenPair (by decide : (1396 : ℕ) ≠ 0) (by decide : Even 1396) hp

theorem nu_p_oneThousandThreeHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1398) p = if p = 2 ∨ p ∣ 1398 then 1 else 2 :=
  nu_p_evenPair (by decide : (1398 : ℕ) ≠ 0) (by decide : Even 1398) hp

theorem nu_p_oneThousandFourHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1400) p = if p = 2 ∨ p ∣ 1400 then 1 else 2 :=
  nu_p_evenPair (by decide : (1400 : ℕ) ≠ 0) (by decide : Even 1400) hp

theorem nu_p_oneThousandThreeHundredNinetyTwo_two : nu_p (evenPair 1392) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1392)

theorem localFactor_oneThousandThreeHundredNinetyTwo_two : localFactor (evenPair 1392) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1392 : ℕ) ≠ 0) (by decide : Even 1392)

theorem nu_p_oneThousandFourHundred_two : nu_p (evenPair 1400) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1400)

theorem localFactor_oneThousandFourHundred_two : localFactor (evenPair 1400) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1400 : ℕ) ≠ 0) (by decide : Even 1400)

end Brockian.SingularSeries.Gaps13921400
