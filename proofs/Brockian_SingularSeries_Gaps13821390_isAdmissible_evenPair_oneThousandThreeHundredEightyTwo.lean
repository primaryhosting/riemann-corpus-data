/-
  Brockian/SingularSeriesGaps13821390.lean — even binary gaps n ∈ {1382, 1384, 1386, 1388, 1390}.

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

namespace Brockian.SingularSeries.Gaps13821390

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThreeHundredEightyTwo : (evenPair 1382).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1382 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredEightyFour : (evenPair 1384).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1384 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredEightySix : (evenPair 1386).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1386 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredEightyEight : (evenPair 1388).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1388 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredNinety : (evenPair 1390).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1390 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThreeHundredEightyTwo : IsAdmissible (evenPair 1382) :=
  isAdmissible_evenPair (by decide : Even 1382)

theorem isAdmissible_evenPair_oneThousandThreeHundredEightyFour : IsAdmissible (evenPair 1384) :=
  isAdmissible_evenPair (by decide : Even 1384)

theorem isAdmissible_evenPair_oneThousandThreeHundredEightySix : IsAdmissible (evenPair 1386) :=
  isAdmissible_evenPair (by decide : Even 1386)

theorem isAdmissible_evenPair_oneThousandThreeHundredEightyEight : IsAdmissible (evenPair 1388) :=
  isAdmissible_evenPair (by decide : Even 1388)

theorem isAdmissible_evenPair_oneThousandThreeHundredNinety : IsAdmissible (evenPair 1390) :=
  isAdmissible_evenPair (by decide : Even 1390)

theorem singular_series_pos_evenPair_oneThousandThreeHundredEightyTwo : 0 < singularSeries (evenPair 1382) :=
  singular_series_pos_evenPair (by decide : Even 1382)

theorem singular_series_pos_evenPair_oneThousandThreeHundredEightyFour : 0 < singularSeries (evenPair 1384) :=
  singular_series_pos_evenPair (by decide : Even 1384)

theorem singular_series_pos_evenPair_oneThousandThreeHundredEightySix : 0 < singularSeries (evenPair 1386) :=
  singular_series_pos_evenPair (by decide : Even 1386)

theorem singular_series_pos_evenPair_oneThousandThreeHundredEightyEight : 0 < singularSeries (evenPair 1388) :=
  singular_series_pos_evenPair (by decide : Even 1388)

theorem singular_series_pos_evenPair_oneThousandThreeHundredNinety : 0 < singularSeries (evenPair 1390) :=
  singular_series_pos_evenPair (by decide : Even 1390)

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1382) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1382) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1384) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1384) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1386) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1386) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1388) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1388) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1390) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1390) P

theorem nu_p_oneThousandThreeHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1382) p = if p = 2 ∨ p ∣ 1382 then 1 else 2 :=
  nu_p_evenPair (by decide : (1382 : ℕ) ≠ 0) (by decide : Even 1382) hp

theorem nu_p_oneThousandThreeHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1384) p = if p = 2 ∨ p ∣ 1384 then 1 else 2 :=
  nu_p_evenPair (by decide : (1384 : ℕ) ≠ 0) (by decide : Even 1384) hp

theorem nu_p_oneThousandThreeHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1386) p = if p = 2 ∨ p ∣ 1386 then 1 else 2 :=
  nu_p_evenPair (by decide : (1386 : ℕ) ≠ 0) (by decide : Even 1386) hp

theorem nu_p_oneThousandThreeHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1388) p = if p = 2 ∨ p ∣ 1388 then 1 else 2 :=
  nu_p_evenPair (by decide : (1388 : ℕ) ≠ 0) (by decide : Even 1388) hp

theorem nu_p_oneThousandThreeHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1390) p = if p = 2 ∨ p ∣ 1390 then 1 else 2 :=
  nu_p_evenPair (by decide : (1390 : ℕ) ≠ 0) (by decide : Even 1390) hp

theorem nu_p_oneThousandThreeHundredEightyTwo_two : nu_p (evenPair 1382) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1382)

theorem localFactor_oneThousandThreeHundredEightyTwo_two : localFactor (evenPair 1382) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1382 : ℕ) ≠ 0) (by decide : Even 1382)

theorem nu_p_oneThousandThreeHundredNinety_two : nu_p (evenPair 1390) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1390)

theorem localFactor_oneThousandThreeHundredNinety_two : localFactor (evenPair 1390) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1390 : ℕ) ≠ 0) (by decide : Even 1390)

end Brockian.SingularSeries.Gaps13821390
