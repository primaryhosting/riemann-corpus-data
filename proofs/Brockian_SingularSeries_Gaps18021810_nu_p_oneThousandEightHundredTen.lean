/-
  Brockian/SingularSeriesGaps18021810.lean — even binary gaps n ∈ {1802, 1804, 1806, 1808, 1810}.

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

namespace Brockian.SingularSeries.Gaps18021810

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightHundredTwo : (evenPair 1802).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1802 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredFour : (evenPair 1804).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1804 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredSix : (evenPair 1806).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1806 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredEight : (evenPair 1808).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1808 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredTen : (evenPair 1810).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1810 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightHundredTwo : IsAdmissible (evenPair 1802) :=
  isAdmissible_evenPair (by decide : Even 1802)

theorem isAdmissible_evenPair_oneThousandEightHundredFour : IsAdmissible (evenPair 1804) :=
  isAdmissible_evenPair (by decide : Even 1804)

theorem isAdmissible_evenPair_oneThousandEightHundredSix : IsAdmissible (evenPair 1806) :=
  isAdmissible_evenPair (by decide : Even 1806)

theorem isAdmissible_evenPair_oneThousandEightHundredEight : IsAdmissible (evenPair 1808) :=
  isAdmissible_evenPair (by decide : Even 1808)

theorem isAdmissible_evenPair_oneThousandEightHundredTen : IsAdmissible (evenPair 1810) :=
  isAdmissible_evenPair (by decide : Even 1810)

theorem singular_series_pos_evenPair_oneThousandEightHundredTwo : 0 < singularSeries (evenPair 1802) :=
  singular_series_pos_evenPair (by decide : Even 1802)

theorem singular_series_pos_evenPair_oneThousandEightHundredFour : 0 < singularSeries (evenPair 1804) :=
  singular_series_pos_evenPair (by decide : Even 1804)

theorem singular_series_pos_evenPair_oneThousandEightHundredSix : 0 < singularSeries (evenPair 1806) :=
  singular_series_pos_evenPair (by decide : Even 1806)

theorem singular_series_pos_evenPair_oneThousandEightHundredEight : 0 < singularSeries (evenPair 1808) :=
  singular_series_pos_evenPair (by decide : Even 1808)

theorem singular_series_pos_evenPair_oneThousandEightHundredTen : 0 < singularSeries (evenPair 1810) :=
  singular_series_pos_evenPair (by decide : Even 1810)

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1802) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1802) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1804) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1804) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1806) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1806) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1808) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1808) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1810) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1810) P

theorem nu_p_oneThousandEightHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1802) p = if p = 2 ∨ p ∣ 1802 then 1 else 2 :=
  nu_p_evenPair (by decide : (1802 : ℕ) ≠ 0) (by decide : Even 1802) hp

theorem nu_p_oneThousandEightHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1804) p = if p = 2 ∨ p ∣ 1804 then 1 else 2 :=
  nu_p_evenPair (by decide : (1804 : ℕ) ≠ 0) (by decide : Even 1804) hp

theorem nu_p_oneThousandEightHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1806) p = if p = 2 ∨ p ∣ 1806 then 1 else 2 :=
  nu_p_evenPair (by decide : (1806 : ℕ) ≠ 0) (by decide : Even 1806) hp

theorem nu_p_oneThousandEightHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1808) p = if p = 2 ∨ p ∣ 1808 then 1 else 2 :=
  nu_p_evenPair (by decide : (1808 : ℕ) ≠ 0) (by decide : Even 1808) hp

theorem nu_p_oneThousandEightHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1810) p = if p = 2 ∨ p ∣ 1810 then 1 else 2 :=
  nu_p_evenPair (by decide : (1810 : ℕ) ≠ 0) (by decide : Even 1810) hp

theorem nu_p_oneThousandEightHundredTwo_two : nu_p (evenPair 1802) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1802)

theorem localFactor_oneThousandEightHundredTwo_two : localFactor (evenPair 1802) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1802 : ℕ) ≠ 0) (by decide : Even 1802)

theorem nu_p_oneThousandEightHundredTen_two : nu_p (evenPair 1810) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1810)

theorem localFactor_oneThousandEightHundredTen_two : localFactor (evenPair 1810) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1810 : ℕ) ≠ 0) (by decide : Even 1810)

end Brockian.SingularSeries.Gaps18021810
