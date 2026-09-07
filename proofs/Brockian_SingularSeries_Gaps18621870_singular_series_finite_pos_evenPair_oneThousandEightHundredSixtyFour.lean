/-
  Brockian/SingularSeriesGaps18621870.lean — even binary gaps n ∈ {1862, 1864, 1866, 1868, 1870}.

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

namespace Brockian.SingularSeries.Gaps18621870

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightHundredSixtyTwo : (evenPair 1862).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1862 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredSixtyFour : (evenPair 1864).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1864 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredSixtySix : (evenPair 1866).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1866 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredSixtyEight : (evenPair 1868).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1868 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredSeventy : (evenPair 1870).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1870 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightHundredSixtyTwo : IsAdmissible (evenPair 1862) :=
  isAdmissible_evenPair (by decide : Even 1862)

theorem isAdmissible_evenPair_oneThousandEightHundredSixtyFour : IsAdmissible (evenPair 1864) :=
  isAdmissible_evenPair (by decide : Even 1864)

theorem isAdmissible_evenPair_oneThousandEightHundredSixtySix : IsAdmissible (evenPair 1866) :=
  isAdmissible_evenPair (by decide : Even 1866)

theorem isAdmissible_evenPair_oneThousandEightHundredSixtyEight : IsAdmissible (evenPair 1868) :=
  isAdmissible_evenPair (by decide : Even 1868)

theorem isAdmissible_evenPair_oneThousandEightHundredSeventy : IsAdmissible (evenPair 1870) :=
  isAdmissible_evenPair (by decide : Even 1870)

theorem singular_series_pos_evenPair_oneThousandEightHundredSixtyTwo : 0 < singularSeries (evenPair 1862) :=
  singular_series_pos_evenPair (by decide : Even 1862)

theorem singular_series_pos_evenPair_oneThousandEightHundredSixtyFour : 0 < singularSeries (evenPair 1864) :=
  singular_series_pos_evenPair (by decide : Even 1864)

theorem singular_series_pos_evenPair_oneThousandEightHundredSixtySix : 0 < singularSeries (evenPair 1866) :=
  singular_series_pos_evenPair (by decide : Even 1866)

theorem singular_series_pos_evenPair_oneThousandEightHundredSixtyEight : 0 < singularSeries (evenPair 1868) :=
  singular_series_pos_evenPair (by decide : Even 1868)

theorem singular_series_pos_evenPair_oneThousandEightHundredSeventy : 0 < singularSeries (evenPair 1870) :=
  singular_series_pos_evenPair (by decide : Even 1870)

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1862) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1862) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1864) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1864) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1866) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1866) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1868) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1868) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1870) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1870) P

theorem nu_p_oneThousandEightHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1862) p = if p = 2 ∨ p ∣ 1862 then 1 else 2 :=
  nu_p_evenPair (by decide : (1862 : ℕ) ≠ 0) (by decide : Even 1862) hp

theorem nu_p_oneThousandEightHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1864) p = if p = 2 ∨ p ∣ 1864 then 1 else 2 :=
  nu_p_evenPair (by decide : (1864 : ℕ) ≠ 0) (by decide : Even 1864) hp

theorem nu_p_oneThousandEightHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1866) p = if p = 2 ∨ p ∣ 1866 then 1 else 2 :=
  nu_p_evenPair (by decide : (1866 : ℕ) ≠ 0) (by decide : Even 1866) hp

theorem nu_p_oneThousandEightHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1868) p = if p = 2 ∨ p ∣ 1868 then 1 else 2 :=
  nu_p_evenPair (by decide : (1868 : ℕ) ≠ 0) (by decide : Even 1868) hp

theorem nu_p_oneThousandEightHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1870) p = if p = 2 ∨ p ∣ 1870 then 1 else 2 :=
  nu_p_evenPair (by decide : (1870 : ℕ) ≠ 0) (by decide : Even 1870) hp

theorem nu_p_oneThousandEightHundredSixtyTwo_two : nu_p (evenPair 1862) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1862)

theorem localFactor_oneThousandEightHundredSixtyTwo_two : localFactor (evenPair 1862) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1862 : ℕ) ≠ 0) (by decide : Even 1862)

theorem nu_p_oneThousandEightHundredSeventy_two : nu_p (evenPair 1870) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1870)

theorem localFactor_oneThousandEightHundredSeventy_two : localFactor (evenPair 1870) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1870 : ℕ) ≠ 0) (by decide : Even 1870)

end Brockian.SingularSeries.Gaps18621870
