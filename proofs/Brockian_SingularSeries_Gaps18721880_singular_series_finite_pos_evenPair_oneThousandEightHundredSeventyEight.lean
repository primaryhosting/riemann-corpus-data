/-
  Brockian/SingularSeriesGaps18721880.lean — even binary gaps n ∈ {1872, 1874, 1876, 1878, 1880}.

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

namespace Brockian.SingularSeries.Gaps18721880

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightHundredSeventyTwo : (evenPair 1872).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1872 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredSeventyFour : (evenPair 1874).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1874 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredSeventySix : (evenPair 1876).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1876 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredSeventyEight : (evenPair 1878).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1878 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredEighty : (evenPair 1880).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1880 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightHundredSeventyTwo : IsAdmissible (evenPair 1872) :=
  isAdmissible_evenPair (by decide : Even 1872)

theorem isAdmissible_evenPair_oneThousandEightHundredSeventyFour : IsAdmissible (evenPair 1874) :=
  isAdmissible_evenPair (by decide : Even 1874)

theorem isAdmissible_evenPair_oneThousandEightHundredSeventySix : IsAdmissible (evenPair 1876) :=
  isAdmissible_evenPair (by decide : Even 1876)

theorem isAdmissible_evenPair_oneThousandEightHundredSeventyEight : IsAdmissible (evenPair 1878) :=
  isAdmissible_evenPair (by decide : Even 1878)

theorem isAdmissible_evenPair_oneThousandEightHundredEighty : IsAdmissible (evenPair 1880) :=
  isAdmissible_evenPair (by decide : Even 1880)

theorem singular_series_pos_evenPair_oneThousandEightHundredSeventyTwo : 0 < singularSeries (evenPair 1872) :=
  singular_series_pos_evenPair (by decide : Even 1872)

theorem singular_series_pos_evenPair_oneThousandEightHundredSeventyFour : 0 < singularSeries (evenPair 1874) :=
  singular_series_pos_evenPair (by decide : Even 1874)

theorem singular_series_pos_evenPair_oneThousandEightHundredSeventySix : 0 < singularSeries (evenPair 1876) :=
  singular_series_pos_evenPair (by decide : Even 1876)

theorem singular_series_pos_evenPair_oneThousandEightHundredSeventyEight : 0 < singularSeries (evenPair 1878) :=
  singular_series_pos_evenPair (by decide : Even 1878)

theorem singular_series_pos_evenPair_oneThousandEightHundredEighty : 0 < singularSeries (evenPair 1880) :=
  singular_series_pos_evenPair (by decide : Even 1880)

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1872) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1872) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1874) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1874) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1876) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1876) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1878) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1878) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1880) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1880) P

theorem nu_p_oneThousandEightHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1872) p = if p = 2 ∨ p ∣ 1872 then 1 else 2 :=
  nu_p_evenPair (by decide : (1872 : ℕ) ≠ 0) (by decide : Even 1872) hp

theorem nu_p_oneThousandEightHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1874) p = if p = 2 ∨ p ∣ 1874 then 1 else 2 :=
  nu_p_evenPair (by decide : (1874 : ℕ) ≠ 0) (by decide : Even 1874) hp

theorem nu_p_oneThousandEightHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1876) p = if p = 2 ∨ p ∣ 1876 then 1 else 2 :=
  nu_p_evenPair (by decide : (1876 : ℕ) ≠ 0) (by decide : Even 1876) hp

theorem nu_p_oneThousandEightHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1878) p = if p = 2 ∨ p ∣ 1878 then 1 else 2 :=
  nu_p_evenPair (by decide : (1878 : ℕ) ≠ 0) (by decide : Even 1878) hp

theorem nu_p_oneThousandEightHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1880) p = if p = 2 ∨ p ∣ 1880 then 1 else 2 :=
  nu_p_evenPair (by decide : (1880 : ℕ) ≠ 0) (by decide : Even 1880) hp

theorem nu_p_oneThousandEightHundredSeventyTwo_two : nu_p (evenPair 1872) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1872)

theorem localFactor_oneThousandEightHundredSeventyTwo_two : localFactor (evenPair 1872) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1872 : ℕ) ≠ 0) (by decide : Even 1872)

theorem nu_p_oneThousandEightHundredEighty_two : nu_p (evenPair 1880) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1880)

theorem localFactor_oneThousandEightHundredEighty_two : localFactor (evenPair 1880) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1880 : ℕ) ≠ 0) (by decide : Even 1880)

end Brockian.SingularSeries.Gaps18721880
