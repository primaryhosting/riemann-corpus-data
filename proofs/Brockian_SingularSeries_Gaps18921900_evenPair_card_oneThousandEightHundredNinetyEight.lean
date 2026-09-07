/-
  Brockian/SingularSeriesGaps18921900.lean — even binary gaps n ∈ {1892, 1894, 1896, 1898, 1900}.

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

namespace Brockian.SingularSeries.Gaps18921900

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightHundredNinetyTwo : (evenPair 1892).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1892 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredNinetyFour : (evenPair 1894).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1894 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredNinetySix : (evenPair 1896).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1896 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredNinetyEight : (evenPair 1898).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1898 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundred : (evenPair 1900).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1900 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightHundredNinetyTwo : IsAdmissible (evenPair 1892) :=
  isAdmissible_evenPair (by decide : Even 1892)

theorem isAdmissible_evenPair_oneThousandEightHundredNinetyFour : IsAdmissible (evenPair 1894) :=
  isAdmissible_evenPair (by decide : Even 1894)

theorem isAdmissible_evenPair_oneThousandEightHundredNinetySix : IsAdmissible (evenPair 1896) :=
  isAdmissible_evenPair (by decide : Even 1896)

theorem isAdmissible_evenPair_oneThousandEightHundredNinetyEight : IsAdmissible (evenPair 1898) :=
  isAdmissible_evenPair (by decide : Even 1898)

theorem isAdmissible_evenPair_oneThousandNineHundred : IsAdmissible (evenPair 1900) :=
  isAdmissible_evenPair (by decide : Even 1900)

theorem singular_series_pos_evenPair_oneThousandEightHundredNinetyTwo : 0 < singularSeries (evenPair 1892) :=
  singular_series_pos_evenPair (by decide : Even 1892)

theorem singular_series_pos_evenPair_oneThousandEightHundredNinetyFour : 0 < singularSeries (evenPair 1894) :=
  singular_series_pos_evenPair (by decide : Even 1894)

theorem singular_series_pos_evenPair_oneThousandEightHundredNinetySix : 0 < singularSeries (evenPair 1896) :=
  singular_series_pos_evenPair (by decide : Even 1896)

theorem singular_series_pos_evenPair_oneThousandEightHundredNinetyEight : 0 < singularSeries (evenPair 1898) :=
  singular_series_pos_evenPair (by decide : Even 1898)

theorem singular_series_pos_evenPair_oneThousandNineHundred : 0 < singularSeries (evenPair 1900) :=
  singular_series_pos_evenPair (by decide : Even 1900)

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1892) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1892) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1894) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1894) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1896) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1896) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1898) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1898) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1900) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1900) P

theorem nu_p_oneThousandEightHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1892) p = if p = 2 ∨ p ∣ 1892 then 1 else 2 :=
  nu_p_evenPair (by decide : (1892 : ℕ) ≠ 0) (by decide : Even 1892) hp

theorem nu_p_oneThousandEightHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1894) p = if p = 2 ∨ p ∣ 1894 then 1 else 2 :=
  nu_p_evenPair (by decide : (1894 : ℕ) ≠ 0) (by decide : Even 1894) hp

theorem nu_p_oneThousandEightHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1896) p = if p = 2 ∨ p ∣ 1896 then 1 else 2 :=
  nu_p_evenPair (by decide : (1896 : ℕ) ≠ 0) (by decide : Even 1896) hp

theorem nu_p_oneThousandEightHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1898) p = if p = 2 ∨ p ∣ 1898 then 1 else 2 :=
  nu_p_evenPair (by decide : (1898 : ℕ) ≠ 0) (by decide : Even 1898) hp

theorem nu_p_oneThousandNineHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1900) p = if p = 2 ∨ p ∣ 1900 then 1 else 2 :=
  nu_p_evenPair (by decide : (1900 : ℕ) ≠ 0) (by decide : Even 1900) hp

theorem nu_p_oneThousandEightHundredNinetyTwo_two : nu_p (evenPair 1892) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1892)

theorem localFactor_oneThousandEightHundredNinetyTwo_two : localFactor (evenPair 1892) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1892 : ℕ) ≠ 0) (by decide : Even 1892)

theorem nu_p_oneThousandNineHundred_two : nu_p (evenPair 1900) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1900)

theorem localFactor_oneThousandNineHundred_two : localFactor (evenPair 1900) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1900 : ℕ) ≠ 0) (by decide : Even 1900)

end Brockian.SingularSeries.Gaps18921900
