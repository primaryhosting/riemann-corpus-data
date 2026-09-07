/-
  Brockian/SingularSeriesGaps18821890.lean — even binary gaps n ∈ {1882, 1884, 1886, 1888, 1890}.

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

namespace Brockian.SingularSeries.Gaps18821890

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightHundredEightyTwo : (evenPair 1882).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1882 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredEightyFour : (evenPair 1884).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1884 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredEightySix : (evenPair 1886).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1886 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredEightyEight : (evenPair 1888).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1888 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredNinety : (evenPair 1890).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1890 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightHundredEightyTwo : IsAdmissible (evenPair 1882) :=
  isAdmissible_evenPair (by decide : Even 1882)

theorem isAdmissible_evenPair_oneThousandEightHundredEightyFour : IsAdmissible (evenPair 1884) :=
  isAdmissible_evenPair (by decide : Even 1884)

theorem isAdmissible_evenPair_oneThousandEightHundredEightySix : IsAdmissible (evenPair 1886) :=
  isAdmissible_evenPair (by decide : Even 1886)

theorem isAdmissible_evenPair_oneThousandEightHundredEightyEight : IsAdmissible (evenPair 1888) :=
  isAdmissible_evenPair (by decide : Even 1888)

theorem isAdmissible_evenPair_oneThousandEightHundredNinety : IsAdmissible (evenPair 1890) :=
  isAdmissible_evenPair (by decide : Even 1890)

theorem singular_series_pos_evenPair_oneThousandEightHundredEightyTwo : 0 < singularSeries (evenPair 1882) :=
  singular_series_pos_evenPair (by decide : Even 1882)

theorem singular_series_pos_evenPair_oneThousandEightHundredEightyFour : 0 < singularSeries (evenPair 1884) :=
  singular_series_pos_evenPair (by decide : Even 1884)

theorem singular_series_pos_evenPair_oneThousandEightHundredEightySix : 0 < singularSeries (evenPair 1886) :=
  singular_series_pos_evenPair (by decide : Even 1886)

theorem singular_series_pos_evenPair_oneThousandEightHundredEightyEight : 0 < singularSeries (evenPair 1888) :=
  singular_series_pos_evenPair (by decide : Even 1888)

theorem singular_series_pos_evenPair_oneThousandEightHundredNinety : 0 < singularSeries (evenPair 1890) :=
  singular_series_pos_evenPair (by decide : Even 1890)

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1882) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1882) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1884) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1884) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1886) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1886) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1888) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1888) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1890) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1890) P

theorem nu_p_oneThousandEightHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1882) p = if p = 2 ∨ p ∣ 1882 then 1 else 2 :=
  nu_p_evenPair (by decide : (1882 : ℕ) ≠ 0) (by decide : Even 1882) hp

theorem nu_p_oneThousandEightHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1884) p = if p = 2 ∨ p ∣ 1884 then 1 else 2 :=
  nu_p_evenPair (by decide : (1884 : ℕ) ≠ 0) (by decide : Even 1884) hp

theorem nu_p_oneThousandEightHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1886) p = if p = 2 ∨ p ∣ 1886 then 1 else 2 :=
  nu_p_evenPair (by decide : (1886 : ℕ) ≠ 0) (by decide : Even 1886) hp

theorem nu_p_oneThousandEightHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1888) p = if p = 2 ∨ p ∣ 1888 then 1 else 2 :=
  nu_p_evenPair (by decide : (1888 : ℕ) ≠ 0) (by decide : Even 1888) hp

theorem nu_p_oneThousandEightHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1890) p = if p = 2 ∨ p ∣ 1890 then 1 else 2 :=
  nu_p_evenPair (by decide : (1890 : ℕ) ≠ 0) (by decide : Even 1890) hp

theorem nu_p_oneThousandEightHundredEightyTwo_two : nu_p (evenPair 1882) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1882)

theorem localFactor_oneThousandEightHundredEightyTwo_two : localFactor (evenPair 1882) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1882 : ℕ) ≠ 0) (by decide : Even 1882)

theorem nu_p_oneThousandEightHundredNinety_two : nu_p (evenPair 1890) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1890)

theorem localFactor_oneThousandEightHundredNinety_two : localFactor (evenPair 1890) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1890 : ℕ) ≠ 0) (by decide : Even 1890)

end Brockian.SingularSeries.Gaps18821890
