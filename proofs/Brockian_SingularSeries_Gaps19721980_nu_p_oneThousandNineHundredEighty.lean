/-
  Brockian/SingularSeriesGaps19721980.lean — even binary gaps n ∈ {1972, 1974, 1976, 1978, 1980}.

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

namespace Brockian.SingularSeries.Gaps19721980

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNineHundredSeventyTwo : (evenPair 1972).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1972 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredSeventyFour : (evenPair 1974).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1974 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredSeventySix : (evenPair 1976).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1976 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredSeventyEight : (evenPair 1978).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1978 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredEighty : (evenPair 1980).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1980 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNineHundredSeventyTwo : IsAdmissible (evenPair 1972) :=
  isAdmissible_evenPair (by decide : Even 1972)

theorem isAdmissible_evenPair_oneThousandNineHundredSeventyFour : IsAdmissible (evenPair 1974) :=
  isAdmissible_evenPair (by decide : Even 1974)

theorem isAdmissible_evenPair_oneThousandNineHundredSeventySix : IsAdmissible (evenPair 1976) :=
  isAdmissible_evenPair (by decide : Even 1976)

theorem isAdmissible_evenPair_oneThousandNineHundredSeventyEight : IsAdmissible (evenPair 1978) :=
  isAdmissible_evenPair (by decide : Even 1978)

theorem isAdmissible_evenPair_oneThousandNineHundredEighty : IsAdmissible (evenPair 1980) :=
  isAdmissible_evenPair (by decide : Even 1980)

theorem singular_series_pos_evenPair_oneThousandNineHundredSeventyTwo : 0 < singularSeries (evenPair 1972) :=
  singular_series_pos_evenPair (by decide : Even 1972)

theorem singular_series_pos_evenPair_oneThousandNineHundredSeventyFour : 0 < singularSeries (evenPair 1974) :=
  singular_series_pos_evenPair (by decide : Even 1974)

theorem singular_series_pos_evenPair_oneThousandNineHundredSeventySix : 0 < singularSeries (evenPair 1976) :=
  singular_series_pos_evenPair (by decide : Even 1976)

theorem singular_series_pos_evenPair_oneThousandNineHundredSeventyEight : 0 < singularSeries (evenPair 1978) :=
  singular_series_pos_evenPair (by decide : Even 1978)

theorem singular_series_pos_evenPair_oneThousandNineHundredEighty : 0 < singularSeries (evenPair 1980) :=
  singular_series_pos_evenPair (by decide : Even 1980)

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1972) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1972) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1974) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1974) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1976) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1976) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1978) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1978) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1980) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1980) P

theorem nu_p_oneThousandNineHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1972) p = if p = 2 ∨ p ∣ 1972 then 1 else 2 :=
  nu_p_evenPair (by decide : (1972 : ℕ) ≠ 0) (by decide : Even 1972) hp

theorem nu_p_oneThousandNineHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1974) p = if p = 2 ∨ p ∣ 1974 then 1 else 2 :=
  nu_p_evenPair (by decide : (1974 : ℕ) ≠ 0) (by decide : Even 1974) hp

theorem nu_p_oneThousandNineHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1976) p = if p = 2 ∨ p ∣ 1976 then 1 else 2 :=
  nu_p_evenPair (by decide : (1976 : ℕ) ≠ 0) (by decide : Even 1976) hp

theorem nu_p_oneThousandNineHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1978) p = if p = 2 ∨ p ∣ 1978 then 1 else 2 :=
  nu_p_evenPair (by decide : (1978 : ℕ) ≠ 0) (by decide : Even 1978) hp

theorem nu_p_oneThousandNineHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1980) p = if p = 2 ∨ p ∣ 1980 then 1 else 2 :=
  nu_p_evenPair (by decide : (1980 : ℕ) ≠ 0) (by decide : Even 1980) hp

theorem nu_p_oneThousandNineHundredSeventyTwo_two : nu_p (evenPair 1972) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1972)

theorem localFactor_oneThousandNineHundredSeventyTwo_two : localFactor (evenPair 1972) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1972 : ℕ) ≠ 0) (by decide : Even 1972)

theorem nu_p_oneThousandNineHundredEighty_two : nu_p (evenPair 1980) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1980)

theorem localFactor_oneThousandNineHundredEighty_two : localFactor (evenPair 1980) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1980 : ℕ) ≠ 0) (by decide : Even 1980)

end Brockian.SingularSeries.Gaps19721980
