/-
  Brockian/SingularSeriesGaps19421950.lean — even binary gaps n ∈ {1942, 1944, 1946, 1948, 1950}.

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

namespace Brockian.SingularSeries.Gaps19421950

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNineHundredFortyTwo : (evenPair 1942).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1942 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredFortyFour : (evenPair 1944).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1944 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredFortySix : (evenPair 1946).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1946 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredFortyEight : (evenPair 1948).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1948 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredFifty : (evenPair 1950).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1950 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNineHundredFortyTwo : IsAdmissible (evenPair 1942) :=
  isAdmissible_evenPair (by decide : Even 1942)

theorem isAdmissible_evenPair_oneThousandNineHundredFortyFour : IsAdmissible (evenPair 1944) :=
  isAdmissible_evenPair (by decide : Even 1944)

theorem isAdmissible_evenPair_oneThousandNineHundredFortySix : IsAdmissible (evenPair 1946) :=
  isAdmissible_evenPair (by decide : Even 1946)

theorem isAdmissible_evenPair_oneThousandNineHundredFortyEight : IsAdmissible (evenPair 1948) :=
  isAdmissible_evenPair (by decide : Even 1948)

theorem isAdmissible_evenPair_oneThousandNineHundredFifty : IsAdmissible (evenPair 1950) :=
  isAdmissible_evenPair (by decide : Even 1950)

theorem singular_series_pos_evenPair_oneThousandNineHundredFortyTwo : 0 < singularSeries (evenPair 1942) :=
  singular_series_pos_evenPair (by decide : Even 1942)

theorem singular_series_pos_evenPair_oneThousandNineHundredFortyFour : 0 < singularSeries (evenPair 1944) :=
  singular_series_pos_evenPair (by decide : Even 1944)

theorem singular_series_pos_evenPair_oneThousandNineHundredFortySix : 0 < singularSeries (evenPair 1946) :=
  singular_series_pos_evenPair (by decide : Even 1946)

theorem singular_series_pos_evenPair_oneThousandNineHundredFortyEight : 0 < singularSeries (evenPair 1948) :=
  singular_series_pos_evenPair (by decide : Even 1948)

theorem singular_series_pos_evenPair_oneThousandNineHundredFifty : 0 < singularSeries (evenPair 1950) :=
  singular_series_pos_evenPair (by decide : Even 1950)

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1942) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1942) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1944) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1944) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1946) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1946) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1948) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1948) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1950) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1950) P

theorem nu_p_oneThousandNineHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1942) p = if p = 2 ∨ p ∣ 1942 then 1 else 2 :=
  nu_p_evenPair (by decide : (1942 : ℕ) ≠ 0) (by decide : Even 1942) hp

theorem nu_p_oneThousandNineHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1944) p = if p = 2 ∨ p ∣ 1944 then 1 else 2 :=
  nu_p_evenPair (by decide : (1944 : ℕ) ≠ 0) (by decide : Even 1944) hp

theorem nu_p_oneThousandNineHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1946) p = if p = 2 ∨ p ∣ 1946 then 1 else 2 :=
  nu_p_evenPair (by decide : (1946 : ℕ) ≠ 0) (by decide : Even 1946) hp

theorem nu_p_oneThousandNineHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1948) p = if p = 2 ∨ p ∣ 1948 then 1 else 2 :=
  nu_p_evenPair (by decide : (1948 : ℕ) ≠ 0) (by decide : Even 1948) hp

theorem nu_p_oneThousandNineHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1950) p = if p = 2 ∨ p ∣ 1950 then 1 else 2 :=
  nu_p_evenPair (by decide : (1950 : ℕ) ≠ 0) (by decide : Even 1950) hp

theorem nu_p_oneThousandNineHundredFortyTwo_two : nu_p (evenPair 1942) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1942)

theorem localFactor_oneThousandNineHundredFortyTwo_two : localFactor (evenPair 1942) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1942 : ℕ) ≠ 0) (by decide : Even 1942)

theorem nu_p_oneThousandNineHundredFifty_two : nu_p (evenPair 1950) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1950)

theorem localFactor_oneThousandNineHundredFifty_two : localFactor (evenPair 1950) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1950 : ℕ) ≠ 0) (by decide : Even 1950)

end Brockian.SingularSeries.Gaps19421950
