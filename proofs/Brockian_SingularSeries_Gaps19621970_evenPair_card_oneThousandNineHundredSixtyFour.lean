/-
  Brockian/SingularSeriesGaps19621970.lean — even binary gaps n ∈ {1962, 1964, 1966, 1968, 1970}.

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

namespace Brockian.SingularSeries.Gaps19621970

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNineHundredSixtyTwo : (evenPair 1962).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1962 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredSixtyFour : (evenPair 1964).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1964 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredSixtySix : (evenPair 1966).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1966 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredSixtyEight : (evenPair 1968).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1968 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredSeventy : (evenPair 1970).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1970 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNineHundredSixtyTwo : IsAdmissible (evenPair 1962) :=
  isAdmissible_evenPair (by decide : Even 1962)

theorem isAdmissible_evenPair_oneThousandNineHundredSixtyFour : IsAdmissible (evenPair 1964) :=
  isAdmissible_evenPair (by decide : Even 1964)

theorem isAdmissible_evenPair_oneThousandNineHundredSixtySix : IsAdmissible (evenPair 1966) :=
  isAdmissible_evenPair (by decide : Even 1966)

theorem isAdmissible_evenPair_oneThousandNineHundredSixtyEight : IsAdmissible (evenPair 1968) :=
  isAdmissible_evenPair (by decide : Even 1968)

theorem isAdmissible_evenPair_oneThousandNineHundredSeventy : IsAdmissible (evenPair 1970) :=
  isAdmissible_evenPair (by decide : Even 1970)

theorem singular_series_pos_evenPair_oneThousandNineHundredSixtyTwo : 0 < singularSeries (evenPair 1962) :=
  singular_series_pos_evenPair (by decide : Even 1962)

theorem singular_series_pos_evenPair_oneThousandNineHundredSixtyFour : 0 < singularSeries (evenPair 1964) :=
  singular_series_pos_evenPair (by decide : Even 1964)

theorem singular_series_pos_evenPair_oneThousandNineHundredSixtySix : 0 < singularSeries (evenPair 1966) :=
  singular_series_pos_evenPair (by decide : Even 1966)

theorem singular_series_pos_evenPair_oneThousandNineHundredSixtyEight : 0 < singularSeries (evenPair 1968) :=
  singular_series_pos_evenPair (by decide : Even 1968)

theorem singular_series_pos_evenPair_oneThousandNineHundredSeventy : 0 < singularSeries (evenPair 1970) :=
  singular_series_pos_evenPair (by decide : Even 1970)

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1962) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1962) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1964) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1964) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1966) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1966) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1968) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1968) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1970) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1970) P

theorem nu_p_oneThousandNineHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1962) p = if p = 2 ∨ p ∣ 1962 then 1 else 2 :=
  nu_p_evenPair (by decide : (1962 : ℕ) ≠ 0) (by decide : Even 1962) hp

theorem nu_p_oneThousandNineHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1964) p = if p = 2 ∨ p ∣ 1964 then 1 else 2 :=
  nu_p_evenPair (by decide : (1964 : ℕ) ≠ 0) (by decide : Even 1964) hp

theorem nu_p_oneThousandNineHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1966) p = if p = 2 ∨ p ∣ 1966 then 1 else 2 :=
  nu_p_evenPair (by decide : (1966 : ℕ) ≠ 0) (by decide : Even 1966) hp

theorem nu_p_oneThousandNineHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1968) p = if p = 2 ∨ p ∣ 1968 then 1 else 2 :=
  nu_p_evenPair (by decide : (1968 : ℕ) ≠ 0) (by decide : Even 1968) hp

theorem nu_p_oneThousandNineHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1970) p = if p = 2 ∨ p ∣ 1970 then 1 else 2 :=
  nu_p_evenPair (by decide : (1970 : ℕ) ≠ 0) (by decide : Even 1970) hp

theorem nu_p_oneThousandNineHundredSixtyTwo_two : nu_p (evenPair 1962) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1962)

theorem localFactor_oneThousandNineHundredSixtyTwo_two : localFactor (evenPair 1962) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1962 : ℕ) ≠ 0) (by decide : Even 1962)

theorem nu_p_oneThousandNineHundredSeventy_two : nu_p (evenPair 1970) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1970)

theorem localFactor_oneThousandNineHundredSeventy_two : localFactor (evenPair 1970) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1970 : ℕ) ≠ 0) (by decide : Even 1970)

end Brockian.SingularSeries.Gaps19621970
