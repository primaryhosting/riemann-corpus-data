/-
  Brockian/SingularSeriesGaps11021110.lean — even binary gaps n ∈ {1102, 1104, 1106, 1108, 1110}.

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

namespace Brockian.SingularSeries.Gaps11021110

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandOneHundredTwo : (evenPair 1102).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1102 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredFour : (evenPair 1104).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1104 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredSix : (evenPair 1106).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1106 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredEight : (evenPair 1108).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1108 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredTen : (evenPair 1110).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1110 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandOneHundredTwo : IsAdmissible (evenPair 1102) :=
  isAdmissible_evenPair (by decide : Even 1102)

theorem isAdmissible_evenPair_oneThousandOneHundredFour : IsAdmissible (evenPair 1104) :=
  isAdmissible_evenPair (by decide : Even 1104)

theorem isAdmissible_evenPair_oneThousandOneHundredSix : IsAdmissible (evenPair 1106) :=
  isAdmissible_evenPair (by decide : Even 1106)

theorem isAdmissible_evenPair_oneThousandOneHundredEight : IsAdmissible (evenPair 1108) :=
  isAdmissible_evenPair (by decide : Even 1108)

theorem isAdmissible_evenPair_oneThousandOneHundredTen : IsAdmissible (evenPair 1110) :=
  isAdmissible_evenPair (by decide : Even 1110)

theorem singular_series_pos_evenPair_oneThousandOneHundredTwo : 0 < singularSeries (evenPair 1102) :=
  singular_series_pos_evenPair (by decide : Even 1102)

theorem singular_series_pos_evenPair_oneThousandOneHundredFour : 0 < singularSeries (evenPair 1104) :=
  singular_series_pos_evenPair (by decide : Even 1104)

theorem singular_series_pos_evenPair_oneThousandOneHundredSix : 0 < singularSeries (evenPair 1106) :=
  singular_series_pos_evenPair (by decide : Even 1106)

theorem singular_series_pos_evenPair_oneThousandOneHundredEight : 0 < singularSeries (evenPair 1108) :=
  singular_series_pos_evenPair (by decide : Even 1108)

theorem singular_series_pos_evenPair_oneThousandOneHundredTen : 0 < singularSeries (evenPair 1110) :=
  singular_series_pos_evenPair (by decide : Even 1110)

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1102) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1102) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1104) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1104) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1106) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1106) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1108) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1108) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1110) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1110) P

theorem nu_p_oneThousandOneHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1102) p = if p = 2 ∨ p ∣ 1102 then 1 else 2 :=
  nu_p_evenPair (by decide : (1102 : ℕ) ≠ 0) (by decide : Even 1102) hp

theorem nu_p_oneThousandOneHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1104) p = if p = 2 ∨ p ∣ 1104 then 1 else 2 :=
  nu_p_evenPair (by decide : (1104 : ℕ) ≠ 0) (by decide : Even 1104) hp

theorem nu_p_oneThousandOneHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1106) p = if p = 2 ∨ p ∣ 1106 then 1 else 2 :=
  nu_p_evenPair (by decide : (1106 : ℕ) ≠ 0) (by decide : Even 1106) hp

theorem nu_p_oneThousandOneHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1108) p = if p = 2 ∨ p ∣ 1108 then 1 else 2 :=
  nu_p_evenPair (by decide : (1108 : ℕ) ≠ 0) (by decide : Even 1108) hp

theorem nu_p_oneThousandOneHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1110) p = if p = 2 ∨ p ∣ 1110 then 1 else 2 :=
  nu_p_evenPair (by decide : (1110 : ℕ) ≠ 0) (by decide : Even 1110) hp

theorem nu_p_oneThousandOneHundredTwo_two : nu_p (evenPair 1102) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1102)

theorem localFactor_oneThousandOneHundredTwo_two : localFactor (evenPair 1102) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1102 : ℕ) ≠ 0) (by decide : Even 1102)

theorem nu_p_oneThousandOneHundredTen_two : nu_p (evenPair 1110) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1110)

theorem localFactor_oneThousandOneHundredTen_two : localFactor (evenPair 1110) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1110 : ℕ) ≠ 0) (by decide : Even 1110)

end Brockian.SingularSeries.Gaps11021110
