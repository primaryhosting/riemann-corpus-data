/-
  Brockian/SingularSeriesGaps21022110.lean — even binary gaps n ∈ {2102, 2104, 2106, 2108, 2110}.

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

namespace Brockian.SingularSeries.Gaps21022110

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandOneHundredTwo : (evenPair 2102).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2102 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredFour : (evenPair 2104).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2104 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredSix : (evenPair 2106).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2106 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredEight : (evenPair 2108).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2108 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredTen : (evenPair 2110).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2110 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandOneHundredTwo : IsAdmissible (evenPair 2102) :=
  isAdmissible_evenPair (by decide : Even 2102)

theorem isAdmissible_evenPair_twoThousandOneHundredFour : IsAdmissible (evenPair 2104) :=
  isAdmissible_evenPair (by decide : Even 2104)

theorem isAdmissible_evenPair_twoThousandOneHundredSix : IsAdmissible (evenPair 2106) :=
  isAdmissible_evenPair (by decide : Even 2106)

theorem isAdmissible_evenPair_twoThousandOneHundredEight : IsAdmissible (evenPair 2108) :=
  isAdmissible_evenPair (by decide : Even 2108)

theorem isAdmissible_evenPair_twoThousandOneHundredTen : IsAdmissible (evenPair 2110) :=
  isAdmissible_evenPair (by decide : Even 2110)

theorem singular_series_pos_evenPair_twoThousandOneHundredTwo : 0 < singularSeries (evenPair 2102) :=
  singular_series_pos_evenPair (by decide : Even 2102)

theorem singular_series_pos_evenPair_twoThousandOneHundredFour : 0 < singularSeries (evenPair 2104) :=
  singular_series_pos_evenPair (by decide : Even 2104)

theorem singular_series_pos_evenPair_twoThousandOneHundredSix : 0 < singularSeries (evenPair 2106) :=
  singular_series_pos_evenPair (by decide : Even 2106)

theorem singular_series_pos_evenPair_twoThousandOneHundredEight : 0 < singularSeries (evenPair 2108) :=
  singular_series_pos_evenPair (by decide : Even 2108)

theorem singular_series_pos_evenPair_twoThousandOneHundredTen : 0 < singularSeries (evenPair 2110) :=
  singular_series_pos_evenPair (by decide : Even 2110)

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2102) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2102) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2104) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2104) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2106) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2106) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2108) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2108) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2110) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2110) P

theorem nu_p_twoThousandOneHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2102) p = if p = 2 ∨ p ∣ 2102 then 1 else 2 :=
  nu_p_evenPair (by decide : (2102 : ℕ) ≠ 0) (by decide : Even 2102) hp

theorem nu_p_twoThousandOneHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2104) p = if p = 2 ∨ p ∣ 2104 then 1 else 2 :=
  nu_p_evenPair (by decide : (2104 : ℕ) ≠ 0) (by decide : Even 2104) hp

theorem nu_p_twoThousandOneHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2106) p = if p = 2 ∨ p ∣ 2106 then 1 else 2 :=
  nu_p_evenPair (by decide : (2106 : ℕ) ≠ 0) (by decide : Even 2106) hp

theorem nu_p_twoThousandOneHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2108) p = if p = 2 ∨ p ∣ 2108 then 1 else 2 :=
  nu_p_evenPair (by decide : (2108 : ℕ) ≠ 0) (by decide : Even 2108) hp

theorem nu_p_twoThousandOneHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2110) p = if p = 2 ∨ p ∣ 2110 then 1 else 2 :=
  nu_p_evenPair (by decide : (2110 : ℕ) ≠ 0) (by decide : Even 2110) hp

theorem nu_p_twoThousandOneHundredTwo_two : nu_p (evenPair 2102) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2102)

theorem localFactor_twoThousandOneHundredTwo_two : localFactor (evenPair 2102) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2102 : ℕ) ≠ 0) (by decide : Even 2102)

theorem nu_p_twoThousandOneHundredTen_two : nu_p (evenPair 2110) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2110)

theorem localFactor_twoThousandOneHundredTen_two : localFactor (evenPair 2110) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2110 : ℕ) ≠ 0) (by decide : Even 2110)

end Brockian.SingularSeries.Gaps21022110
