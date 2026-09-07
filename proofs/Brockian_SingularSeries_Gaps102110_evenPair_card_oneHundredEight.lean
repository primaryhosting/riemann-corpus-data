/-
  Brockian/SingularSeriesGaps102110.lean — even binary gaps n ∈ {102, 104, 106, 108, 110}.

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

namespace Brockian.SingularSeries.Gaps102110

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneHundredTwo : (evenPair 102).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (102 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredFour : (evenPair 104).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (104 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredSix : (evenPair 106).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (106 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredEight : (evenPair 108).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (108 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredTen : (evenPair 110).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (110 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneHundredTwo : IsAdmissible (evenPair 102) :=
  isAdmissible_evenPair (by decide : Even 102)

theorem isAdmissible_evenPair_oneHundredFour : IsAdmissible (evenPair 104) :=
  isAdmissible_evenPair (by decide : Even 104)

theorem isAdmissible_evenPair_oneHundredSix : IsAdmissible (evenPair 106) :=
  isAdmissible_evenPair (by decide : Even 106)

theorem isAdmissible_evenPair_oneHundredEight : IsAdmissible (evenPair 108) :=
  isAdmissible_evenPair (by decide : Even 108)

theorem isAdmissible_evenPair_oneHundredTen : IsAdmissible (evenPair 110) :=
  isAdmissible_evenPair (by decide : Even 110)

theorem singular_series_pos_evenPair_oneHundredTwo : 0 < singularSeries (evenPair 102) :=
  singular_series_pos_evenPair (by decide : Even 102)

theorem singular_series_pos_evenPair_oneHundredFour : 0 < singularSeries (evenPair 104) :=
  singular_series_pos_evenPair (by decide : Even 104)

theorem singular_series_pos_evenPair_oneHundredSix : 0 < singularSeries (evenPair 106) :=
  singular_series_pos_evenPair (by decide : Even 106)

theorem singular_series_pos_evenPair_oneHundredEight : 0 < singularSeries (evenPair 108) :=
  singular_series_pos_evenPair (by decide : Even 108)

theorem singular_series_pos_evenPair_oneHundredTen : 0 < singularSeries (evenPair 110) :=
  singular_series_pos_evenPair (by decide : Even 110)

theorem singular_series_finite_pos_evenPair_oneHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 102) P :=
  singular_series_finite_pos_evenPair (by decide : Even 102) P

theorem singular_series_finite_pos_evenPair_oneHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 104) P :=
  singular_series_finite_pos_evenPair (by decide : Even 104) P

theorem singular_series_finite_pos_evenPair_oneHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 106) P :=
  singular_series_finite_pos_evenPair (by decide : Even 106) P

theorem singular_series_finite_pos_evenPair_oneHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 108) P :=
  singular_series_finite_pos_evenPair (by decide : Even 108) P

theorem singular_series_finite_pos_evenPair_oneHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 110) P :=
  singular_series_finite_pos_evenPair (by decide : Even 110) P

theorem nu_p_oneHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 102) p = if p = 2 ∨ p ∣ 102 then 1 else 2 :=
  nu_p_evenPair (by decide : (102 : ℕ) ≠ 0) (by decide : Even 102) hp

theorem nu_p_oneHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 104) p = if p = 2 ∨ p ∣ 104 then 1 else 2 :=
  nu_p_evenPair (by decide : (104 : ℕ) ≠ 0) (by decide : Even 104) hp

theorem nu_p_oneHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 106) p = if p = 2 ∨ p ∣ 106 then 1 else 2 :=
  nu_p_evenPair (by decide : (106 : ℕ) ≠ 0) (by decide : Even 106) hp

theorem nu_p_oneHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 108) p = if p = 2 ∨ p ∣ 108 then 1 else 2 :=
  nu_p_evenPair (by decide : (108 : ℕ) ≠ 0) (by decide : Even 108) hp

theorem nu_p_oneHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 110) p = if p = 2 ∨ p ∣ 110 then 1 else 2 :=
  nu_p_evenPair (by decide : (110 : ℕ) ≠ 0) (by decide : Even 110) hp

theorem nu_p_oneHundredTwo_two : nu_p (evenPair 102) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 102)

theorem localFactor_oneHundredTwo_two : localFactor (evenPair 102) 2 = 2 :=
  localFactor_evenPair_two (by decide : (102 : ℕ) ≠ 0) (by decide : Even 102)

theorem nu_p_oneHundredTen_two : nu_p (evenPair 110) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 110)

theorem localFactor_oneHundredTen_two : localFactor (evenPair 110) 2 = 2 :=
  localFactor_evenPair_two (by decide : (110 : ℕ) ≠ 0) (by decide : Even 110)

end Brockian.SingularSeries.Gaps102110
