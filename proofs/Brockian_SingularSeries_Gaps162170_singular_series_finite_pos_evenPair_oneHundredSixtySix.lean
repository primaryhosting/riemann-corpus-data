/-
  Brockian/SingularSeriesGaps162170.lean — even binary gaps n ∈ {162, 164, 166, 168, 170}.

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

namespace Brockian.SingularSeries.Gaps162170

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneHundredSixtyTwo : (evenPair 162).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (162 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredSixtyFour : (evenPair 164).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (164 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredSixtySix : (evenPair 166).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (166 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredSixtyEight : (evenPair 168).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (168 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredSeventy : (evenPair 170).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (170 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneHundredSixtyTwo : IsAdmissible (evenPair 162) :=
  isAdmissible_evenPair (by decide : Even 162)

theorem isAdmissible_evenPair_oneHundredSixtyFour : IsAdmissible (evenPair 164) :=
  isAdmissible_evenPair (by decide : Even 164)

theorem isAdmissible_evenPair_oneHundredSixtySix : IsAdmissible (evenPair 166) :=
  isAdmissible_evenPair (by decide : Even 166)

theorem isAdmissible_evenPair_oneHundredSixtyEight : IsAdmissible (evenPair 168) :=
  isAdmissible_evenPair (by decide : Even 168)

theorem isAdmissible_evenPair_oneHundredSeventy : IsAdmissible (evenPair 170) :=
  isAdmissible_evenPair (by decide : Even 170)

theorem singular_series_pos_evenPair_oneHundredSixtyTwo : 0 < singularSeries (evenPair 162) :=
  singular_series_pos_evenPair (by decide : Even 162)

theorem singular_series_pos_evenPair_oneHundredSixtyFour : 0 < singularSeries (evenPair 164) :=
  singular_series_pos_evenPair (by decide : Even 164)

theorem singular_series_pos_evenPair_oneHundredSixtySix : 0 < singularSeries (evenPair 166) :=
  singular_series_pos_evenPair (by decide : Even 166)

theorem singular_series_pos_evenPair_oneHundredSixtyEight : 0 < singularSeries (evenPair 168) :=
  singular_series_pos_evenPair (by decide : Even 168)

theorem singular_series_pos_evenPair_oneHundredSeventy : 0 < singularSeries (evenPair 170) :=
  singular_series_pos_evenPair (by decide : Even 170)

theorem singular_series_finite_pos_evenPair_oneHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 162) P :=
  singular_series_finite_pos_evenPair (by decide : Even 162) P

theorem singular_series_finite_pos_evenPair_oneHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 164) P :=
  singular_series_finite_pos_evenPair (by decide : Even 164) P

theorem singular_series_finite_pos_evenPair_oneHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 166) P :=
  singular_series_finite_pos_evenPair (by decide : Even 166) P

theorem singular_series_finite_pos_evenPair_oneHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 168) P :=
  singular_series_finite_pos_evenPair (by decide : Even 168) P

theorem singular_series_finite_pos_evenPair_oneHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 170) P :=
  singular_series_finite_pos_evenPair (by decide : Even 170) P

theorem nu_p_oneHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 162) p = if p = 2 ∨ p ∣ 162 then 1 else 2 :=
  nu_p_evenPair (by decide : (162 : ℕ) ≠ 0) (by decide : Even 162) hp

theorem nu_p_oneHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 164) p = if p = 2 ∨ p ∣ 164 then 1 else 2 :=
  nu_p_evenPair (by decide : (164 : ℕ) ≠ 0) (by decide : Even 164) hp

theorem nu_p_oneHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 166) p = if p = 2 ∨ p ∣ 166 then 1 else 2 :=
  nu_p_evenPair (by decide : (166 : ℕ) ≠ 0) (by decide : Even 166) hp

theorem nu_p_oneHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 168) p = if p = 2 ∨ p ∣ 168 then 1 else 2 :=
  nu_p_evenPair (by decide : (168 : ℕ) ≠ 0) (by decide : Even 168) hp

theorem nu_p_oneHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 170) p = if p = 2 ∨ p ∣ 170 then 1 else 2 :=
  nu_p_evenPair (by decide : (170 : ℕ) ≠ 0) (by decide : Even 170) hp

theorem nu_p_oneHundredSixtyTwo_two : nu_p (evenPair 162) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 162)

theorem localFactor_oneHundredSixtyTwo_two : localFactor (evenPair 162) 2 = 2 :=
  localFactor_evenPair_two (by decide : (162 : ℕ) ≠ 0) (by decide : Even 162)

theorem nu_p_oneHundredSeventy_two : nu_p (evenPair 170) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 170)

theorem localFactor_oneHundredSeventy_two : localFactor (evenPair 170) 2 = 2 :=
  localFactor_evenPair_two (by decide : (170 : ℕ) ≠ 0) (by decide : Even 170)

end Brockian.SingularSeries.Gaps162170
