/-
  Brockian/SingularSeriesGaps202210.lean — even binary gaps n ∈ {202, 204, 206, 208, 210}.

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

namespace Brockian.SingularSeries.Gaps202210

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoHundredTwo : (evenPair 202).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (202 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredFour : (evenPair 204).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (204 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredSix : (evenPair 206).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (206 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredEight : (evenPair 208).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (208 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredTen : (evenPair 210).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (210 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoHundredTwo : IsAdmissible (evenPair 202) :=
  isAdmissible_evenPair (by decide : Even 202)

theorem isAdmissible_evenPair_twoHundredFour : IsAdmissible (evenPair 204) :=
  isAdmissible_evenPair (by decide : Even 204)

theorem isAdmissible_evenPair_twoHundredSix : IsAdmissible (evenPair 206) :=
  isAdmissible_evenPair (by decide : Even 206)

theorem isAdmissible_evenPair_twoHundredEight : IsAdmissible (evenPair 208) :=
  isAdmissible_evenPair (by decide : Even 208)

theorem isAdmissible_evenPair_twoHundredTen : IsAdmissible (evenPair 210) :=
  isAdmissible_evenPair (by decide : Even 210)

theorem singular_series_pos_evenPair_twoHundredTwo : 0 < singularSeries (evenPair 202) :=
  singular_series_pos_evenPair (by decide : Even 202)

theorem singular_series_pos_evenPair_twoHundredFour : 0 < singularSeries (evenPair 204) :=
  singular_series_pos_evenPair (by decide : Even 204)

theorem singular_series_pos_evenPair_twoHundredSix : 0 < singularSeries (evenPair 206) :=
  singular_series_pos_evenPair (by decide : Even 206)

theorem singular_series_pos_evenPair_twoHundredEight : 0 < singularSeries (evenPair 208) :=
  singular_series_pos_evenPair (by decide : Even 208)

theorem singular_series_pos_evenPair_twoHundredTen : 0 < singularSeries (evenPair 210) :=
  singular_series_pos_evenPair (by decide : Even 210)

theorem singular_series_finite_pos_evenPair_twoHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 202) P :=
  singular_series_finite_pos_evenPair (by decide : Even 202) P

theorem singular_series_finite_pos_evenPair_twoHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 204) P :=
  singular_series_finite_pos_evenPair (by decide : Even 204) P

theorem singular_series_finite_pos_evenPair_twoHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 206) P :=
  singular_series_finite_pos_evenPair (by decide : Even 206) P

theorem singular_series_finite_pos_evenPair_twoHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 208) P :=
  singular_series_finite_pos_evenPair (by decide : Even 208) P

theorem singular_series_finite_pos_evenPair_twoHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 210) P :=
  singular_series_finite_pos_evenPair (by decide : Even 210) P

theorem nu_p_twoHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 202) p = if p = 2 ∨ p ∣ 202 then 1 else 2 :=
  nu_p_evenPair (by decide : (202 : ℕ) ≠ 0) (by decide : Even 202) hp

theorem nu_p_twoHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 204) p = if p = 2 ∨ p ∣ 204 then 1 else 2 :=
  nu_p_evenPair (by decide : (204 : ℕ) ≠ 0) (by decide : Even 204) hp

theorem nu_p_twoHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 206) p = if p = 2 ∨ p ∣ 206 then 1 else 2 :=
  nu_p_evenPair (by decide : (206 : ℕ) ≠ 0) (by decide : Even 206) hp

theorem nu_p_twoHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 208) p = if p = 2 ∨ p ∣ 208 then 1 else 2 :=
  nu_p_evenPair (by decide : (208 : ℕ) ≠ 0) (by decide : Even 208) hp

theorem nu_p_twoHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 210) p = if p = 2 ∨ p ∣ 210 then 1 else 2 :=
  nu_p_evenPair (by decide : (210 : ℕ) ≠ 0) (by decide : Even 210) hp

theorem nu_p_twoHundredTwo_two : nu_p (evenPair 202) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 202)

theorem localFactor_twoHundredTwo_two : localFactor (evenPair 202) 2 = 2 :=
  localFactor_evenPair_two (by decide : (202 : ℕ) ≠ 0) (by decide : Even 202)

theorem nu_p_twoHundredTen_two : nu_p (evenPair 210) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 210)

theorem localFactor_twoHundredTen_two : localFactor (evenPair 210) 2 = 2 :=
  localFactor_evenPair_two (by decide : (210 : ℕ) ≠ 0) (by decide : Even 210)

end Brockian.SingularSeries.Gaps202210
