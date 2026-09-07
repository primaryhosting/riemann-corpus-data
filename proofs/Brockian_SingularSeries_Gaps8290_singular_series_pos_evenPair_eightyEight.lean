/-
  Brockian/SingularSeriesGaps8290.lean — even binary gaps n ∈ {82, 84, 86, 88, 90}.

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

namespace Brockian.SingularSeries.Gaps8290

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightyTwo : (evenPair 82).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (82 : ℕ) ≠ 0)

theorem evenPair_card_eightyFour : (evenPair 84).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (84 : ℕ) ≠ 0)

theorem evenPair_card_eightySix : (evenPair 86).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (86 : ℕ) ≠ 0)

theorem evenPair_card_eightyEight : (evenPair 88).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (88 : ℕ) ≠ 0)

theorem evenPair_card_ninety : (evenPair 90).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (90 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightyTwo : IsAdmissible (evenPair 82) :=
  isAdmissible_evenPair (by decide : Even 82)

theorem isAdmissible_evenPair_eightyFour : IsAdmissible (evenPair 84) :=
  isAdmissible_evenPair (by decide : Even 84)

theorem isAdmissible_evenPair_eightySix : IsAdmissible (evenPair 86) :=
  isAdmissible_evenPair (by decide : Even 86)

theorem isAdmissible_evenPair_eightyEight : IsAdmissible (evenPair 88) :=
  isAdmissible_evenPair (by decide : Even 88)

theorem isAdmissible_evenPair_ninety : IsAdmissible (evenPair 90) :=
  isAdmissible_evenPair (by decide : Even 90)

theorem singular_series_pos_evenPair_eightyTwo : 0 < singularSeries (evenPair 82) :=
  singular_series_pos_evenPair (by decide : Even 82)

theorem singular_series_pos_evenPair_eightyFour : 0 < singularSeries (evenPair 84) :=
  singular_series_pos_evenPair (by decide : Even 84)

theorem singular_series_pos_evenPair_eightySix : 0 < singularSeries (evenPair 86) :=
  singular_series_pos_evenPair (by decide : Even 86)

theorem singular_series_pos_evenPair_eightyEight : 0 < singularSeries (evenPair 88) :=
  singular_series_pos_evenPair (by decide : Even 88)

theorem singular_series_pos_evenPair_ninety : 0 < singularSeries (evenPair 90) :=
  singular_series_pos_evenPair (by decide : Even 90)

theorem singular_series_finite_pos_evenPair_eightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 82) P :=
  singular_series_finite_pos_evenPair (by decide : Even 82) P

theorem singular_series_finite_pos_evenPair_eightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 84) P :=
  singular_series_finite_pos_evenPair (by decide : Even 84) P

theorem singular_series_finite_pos_evenPair_eightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 86) P :=
  singular_series_finite_pos_evenPair (by decide : Even 86) P

theorem singular_series_finite_pos_evenPair_eightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 88) P :=
  singular_series_finite_pos_evenPair (by decide : Even 88) P

theorem singular_series_finite_pos_evenPair_ninety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 90) P :=
  singular_series_finite_pos_evenPair (by decide : Even 90) P

theorem nu_p_eightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 82) p = if p = 2 ∨ p ∣ 82 then 1 else 2 :=
  nu_p_evenPair (by decide : (82 : ℕ) ≠ 0) (by decide : Even 82) hp

theorem nu_p_eightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 84) p = if p = 2 ∨ p ∣ 84 then 1 else 2 :=
  nu_p_evenPair (by decide : (84 : ℕ) ≠ 0) (by decide : Even 84) hp

theorem nu_p_eightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 86) p = if p = 2 ∨ p ∣ 86 then 1 else 2 :=
  nu_p_evenPair (by decide : (86 : ℕ) ≠ 0) (by decide : Even 86) hp

theorem nu_p_eightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 88) p = if p = 2 ∨ p ∣ 88 then 1 else 2 :=
  nu_p_evenPair (by decide : (88 : ℕ) ≠ 0) (by decide : Even 88) hp

theorem nu_p_ninety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 90) p = if p = 2 ∨ p ∣ 90 then 1 else 2 :=
  nu_p_evenPair (by decide : (90 : ℕ) ≠ 0) (by decide : Even 90) hp

theorem nu_p_eightyTwo_two : nu_p (evenPair 82) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 82)

theorem localFactor_eightyTwo_two : localFactor (evenPair 82) 2 = 2 :=
  localFactor_evenPair_two (by decide : (82 : ℕ) ≠ 0) (by decide : Even 82)

theorem nu_p_ninety_two : nu_p (evenPair 90) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 90)

theorem localFactor_ninety_two : localFactor (evenPair 90) 2 = 2 :=
  localFactor_evenPair_two (by decide : (90 : ℕ) ≠ 0) (by decide : Even 90)

end Brockian.SingularSeries.Gaps8290
