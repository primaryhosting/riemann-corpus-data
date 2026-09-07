/-
  Brockian/SingularSeriesGaps702710.lean — even binary gaps n ∈ {702, 704, 706, 708, 710}.

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

namespace Brockian.SingularSeries.Gaps702710

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sevenHundredTwo : (evenPair 702).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (702 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredFour : (evenPair 704).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (704 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredSix : (evenPair 706).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (706 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredEight : (evenPair 708).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (708 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredTen : (evenPair 710).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (710 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sevenHundredTwo : IsAdmissible (evenPair 702) :=
  isAdmissible_evenPair (by decide : Even 702)

theorem isAdmissible_evenPair_sevenHundredFour : IsAdmissible (evenPair 704) :=
  isAdmissible_evenPair (by decide : Even 704)

theorem isAdmissible_evenPair_sevenHundredSix : IsAdmissible (evenPair 706) :=
  isAdmissible_evenPair (by decide : Even 706)

theorem isAdmissible_evenPair_sevenHundredEight : IsAdmissible (evenPair 708) :=
  isAdmissible_evenPair (by decide : Even 708)

theorem isAdmissible_evenPair_sevenHundredTen : IsAdmissible (evenPair 710) :=
  isAdmissible_evenPair (by decide : Even 710)

theorem singular_series_pos_evenPair_sevenHundredTwo : 0 < singularSeries (evenPair 702) :=
  singular_series_pos_evenPair (by decide : Even 702)

theorem singular_series_pos_evenPair_sevenHundredFour : 0 < singularSeries (evenPair 704) :=
  singular_series_pos_evenPair (by decide : Even 704)

theorem singular_series_pos_evenPair_sevenHundredSix : 0 < singularSeries (evenPair 706) :=
  singular_series_pos_evenPair (by decide : Even 706)

theorem singular_series_pos_evenPair_sevenHundredEight : 0 < singularSeries (evenPair 708) :=
  singular_series_pos_evenPair (by decide : Even 708)

theorem singular_series_pos_evenPair_sevenHundredTen : 0 < singularSeries (evenPair 710) :=
  singular_series_pos_evenPair (by decide : Even 710)

theorem singular_series_finite_pos_evenPair_sevenHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 702) P :=
  singular_series_finite_pos_evenPair (by decide : Even 702) P

theorem singular_series_finite_pos_evenPair_sevenHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 704) P :=
  singular_series_finite_pos_evenPair (by decide : Even 704) P

theorem singular_series_finite_pos_evenPair_sevenHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 706) P :=
  singular_series_finite_pos_evenPair (by decide : Even 706) P

theorem singular_series_finite_pos_evenPair_sevenHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 708) P :=
  singular_series_finite_pos_evenPair (by decide : Even 708) P

theorem singular_series_finite_pos_evenPair_sevenHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 710) P :=
  singular_series_finite_pos_evenPair (by decide : Even 710) P

theorem nu_p_sevenHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 702) p = if p = 2 ∨ p ∣ 702 then 1 else 2 :=
  nu_p_evenPair (by decide : (702 : ℕ) ≠ 0) (by decide : Even 702) hp

theorem nu_p_sevenHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 704) p = if p = 2 ∨ p ∣ 704 then 1 else 2 :=
  nu_p_evenPair (by decide : (704 : ℕ) ≠ 0) (by decide : Even 704) hp

theorem nu_p_sevenHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 706) p = if p = 2 ∨ p ∣ 706 then 1 else 2 :=
  nu_p_evenPair (by decide : (706 : ℕ) ≠ 0) (by decide : Even 706) hp

theorem nu_p_sevenHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 708) p = if p = 2 ∨ p ∣ 708 then 1 else 2 :=
  nu_p_evenPair (by decide : (708 : ℕ) ≠ 0) (by decide : Even 708) hp

theorem nu_p_sevenHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 710) p = if p = 2 ∨ p ∣ 710 then 1 else 2 :=
  nu_p_evenPair (by decide : (710 : ℕ) ≠ 0) (by decide : Even 710) hp

theorem nu_p_sevenHundredTwo_two : nu_p (evenPair 702) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 702)

theorem localFactor_sevenHundredTwo_two : localFactor (evenPair 702) 2 = 2 :=
  localFactor_evenPair_two (by decide : (702 : ℕ) ≠ 0) (by decide : Even 702)

theorem nu_p_sevenHundredTen_two : nu_p (evenPair 710) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 710)

theorem localFactor_sevenHundredTen_two : localFactor (evenPair 710) 2 = 2 :=
  localFactor_evenPair_two (by decide : (710 : ℕ) ≠ 0) (by decide : Even 710)

end Brockian.SingularSeries.Gaps702710
