/-
  Brockian/SingularSeriesGaps602610.lean — even binary gaps n ∈ {602, 604, 606, 608, 610}.

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

namespace Brockian.SingularSeries.Gaps602610

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixHundredTwo : (evenPair 602).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (602 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredFour : (evenPair 604).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (604 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredSix : (evenPair 606).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (606 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredEight : (evenPair 608).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (608 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredTen : (evenPair 610).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (610 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixHundredTwo : IsAdmissible (evenPair 602) :=
  isAdmissible_evenPair (by decide : Even 602)

theorem isAdmissible_evenPair_sixHundredFour : IsAdmissible (evenPair 604) :=
  isAdmissible_evenPair (by decide : Even 604)

theorem isAdmissible_evenPair_sixHundredSix : IsAdmissible (evenPair 606) :=
  isAdmissible_evenPair (by decide : Even 606)

theorem isAdmissible_evenPair_sixHundredEight : IsAdmissible (evenPair 608) :=
  isAdmissible_evenPair (by decide : Even 608)

theorem isAdmissible_evenPair_sixHundredTen : IsAdmissible (evenPair 610) :=
  isAdmissible_evenPair (by decide : Even 610)

theorem singular_series_pos_evenPair_sixHundredTwo : 0 < singularSeries (evenPair 602) :=
  singular_series_pos_evenPair (by decide : Even 602)

theorem singular_series_pos_evenPair_sixHundredFour : 0 < singularSeries (evenPair 604) :=
  singular_series_pos_evenPair (by decide : Even 604)

theorem singular_series_pos_evenPair_sixHundredSix : 0 < singularSeries (evenPair 606) :=
  singular_series_pos_evenPair (by decide : Even 606)

theorem singular_series_pos_evenPair_sixHundredEight : 0 < singularSeries (evenPair 608) :=
  singular_series_pos_evenPair (by decide : Even 608)

theorem singular_series_pos_evenPair_sixHundredTen : 0 < singularSeries (evenPair 610) :=
  singular_series_pos_evenPair (by decide : Even 610)

theorem singular_series_finite_pos_evenPair_sixHundredTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 602) P :=
  singular_series_finite_pos_evenPair (by decide : Even 602) P

theorem singular_series_finite_pos_evenPair_sixHundredFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 604) P :=
  singular_series_finite_pos_evenPair (by decide : Even 604) P

theorem singular_series_finite_pos_evenPair_sixHundredSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 606) P :=
  singular_series_finite_pos_evenPair (by decide : Even 606) P

theorem singular_series_finite_pos_evenPair_sixHundredEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 608) P :=
  singular_series_finite_pos_evenPair (by decide : Even 608) P

theorem singular_series_finite_pos_evenPair_sixHundredTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 610) P :=
  singular_series_finite_pos_evenPair (by decide : Even 610) P

theorem nu_p_sixHundredTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 602) p = if p = 2 ∨ p ∣ 602 then 1 else 2 :=
  nu_p_evenPair (by decide : (602 : ℕ) ≠ 0) (by decide : Even 602) hp

theorem nu_p_sixHundredFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 604) p = if p = 2 ∨ p ∣ 604 then 1 else 2 :=
  nu_p_evenPair (by decide : (604 : ℕ) ≠ 0) (by decide : Even 604) hp

theorem nu_p_sixHundredSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 606) p = if p = 2 ∨ p ∣ 606 then 1 else 2 :=
  nu_p_evenPair (by decide : (606 : ℕ) ≠ 0) (by decide : Even 606) hp

theorem nu_p_sixHundredEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 608) p = if p = 2 ∨ p ∣ 608 then 1 else 2 :=
  nu_p_evenPair (by decide : (608 : ℕ) ≠ 0) (by decide : Even 608) hp

theorem nu_p_sixHundredTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 610) p = if p = 2 ∨ p ∣ 610 then 1 else 2 :=
  nu_p_evenPair (by decide : (610 : ℕ) ≠ 0) (by decide : Even 610) hp

theorem nu_p_sixHundredTwo_two : nu_p (evenPair 602) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 602)

theorem localFactor_sixHundredTwo_two : localFactor (evenPair 602) 2 = 2 :=
  localFactor_evenPair_two (by decide : (602 : ℕ) ≠ 0) (by decide : Even 602)

theorem nu_p_sixHundredTen_two : nu_p (evenPair 610) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 610)

theorem localFactor_sixHundredTen_two : localFactor (evenPair 610) 2 = 2 :=
  localFactor_evenPair_two (by decide : (610 : ℕ) ≠ 0) (by decide : Even 610)

end Brockian.SingularSeries.Gaps602610
