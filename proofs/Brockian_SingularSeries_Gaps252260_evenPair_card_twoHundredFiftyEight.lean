/-
  Brockian/SingularSeriesGaps252260.lean — even binary gaps n ∈ {252, 254, 256, 258, 260}.

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

namespace Brockian.SingularSeries.Gaps252260

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoHundredFiftyTwo : (evenPair 252).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (252 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredFiftyFour : (evenPair 254).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (254 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredFiftySix : (evenPair 256).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (256 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredFiftyEight : (evenPair 258).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (258 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredSixty : (evenPair 260).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (260 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoHundredFiftyTwo : IsAdmissible (evenPair 252) :=
  isAdmissible_evenPair (by decide : Even 252)

theorem isAdmissible_evenPair_twoHundredFiftyFour : IsAdmissible (evenPair 254) :=
  isAdmissible_evenPair (by decide : Even 254)

theorem isAdmissible_evenPair_twoHundredFiftySix : IsAdmissible (evenPair 256) :=
  isAdmissible_evenPair (by decide : Even 256)

theorem isAdmissible_evenPair_twoHundredFiftyEight : IsAdmissible (evenPair 258) :=
  isAdmissible_evenPair (by decide : Even 258)

theorem isAdmissible_evenPair_twoHundredSixty : IsAdmissible (evenPair 260) :=
  isAdmissible_evenPair (by decide : Even 260)

theorem singular_series_pos_evenPair_twoHundredFiftyTwo : 0 < singularSeries (evenPair 252) :=
  singular_series_pos_evenPair (by decide : Even 252)

theorem singular_series_pos_evenPair_twoHundredFiftyFour : 0 < singularSeries (evenPair 254) :=
  singular_series_pos_evenPair (by decide : Even 254)

theorem singular_series_pos_evenPair_twoHundredFiftySix : 0 < singularSeries (evenPair 256) :=
  singular_series_pos_evenPair (by decide : Even 256)

theorem singular_series_pos_evenPair_twoHundredFiftyEight : 0 < singularSeries (evenPair 258) :=
  singular_series_pos_evenPair (by decide : Even 258)

theorem singular_series_pos_evenPair_twoHundredSixty : 0 < singularSeries (evenPair 260) :=
  singular_series_pos_evenPair (by decide : Even 260)

theorem singular_series_finite_pos_evenPair_twoHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 252) P :=
  singular_series_finite_pos_evenPair (by decide : Even 252) P

theorem singular_series_finite_pos_evenPair_twoHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 254) P :=
  singular_series_finite_pos_evenPair (by decide : Even 254) P

theorem singular_series_finite_pos_evenPair_twoHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 256) P :=
  singular_series_finite_pos_evenPair (by decide : Even 256) P

theorem singular_series_finite_pos_evenPair_twoHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 258) P :=
  singular_series_finite_pos_evenPair (by decide : Even 258) P

theorem singular_series_finite_pos_evenPair_twoHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 260) P :=
  singular_series_finite_pos_evenPair (by decide : Even 260) P

theorem nu_p_twoHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 252) p = if p = 2 ∨ p ∣ 252 then 1 else 2 :=
  nu_p_evenPair (by decide : (252 : ℕ) ≠ 0) (by decide : Even 252) hp

theorem nu_p_twoHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 254) p = if p = 2 ∨ p ∣ 254 then 1 else 2 :=
  nu_p_evenPair (by decide : (254 : ℕ) ≠ 0) (by decide : Even 254) hp

theorem nu_p_twoHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 256) p = if p = 2 ∨ p ∣ 256 then 1 else 2 :=
  nu_p_evenPair (by decide : (256 : ℕ) ≠ 0) (by decide : Even 256) hp

theorem nu_p_twoHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 258) p = if p = 2 ∨ p ∣ 258 then 1 else 2 :=
  nu_p_evenPair (by decide : (258 : ℕ) ≠ 0) (by decide : Even 258) hp

theorem nu_p_twoHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 260) p = if p = 2 ∨ p ∣ 260 then 1 else 2 :=
  nu_p_evenPair (by decide : (260 : ℕ) ≠ 0) (by decide : Even 260) hp

theorem nu_p_twoHundredFiftyTwo_two : nu_p (evenPair 252) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 252)

theorem localFactor_twoHundredFiftyTwo_two : localFactor (evenPair 252) 2 = 2 :=
  localFactor_evenPair_two (by decide : (252 : ℕ) ≠ 0) (by decide : Even 252)

theorem nu_p_twoHundredSixty_two : nu_p (evenPair 260) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 260)

theorem localFactor_twoHundredSixty_two : localFactor (evenPair 260) 2 = 2 :=
  localFactor_evenPair_two (by decide : (260 : ℕ) ≠ 0) (by decide : Even 260)

end Brockian.SingularSeries.Gaps252260
