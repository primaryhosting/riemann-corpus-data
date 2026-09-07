/-
  Brockian/SingularSeriesGaps282290.lean — even binary gaps n ∈ {282, 284, 286, 288, 290}.

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

namespace Brockian.SingularSeries.Gaps282290

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoHundredEightyTwo : (evenPair 282).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (282 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredEightyFour : (evenPair 284).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (284 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredEightySix : (evenPair 286).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (286 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredEightyEight : (evenPair 288).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (288 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredNinety : (evenPair 290).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (290 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoHundredEightyTwo : IsAdmissible (evenPair 282) :=
  isAdmissible_evenPair (by decide : Even 282)

theorem isAdmissible_evenPair_twoHundredEightyFour : IsAdmissible (evenPair 284) :=
  isAdmissible_evenPair (by decide : Even 284)

theorem isAdmissible_evenPair_twoHundredEightySix : IsAdmissible (evenPair 286) :=
  isAdmissible_evenPair (by decide : Even 286)

theorem isAdmissible_evenPair_twoHundredEightyEight : IsAdmissible (evenPair 288) :=
  isAdmissible_evenPair (by decide : Even 288)

theorem isAdmissible_evenPair_twoHundredNinety : IsAdmissible (evenPair 290) :=
  isAdmissible_evenPair (by decide : Even 290)

theorem singular_series_pos_evenPair_twoHundredEightyTwo : 0 < singularSeries (evenPair 282) :=
  singular_series_pos_evenPair (by decide : Even 282)

theorem singular_series_pos_evenPair_twoHundredEightyFour : 0 < singularSeries (evenPair 284) :=
  singular_series_pos_evenPair (by decide : Even 284)

theorem singular_series_pos_evenPair_twoHundredEightySix : 0 < singularSeries (evenPair 286) :=
  singular_series_pos_evenPair (by decide : Even 286)

theorem singular_series_pos_evenPair_twoHundredEightyEight : 0 < singularSeries (evenPair 288) :=
  singular_series_pos_evenPair (by decide : Even 288)

theorem singular_series_pos_evenPair_twoHundredNinety : 0 < singularSeries (evenPair 290) :=
  singular_series_pos_evenPair (by decide : Even 290)

theorem singular_series_finite_pos_evenPair_twoHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 282) P :=
  singular_series_finite_pos_evenPair (by decide : Even 282) P

theorem singular_series_finite_pos_evenPair_twoHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 284) P :=
  singular_series_finite_pos_evenPair (by decide : Even 284) P

theorem singular_series_finite_pos_evenPair_twoHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 286) P :=
  singular_series_finite_pos_evenPair (by decide : Even 286) P

theorem singular_series_finite_pos_evenPair_twoHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 288) P :=
  singular_series_finite_pos_evenPair (by decide : Even 288) P

theorem singular_series_finite_pos_evenPair_twoHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 290) P :=
  singular_series_finite_pos_evenPair (by decide : Even 290) P

theorem nu_p_twoHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 282) p = if p = 2 ∨ p ∣ 282 then 1 else 2 :=
  nu_p_evenPair (by decide : (282 : ℕ) ≠ 0) (by decide : Even 282) hp

theorem nu_p_twoHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 284) p = if p = 2 ∨ p ∣ 284 then 1 else 2 :=
  nu_p_evenPair (by decide : (284 : ℕ) ≠ 0) (by decide : Even 284) hp

theorem nu_p_twoHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 286) p = if p = 2 ∨ p ∣ 286 then 1 else 2 :=
  nu_p_evenPair (by decide : (286 : ℕ) ≠ 0) (by decide : Even 286) hp

theorem nu_p_twoHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 288) p = if p = 2 ∨ p ∣ 288 then 1 else 2 :=
  nu_p_evenPair (by decide : (288 : ℕ) ≠ 0) (by decide : Even 288) hp

theorem nu_p_twoHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 290) p = if p = 2 ∨ p ∣ 290 then 1 else 2 :=
  nu_p_evenPair (by decide : (290 : ℕ) ≠ 0) (by decide : Even 290) hp

theorem nu_p_twoHundredEightyTwo_two : nu_p (evenPair 282) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 282)

theorem localFactor_twoHundredEightyTwo_two : localFactor (evenPair 282) 2 = 2 :=
  localFactor_evenPair_two (by decide : (282 : ℕ) ≠ 0) (by decide : Even 282)

theorem nu_p_twoHundredNinety_two : nu_p (evenPair 290) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 290)

theorem localFactor_twoHundredNinety_two : localFactor (evenPair 290) 2 = 2 :=
  localFactor_evenPair_two (by decide : (290 : ℕ) ≠ 0) (by decide : Even 290)

end Brockian.SingularSeries.Gaps282290
