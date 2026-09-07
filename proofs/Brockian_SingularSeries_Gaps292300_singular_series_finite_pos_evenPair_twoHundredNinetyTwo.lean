/-
  Brockian/SingularSeriesGaps292300.lean — even binary gaps n ∈ {292, 294, 296, 298, 300}.

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

namespace Brockian.SingularSeries.Gaps292300

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoHundredNinetyTwo : (evenPair 292).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (292 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredNinetyFour : (evenPair 294).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (294 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredNinetySix : (evenPair 296).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (296 : ℕ) ≠ 0)

theorem evenPair_card_twoHundredNinetyEight : (evenPair 298).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (298 : ℕ) ≠ 0)

theorem evenPair_card_threeHundred : (evenPair 300).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (300 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoHundredNinetyTwo : IsAdmissible (evenPair 292) :=
  isAdmissible_evenPair (by decide : Even 292)

theorem isAdmissible_evenPair_twoHundredNinetyFour : IsAdmissible (evenPair 294) :=
  isAdmissible_evenPair (by decide : Even 294)

theorem isAdmissible_evenPair_twoHundredNinetySix : IsAdmissible (evenPair 296) :=
  isAdmissible_evenPair (by decide : Even 296)

theorem isAdmissible_evenPair_twoHundredNinetyEight : IsAdmissible (evenPair 298) :=
  isAdmissible_evenPair (by decide : Even 298)

theorem isAdmissible_evenPair_threeHundred : IsAdmissible (evenPair 300) :=
  isAdmissible_evenPair (by decide : Even 300)

theorem singular_series_pos_evenPair_twoHundredNinetyTwo : 0 < singularSeries (evenPair 292) :=
  singular_series_pos_evenPair (by decide : Even 292)

theorem singular_series_pos_evenPair_twoHundredNinetyFour : 0 < singularSeries (evenPair 294) :=
  singular_series_pos_evenPair (by decide : Even 294)

theorem singular_series_pos_evenPair_twoHundredNinetySix : 0 < singularSeries (evenPair 296) :=
  singular_series_pos_evenPair (by decide : Even 296)

theorem singular_series_pos_evenPair_twoHundredNinetyEight : 0 < singularSeries (evenPair 298) :=
  singular_series_pos_evenPair (by decide : Even 298)

theorem singular_series_pos_evenPair_threeHundred : 0 < singularSeries (evenPair 300) :=
  singular_series_pos_evenPair (by decide : Even 300)

theorem singular_series_finite_pos_evenPair_twoHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 292) P :=
  singular_series_finite_pos_evenPair (by decide : Even 292) P

theorem singular_series_finite_pos_evenPair_twoHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 294) P :=
  singular_series_finite_pos_evenPair (by decide : Even 294) P

theorem singular_series_finite_pos_evenPair_twoHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 296) P :=
  singular_series_finite_pos_evenPair (by decide : Even 296) P

theorem singular_series_finite_pos_evenPair_twoHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 298) P :=
  singular_series_finite_pos_evenPair (by decide : Even 298) P

theorem singular_series_finite_pos_evenPair_threeHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 300) P :=
  singular_series_finite_pos_evenPair (by decide : Even 300) P

theorem nu_p_twoHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 292) p = if p = 2 ∨ p ∣ 292 then 1 else 2 :=
  nu_p_evenPair (by decide : (292 : ℕ) ≠ 0) (by decide : Even 292) hp

theorem nu_p_twoHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 294) p = if p = 2 ∨ p ∣ 294 then 1 else 2 :=
  nu_p_evenPair (by decide : (294 : ℕ) ≠ 0) (by decide : Even 294) hp

theorem nu_p_twoHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 296) p = if p = 2 ∨ p ∣ 296 then 1 else 2 :=
  nu_p_evenPair (by decide : (296 : ℕ) ≠ 0) (by decide : Even 296) hp

theorem nu_p_twoHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 298) p = if p = 2 ∨ p ∣ 298 then 1 else 2 :=
  nu_p_evenPair (by decide : (298 : ℕ) ≠ 0) (by decide : Even 298) hp

theorem nu_p_threeHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 300) p = if p = 2 ∨ p ∣ 300 then 1 else 2 :=
  nu_p_evenPair (by decide : (300 : ℕ) ≠ 0) (by decide : Even 300) hp

theorem nu_p_twoHundredNinetyTwo_two : nu_p (evenPair 292) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 292)

theorem localFactor_twoHundredNinetyTwo_two : localFactor (evenPair 292) 2 = 2 :=
  localFactor_evenPair_two (by decide : (292 : ℕ) ≠ 0) (by decide : Even 292)

theorem nu_p_threeHundred_two : nu_p (evenPair 300) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 300)

theorem localFactor_threeHundred_two : localFactor (evenPair 300) 2 = 2 :=
  localFactor_evenPair_two (by decide : (300 : ℕ) ≠ 0) (by decide : Even 300)

end Brockian.SingularSeries.Gaps292300
