/-
  Brockian/SingularSeriesGaps352360.lean — even binary gaps n ∈ {352, 354, 356, 358, 360}.

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

namespace Brockian.SingularSeries.Gaps352360

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_threeHundredFiftyTwo : (evenPair 352).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (352 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredFiftyFour : (evenPair 354).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (354 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredFiftySix : (evenPair 356).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (356 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredFiftyEight : (evenPair 358).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (358 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredSixty : (evenPair 360).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (360 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_threeHundredFiftyTwo : IsAdmissible (evenPair 352) :=
  isAdmissible_evenPair (by decide : Even 352)

theorem isAdmissible_evenPair_threeHundredFiftyFour : IsAdmissible (evenPair 354) :=
  isAdmissible_evenPair (by decide : Even 354)

theorem isAdmissible_evenPair_threeHundredFiftySix : IsAdmissible (evenPair 356) :=
  isAdmissible_evenPair (by decide : Even 356)

theorem isAdmissible_evenPair_threeHundredFiftyEight : IsAdmissible (evenPair 358) :=
  isAdmissible_evenPair (by decide : Even 358)

theorem isAdmissible_evenPair_threeHundredSixty : IsAdmissible (evenPair 360) :=
  isAdmissible_evenPair (by decide : Even 360)

theorem singular_series_pos_evenPair_threeHundredFiftyTwo : 0 < singularSeries (evenPair 352) :=
  singular_series_pos_evenPair (by decide : Even 352)

theorem singular_series_pos_evenPair_threeHundredFiftyFour : 0 < singularSeries (evenPair 354) :=
  singular_series_pos_evenPair (by decide : Even 354)

theorem singular_series_pos_evenPair_threeHundredFiftySix : 0 < singularSeries (evenPair 356) :=
  singular_series_pos_evenPair (by decide : Even 356)

theorem singular_series_pos_evenPair_threeHundredFiftyEight : 0 < singularSeries (evenPair 358) :=
  singular_series_pos_evenPair (by decide : Even 358)

theorem singular_series_pos_evenPair_threeHundredSixty : 0 < singularSeries (evenPair 360) :=
  singular_series_pos_evenPair (by decide : Even 360)

theorem singular_series_finite_pos_evenPair_threeHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 352) P :=
  singular_series_finite_pos_evenPair (by decide : Even 352) P

theorem singular_series_finite_pos_evenPair_threeHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 354) P :=
  singular_series_finite_pos_evenPair (by decide : Even 354) P

theorem singular_series_finite_pos_evenPair_threeHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 356) P :=
  singular_series_finite_pos_evenPair (by decide : Even 356) P

theorem singular_series_finite_pos_evenPair_threeHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 358) P :=
  singular_series_finite_pos_evenPair (by decide : Even 358) P

theorem singular_series_finite_pos_evenPair_threeHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 360) P :=
  singular_series_finite_pos_evenPair (by decide : Even 360) P

theorem nu_p_threeHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 352) p = if p = 2 ∨ p ∣ 352 then 1 else 2 :=
  nu_p_evenPair (by decide : (352 : ℕ) ≠ 0) (by decide : Even 352) hp

theorem nu_p_threeHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 354) p = if p = 2 ∨ p ∣ 354 then 1 else 2 :=
  nu_p_evenPair (by decide : (354 : ℕ) ≠ 0) (by decide : Even 354) hp

theorem nu_p_threeHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 356) p = if p = 2 ∨ p ∣ 356 then 1 else 2 :=
  nu_p_evenPair (by decide : (356 : ℕ) ≠ 0) (by decide : Even 356) hp

theorem nu_p_threeHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 358) p = if p = 2 ∨ p ∣ 358 then 1 else 2 :=
  nu_p_evenPair (by decide : (358 : ℕ) ≠ 0) (by decide : Even 358) hp

theorem nu_p_threeHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 360) p = if p = 2 ∨ p ∣ 360 then 1 else 2 :=
  nu_p_evenPair (by decide : (360 : ℕ) ≠ 0) (by decide : Even 360) hp

theorem nu_p_threeHundredFiftyTwo_two : nu_p (evenPair 352) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 352)

theorem localFactor_threeHundredFiftyTwo_two : localFactor (evenPair 352) 2 = 2 :=
  localFactor_evenPair_two (by decide : (352 : ℕ) ≠ 0) (by decide : Even 352)

theorem nu_p_threeHundredSixty_two : nu_p (evenPair 360) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 360)

theorem localFactor_threeHundredSixty_two : localFactor (evenPair 360) 2 = 2 :=
  localFactor_evenPair_two (by decide : (360 : ℕ) ≠ 0) (by decide : Even 360)

end Brockian.SingularSeries.Gaps352360
