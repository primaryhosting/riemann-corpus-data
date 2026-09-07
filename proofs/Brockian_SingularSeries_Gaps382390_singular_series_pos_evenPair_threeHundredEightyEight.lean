/-
  Brockian/SingularSeriesGaps382390.lean — even binary gaps n ∈ {382, 384, 386, 388, 390}.

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

namespace Brockian.SingularSeries.Gaps382390

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_threeHundredEightyTwo : (evenPair 382).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (382 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredEightyFour : (evenPair 384).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (384 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredEightySix : (evenPair 386).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (386 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredEightyEight : (evenPair 388).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (388 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredNinety : (evenPair 390).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (390 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_threeHundredEightyTwo : IsAdmissible (evenPair 382) :=
  isAdmissible_evenPair (by decide : Even 382)

theorem isAdmissible_evenPair_threeHundredEightyFour : IsAdmissible (evenPair 384) :=
  isAdmissible_evenPair (by decide : Even 384)

theorem isAdmissible_evenPair_threeHundredEightySix : IsAdmissible (evenPair 386) :=
  isAdmissible_evenPair (by decide : Even 386)

theorem isAdmissible_evenPair_threeHundredEightyEight : IsAdmissible (evenPair 388) :=
  isAdmissible_evenPair (by decide : Even 388)

theorem isAdmissible_evenPair_threeHundredNinety : IsAdmissible (evenPair 390) :=
  isAdmissible_evenPair (by decide : Even 390)

theorem singular_series_pos_evenPair_threeHundredEightyTwo : 0 < singularSeries (evenPair 382) :=
  singular_series_pos_evenPair (by decide : Even 382)

theorem singular_series_pos_evenPair_threeHundredEightyFour : 0 < singularSeries (evenPair 384) :=
  singular_series_pos_evenPair (by decide : Even 384)

theorem singular_series_pos_evenPair_threeHundredEightySix : 0 < singularSeries (evenPair 386) :=
  singular_series_pos_evenPair (by decide : Even 386)

theorem singular_series_pos_evenPair_threeHundredEightyEight : 0 < singularSeries (evenPair 388) :=
  singular_series_pos_evenPair (by decide : Even 388)

theorem singular_series_pos_evenPair_threeHundredNinety : 0 < singularSeries (evenPair 390) :=
  singular_series_pos_evenPair (by decide : Even 390)

theorem singular_series_finite_pos_evenPair_threeHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 382) P :=
  singular_series_finite_pos_evenPair (by decide : Even 382) P

theorem singular_series_finite_pos_evenPair_threeHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 384) P :=
  singular_series_finite_pos_evenPair (by decide : Even 384) P

theorem singular_series_finite_pos_evenPair_threeHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 386) P :=
  singular_series_finite_pos_evenPair (by decide : Even 386) P

theorem singular_series_finite_pos_evenPair_threeHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 388) P :=
  singular_series_finite_pos_evenPair (by decide : Even 388) P

theorem singular_series_finite_pos_evenPair_threeHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 390) P :=
  singular_series_finite_pos_evenPair (by decide : Even 390) P

theorem nu_p_threeHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 382) p = if p = 2 ∨ p ∣ 382 then 1 else 2 :=
  nu_p_evenPair (by decide : (382 : ℕ) ≠ 0) (by decide : Even 382) hp

theorem nu_p_threeHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 384) p = if p = 2 ∨ p ∣ 384 then 1 else 2 :=
  nu_p_evenPair (by decide : (384 : ℕ) ≠ 0) (by decide : Even 384) hp

theorem nu_p_threeHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 386) p = if p = 2 ∨ p ∣ 386 then 1 else 2 :=
  nu_p_evenPair (by decide : (386 : ℕ) ≠ 0) (by decide : Even 386) hp

theorem nu_p_threeHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 388) p = if p = 2 ∨ p ∣ 388 then 1 else 2 :=
  nu_p_evenPair (by decide : (388 : ℕ) ≠ 0) (by decide : Even 388) hp

theorem nu_p_threeHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 390) p = if p = 2 ∨ p ∣ 390 then 1 else 2 :=
  nu_p_evenPair (by decide : (390 : ℕ) ≠ 0) (by decide : Even 390) hp

theorem nu_p_threeHundredEightyTwo_two : nu_p (evenPair 382) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 382)

theorem localFactor_threeHundredEightyTwo_two : localFactor (evenPair 382) 2 = 2 :=
  localFactor_evenPair_two (by decide : (382 : ℕ) ≠ 0) (by decide : Even 382)

theorem nu_p_threeHundredNinety_two : nu_p (evenPair 390) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 390)

theorem localFactor_threeHundredNinety_two : localFactor (evenPair 390) 2 = 2 :=
  localFactor_evenPair_two (by decide : (390 : ℕ) ≠ 0) (by decide : Even 390)

end Brockian.SingularSeries.Gaps382390
