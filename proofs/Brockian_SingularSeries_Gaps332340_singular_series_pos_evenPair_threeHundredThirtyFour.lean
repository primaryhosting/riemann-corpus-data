/-
  Brockian/SingularSeriesGaps332340.lean — even binary gaps n ∈ {332, 334, 336, 338, 340}.

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

namespace Brockian.SingularSeries.Gaps332340

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_threeHundredThirtyTwo : (evenPair 332).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (332 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredThirtyFour : (evenPair 334).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (334 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredThirtySix : (evenPair 336).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (336 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredThirtyEight : (evenPair 338).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (338 : ℕ) ≠ 0)

theorem evenPair_card_threeHundredForty : (evenPair 340).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (340 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_threeHundredThirtyTwo : IsAdmissible (evenPair 332) :=
  isAdmissible_evenPair (by decide : Even 332)

theorem isAdmissible_evenPair_threeHundredThirtyFour : IsAdmissible (evenPair 334) :=
  isAdmissible_evenPair (by decide : Even 334)

theorem isAdmissible_evenPair_threeHundredThirtySix : IsAdmissible (evenPair 336) :=
  isAdmissible_evenPair (by decide : Even 336)

theorem isAdmissible_evenPair_threeHundredThirtyEight : IsAdmissible (evenPair 338) :=
  isAdmissible_evenPair (by decide : Even 338)

theorem isAdmissible_evenPair_threeHundredForty : IsAdmissible (evenPair 340) :=
  isAdmissible_evenPair (by decide : Even 340)

theorem singular_series_pos_evenPair_threeHundredThirtyTwo : 0 < singularSeries (evenPair 332) :=
  singular_series_pos_evenPair (by decide : Even 332)

theorem singular_series_pos_evenPair_threeHundredThirtyFour : 0 < singularSeries (evenPair 334) :=
  singular_series_pos_evenPair (by decide : Even 334)

theorem singular_series_pos_evenPair_threeHundredThirtySix : 0 < singularSeries (evenPair 336) :=
  singular_series_pos_evenPair (by decide : Even 336)

theorem singular_series_pos_evenPair_threeHundredThirtyEight : 0 < singularSeries (evenPair 338) :=
  singular_series_pos_evenPair (by decide : Even 338)

theorem singular_series_pos_evenPair_threeHundredForty : 0 < singularSeries (evenPair 340) :=
  singular_series_pos_evenPair (by decide : Even 340)

theorem singular_series_finite_pos_evenPair_threeHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 332) P :=
  singular_series_finite_pos_evenPair (by decide : Even 332) P

theorem singular_series_finite_pos_evenPair_threeHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 334) P :=
  singular_series_finite_pos_evenPair (by decide : Even 334) P

theorem singular_series_finite_pos_evenPair_threeHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 336) P :=
  singular_series_finite_pos_evenPair (by decide : Even 336) P

theorem singular_series_finite_pos_evenPair_threeHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 338) P :=
  singular_series_finite_pos_evenPair (by decide : Even 338) P

theorem singular_series_finite_pos_evenPair_threeHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 340) P :=
  singular_series_finite_pos_evenPair (by decide : Even 340) P

theorem nu_p_threeHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 332) p = if p = 2 ∨ p ∣ 332 then 1 else 2 :=
  nu_p_evenPair (by decide : (332 : ℕ) ≠ 0) (by decide : Even 332) hp

theorem nu_p_threeHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 334) p = if p = 2 ∨ p ∣ 334 then 1 else 2 :=
  nu_p_evenPair (by decide : (334 : ℕ) ≠ 0) (by decide : Even 334) hp

theorem nu_p_threeHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 336) p = if p = 2 ∨ p ∣ 336 then 1 else 2 :=
  nu_p_evenPair (by decide : (336 : ℕ) ≠ 0) (by decide : Even 336) hp

theorem nu_p_threeHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 338) p = if p = 2 ∨ p ∣ 338 then 1 else 2 :=
  nu_p_evenPair (by decide : (338 : ℕ) ≠ 0) (by decide : Even 338) hp

theorem nu_p_threeHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 340) p = if p = 2 ∨ p ∣ 340 then 1 else 2 :=
  nu_p_evenPair (by decide : (340 : ℕ) ≠ 0) (by decide : Even 340) hp

theorem nu_p_threeHundredThirtyTwo_two : nu_p (evenPair 332) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 332)

theorem localFactor_threeHundredThirtyTwo_two : localFactor (evenPair 332) 2 = 2 :=
  localFactor_evenPair_two (by decide : (332 : ℕ) ≠ 0) (by decide : Even 332)

theorem nu_p_threeHundredForty_two : nu_p (evenPair 340) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 340)

theorem localFactor_threeHundredForty_two : localFactor (evenPair 340) 2 = 2 :=
  localFactor_evenPair_two (by decide : (340 : ℕ) ≠ 0) (by decide : Even 340)

end Brockian.SingularSeries.Gaps332340
