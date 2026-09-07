/-
  Brockian/SingularSeriesGaps632640.lean — even binary gaps n ∈ {632, 634, 636, 638, 640}.

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

namespace Brockian.SingularSeries.Gaps632640

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixHundredThirtyTwo : (evenPair 632).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (632 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredThirtyFour : (evenPair 634).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (634 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredThirtySix : (evenPair 636).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (636 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredThirtyEight : (evenPair 638).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (638 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredForty : (evenPair 640).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (640 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixHundredThirtyTwo : IsAdmissible (evenPair 632) :=
  isAdmissible_evenPair (by decide : Even 632)

theorem isAdmissible_evenPair_sixHundredThirtyFour : IsAdmissible (evenPair 634) :=
  isAdmissible_evenPair (by decide : Even 634)

theorem isAdmissible_evenPair_sixHundredThirtySix : IsAdmissible (evenPair 636) :=
  isAdmissible_evenPair (by decide : Even 636)

theorem isAdmissible_evenPair_sixHundredThirtyEight : IsAdmissible (evenPair 638) :=
  isAdmissible_evenPair (by decide : Even 638)

theorem isAdmissible_evenPair_sixHundredForty : IsAdmissible (evenPair 640) :=
  isAdmissible_evenPair (by decide : Even 640)

theorem singular_series_pos_evenPair_sixHundredThirtyTwo : 0 < singularSeries (evenPair 632) :=
  singular_series_pos_evenPair (by decide : Even 632)

theorem singular_series_pos_evenPair_sixHundredThirtyFour : 0 < singularSeries (evenPair 634) :=
  singular_series_pos_evenPair (by decide : Even 634)

theorem singular_series_pos_evenPair_sixHundredThirtySix : 0 < singularSeries (evenPair 636) :=
  singular_series_pos_evenPair (by decide : Even 636)

theorem singular_series_pos_evenPair_sixHundredThirtyEight : 0 < singularSeries (evenPair 638) :=
  singular_series_pos_evenPair (by decide : Even 638)

theorem singular_series_pos_evenPair_sixHundredForty : 0 < singularSeries (evenPair 640) :=
  singular_series_pos_evenPair (by decide : Even 640)

theorem singular_series_finite_pos_evenPair_sixHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 632) P :=
  singular_series_finite_pos_evenPair (by decide : Even 632) P

theorem singular_series_finite_pos_evenPair_sixHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 634) P :=
  singular_series_finite_pos_evenPair (by decide : Even 634) P

theorem singular_series_finite_pos_evenPair_sixHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 636) P :=
  singular_series_finite_pos_evenPair (by decide : Even 636) P

theorem singular_series_finite_pos_evenPair_sixHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 638) P :=
  singular_series_finite_pos_evenPair (by decide : Even 638) P

theorem singular_series_finite_pos_evenPair_sixHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 640) P :=
  singular_series_finite_pos_evenPair (by decide : Even 640) P

theorem nu_p_sixHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 632) p = if p = 2 ∨ p ∣ 632 then 1 else 2 :=
  nu_p_evenPair (by decide : (632 : ℕ) ≠ 0) (by decide : Even 632) hp

theorem nu_p_sixHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 634) p = if p = 2 ∨ p ∣ 634 then 1 else 2 :=
  nu_p_evenPair (by decide : (634 : ℕ) ≠ 0) (by decide : Even 634) hp

theorem nu_p_sixHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 636) p = if p = 2 ∨ p ∣ 636 then 1 else 2 :=
  nu_p_evenPair (by decide : (636 : ℕ) ≠ 0) (by decide : Even 636) hp

theorem nu_p_sixHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 638) p = if p = 2 ∨ p ∣ 638 then 1 else 2 :=
  nu_p_evenPair (by decide : (638 : ℕ) ≠ 0) (by decide : Even 638) hp

theorem nu_p_sixHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 640) p = if p = 2 ∨ p ∣ 640 then 1 else 2 :=
  nu_p_evenPair (by decide : (640 : ℕ) ≠ 0) (by decide : Even 640) hp

theorem nu_p_sixHundredThirtyTwo_two : nu_p (evenPair 632) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 632)

theorem localFactor_sixHundredThirtyTwo_two : localFactor (evenPair 632) 2 = 2 :=
  localFactor_evenPair_two (by decide : (632 : ℕ) ≠ 0) (by decide : Even 632)

theorem nu_p_sixHundredForty_two : nu_p (evenPair 640) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 640)

theorem localFactor_sixHundredForty_two : localFactor (evenPair 640) 2 = 2 :=
  localFactor_evenPair_two (by decide : (640 : ℕ) ≠ 0) (by decide : Even 640)

end Brockian.SingularSeries.Gaps632640
