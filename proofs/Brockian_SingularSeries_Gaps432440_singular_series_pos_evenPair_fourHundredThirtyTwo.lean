/-
  Brockian/SingularSeriesGaps432440.lean — even binary gaps n ∈ {432, 434, 436, 438, 440}.

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

namespace Brockian.SingularSeries.Gaps432440

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fourHundredThirtyTwo : (evenPair 432).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (432 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredThirtyFour : (evenPair 434).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (434 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredThirtySix : (evenPair 436).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (436 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredThirtyEight : (evenPair 438).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (438 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredForty : (evenPair 440).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (440 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fourHundredThirtyTwo : IsAdmissible (evenPair 432) :=
  isAdmissible_evenPair (by decide : Even 432)

theorem isAdmissible_evenPair_fourHundredThirtyFour : IsAdmissible (evenPair 434) :=
  isAdmissible_evenPair (by decide : Even 434)

theorem isAdmissible_evenPair_fourHundredThirtySix : IsAdmissible (evenPair 436) :=
  isAdmissible_evenPair (by decide : Even 436)

theorem isAdmissible_evenPair_fourHundredThirtyEight : IsAdmissible (evenPair 438) :=
  isAdmissible_evenPair (by decide : Even 438)

theorem isAdmissible_evenPair_fourHundredForty : IsAdmissible (evenPair 440) :=
  isAdmissible_evenPair (by decide : Even 440)

theorem singular_series_pos_evenPair_fourHundredThirtyTwo : 0 < singularSeries (evenPair 432) :=
  singular_series_pos_evenPair (by decide : Even 432)

theorem singular_series_pos_evenPair_fourHundredThirtyFour : 0 < singularSeries (evenPair 434) :=
  singular_series_pos_evenPair (by decide : Even 434)

theorem singular_series_pos_evenPair_fourHundredThirtySix : 0 < singularSeries (evenPair 436) :=
  singular_series_pos_evenPair (by decide : Even 436)

theorem singular_series_pos_evenPair_fourHundredThirtyEight : 0 < singularSeries (evenPair 438) :=
  singular_series_pos_evenPair (by decide : Even 438)

theorem singular_series_pos_evenPair_fourHundredForty : 0 < singularSeries (evenPair 440) :=
  singular_series_pos_evenPair (by decide : Even 440)

theorem singular_series_finite_pos_evenPair_fourHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 432) P :=
  singular_series_finite_pos_evenPair (by decide : Even 432) P

theorem singular_series_finite_pos_evenPair_fourHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 434) P :=
  singular_series_finite_pos_evenPair (by decide : Even 434) P

theorem singular_series_finite_pos_evenPair_fourHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 436) P :=
  singular_series_finite_pos_evenPair (by decide : Even 436) P

theorem singular_series_finite_pos_evenPair_fourHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 438) P :=
  singular_series_finite_pos_evenPair (by decide : Even 438) P

theorem singular_series_finite_pos_evenPair_fourHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 440) P :=
  singular_series_finite_pos_evenPair (by decide : Even 440) P

theorem nu_p_fourHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 432) p = if p = 2 ∨ p ∣ 432 then 1 else 2 :=
  nu_p_evenPair (by decide : (432 : ℕ) ≠ 0) (by decide : Even 432) hp

theorem nu_p_fourHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 434) p = if p = 2 ∨ p ∣ 434 then 1 else 2 :=
  nu_p_evenPair (by decide : (434 : ℕ) ≠ 0) (by decide : Even 434) hp

theorem nu_p_fourHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 436) p = if p = 2 ∨ p ∣ 436 then 1 else 2 :=
  nu_p_evenPair (by decide : (436 : ℕ) ≠ 0) (by decide : Even 436) hp

theorem nu_p_fourHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 438) p = if p = 2 ∨ p ∣ 438 then 1 else 2 :=
  nu_p_evenPair (by decide : (438 : ℕ) ≠ 0) (by decide : Even 438) hp

theorem nu_p_fourHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 440) p = if p = 2 ∨ p ∣ 440 then 1 else 2 :=
  nu_p_evenPair (by decide : (440 : ℕ) ≠ 0) (by decide : Even 440) hp

theorem nu_p_fourHundredThirtyTwo_two : nu_p (evenPair 432) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 432)

theorem localFactor_fourHundredThirtyTwo_two : localFactor (evenPair 432) 2 = 2 :=
  localFactor_evenPair_two (by decide : (432 : ℕ) ≠ 0) (by decide : Even 432)

theorem nu_p_fourHundredForty_two : nu_p (evenPair 440) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 440)

theorem localFactor_fourHundredForty_two : localFactor (evenPair 440) 2 = 2 :=
  localFactor_evenPair_two (by decide : (440 : ℕ) ≠ 0) (by decide : Even 440)

end Brockian.SingularSeries.Gaps432440
