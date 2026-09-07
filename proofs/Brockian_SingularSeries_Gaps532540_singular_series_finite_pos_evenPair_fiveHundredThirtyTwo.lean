/-
  Brockian/SingularSeriesGaps532540.lean — even binary gaps n ∈ {532, 534, 536, 538, 540}.

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

namespace Brockian.SingularSeries.Gaps532540

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiveHundredThirtyTwo : (evenPair 532).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (532 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredThirtyFour : (evenPair 534).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (534 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredThirtySix : (evenPair 536).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (536 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredThirtyEight : (evenPair 538).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (538 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredForty : (evenPair 540).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (540 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiveHundredThirtyTwo : IsAdmissible (evenPair 532) :=
  isAdmissible_evenPair (by decide : Even 532)

theorem isAdmissible_evenPair_fiveHundredThirtyFour : IsAdmissible (evenPair 534) :=
  isAdmissible_evenPair (by decide : Even 534)

theorem isAdmissible_evenPair_fiveHundredThirtySix : IsAdmissible (evenPair 536) :=
  isAdmissible_evenPair (by decide : Even 536)

theorem isAdmissible_evenPair_fiveHundredThirtyEight : IsAdmissible (evenPair 538) :=
  isAdmissible_evenPair (by decide : Even 538)

theorem isAdmissible_evenPair_fiveHundredForty : IsAdmissible (evenPair 540) :=
  isAdmissible_evenPair (by decide : Even 540)

theorem singular_series_pos_evenPair_fiveHundredThirtyTwo : 0 < singularSeries (evenPair 532) :=
  singular_series_pos_evenPair (by decide : Even 532)

theorem singular_series_pos_evenPair_fiveHundredThirtyFour : 0 < singularSeries (evenPair 534) :=
  singular_series_pos_evenPair (by decide : Even 534)

theorem singular_series_pos_evenPair_fiveHundredThirtySix : 0 < singularSeries (evenPair 536) :=
  singular_series_pos_evenPair (by decide : Even 536)

theorem singular_series_pos_evenPair_fiveHundredThirtyEight : 0 < singularSeries (evenPair 538) :=
  singular_series_pos_evenPair (by decide : Even 538)

theorem singular_series_pos_evenPair_fiveHundredForty : 0 < singularSeries (evenPair 540) :=
  singular_series_pos_evenPair (by decide : Even 540)

theorem singular_series_finite_pos_evenPair_fiveHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 532) P :=
  singular_series_finite_pos_evenPair (by decide : Even 532) P

theorem singular_series_finite_pos_evenPair_fiveHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 534) P :=
  singular_series_finite_pos_evenPair (by decide : Even 534) P

theorem singular_series_finite_pos_evenPair_fiveHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 536) P :=
  singular_series_finite_pos_evenPair (by decide : Even 536) P

theorem singular_series_finite_pos_evenPair_fiveHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 538) P :=
  singular_series_finite_pos_evenPair (by decide : Even 538) P

theorem singular_series_finite_pos_evenPair_fiveHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 540) P :=
  singular_series_finite_pos_evenPair (by decide : Even 540) P

theorem nu_p_fiveHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 532) p = if p = 2 ∨ p ∣ 532 then 1 else 2 :=
  nu_p_evenPair (by decide : (532 : ℕ) ≠ 0) (by decide : Even 532) hp

theorem nu_p_fiveHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 534) p = if p = 2 ∨ p ∣ 534 then 1 else 2 :=
  nu_p_evenPair (by decide : (534 : ℕ) ≠ 0) (by decide : Even 534) hp

theorem nu_p_fiveHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 536) p = if p = 2 ∨ p ∣ 536 then 1 else 2 :=
  nu_p_evenPair (by decide : (536 : ℕ) ≠ 0) (by decide : Even 536) hp

theorem nu_p_fiveHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 538) p = if p = 2 ∨ p ∣ 538 then 1 else 2 :=
  nu_p_evenPair (by decide : (538 : ℕ) ≠ 0) (by decide : Even 538) hp

theorem nu_p_fiveHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 540) p = if p = 2 ∨ p ∣ 540 then 1 else 2 :=
  nu_p_evenPair (by decide : (540 : ℕ) ≠ 0) (by decide : Even 540) hp

theorem nu_p_fiveHundredThirtyTwo_two : nu_p (evenPair 532) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 532)

theorem localFactor_fiveHundredThirtyTwo_two : localFactor (evenPair 532) 2 = 2 :=
  localFactor_evenPair_two (by decide : (532 : ℕ) ≠ 0) (by decide : Even 532)

theorem nu_p_fiveHundredForty_two : nu_p (evenPair 540) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 540)

theorem localFactor_fiveHundredForty_two : localFactor (evenPair 540) 2 = 2 :=
  localFactor_evenPair_two (by decide : (540 : ℕ) ≠ 0) (by decide : Even 540)

end Brockian.SingularSeries.Gaps532540
