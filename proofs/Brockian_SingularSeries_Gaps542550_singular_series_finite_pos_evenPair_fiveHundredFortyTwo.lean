/-
  Brockian/SingularSeriesGaps542550.lean — even binary gaps n ∈ {542, 544, 546, 548, 550}.

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

namespace Brockian.SingularSeries.Gaps542550

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiveHundredFortyTwo : (evenPair 542).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (542 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredFortyFour : (evenPair 544).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (544 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredFortySix : (evenPair 546).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (546 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredFortyEight : (evenPair 548).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (548 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredFifty : (evenPair 550).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (550 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiveHundredFortyTwo : IsAdmissible (evenPair 542) :=
  isAdmissible_evenPair (by decide : Even 542)

theorem isAdmissible_evenPair_fiveHundredFortyFour : IsAdmissible (evenPair 544) :=
  isAdmissible_evenPair (by decide : Even 544)

theorem isAdmissible_evenPair_fiveHundredFortySix : IsAdmissible (evenPair 546) :=
  isAdmissible_evenPair (by decide : Even 546)

theorem isAdmissible_evenPair_fiveHundredFortyEight : IsAdmissible (evenPair 548) :=
  isAdmissible_evenPair (by decide : Even 548)

theorem isAdmissible_evenPair_fiveHundredFifty : IsAdmissible (evenPair 550) :=
  isAdmissible_evenPair (by decide : Even 550)

theorem singular_series_pos_evenPair_fiveHundredFortyTwo : 0 < singularSeries (evenPair 542) :=
  singular_series_pos_evenPair (by decide : Even 542)

theorem singular_series_pos_evenPair_fiveHundredFortyFour : 0 < singularSeries (evenPair 544) :=
  singular_series_pos_evenPair (by decide : Even 544)

theorem singular_series_pos_evenPair_fiveHundredFortySix : 0 < singularSeries (evenPair 546) :=
  singular_series_pos_evenPair (by decide : Even 546)

theorem singular_series_pos_evenPair_fiveHundredFortyEight : 0 < singularSeries (evenPair 548) :=
  singular_series_pos_evenPair (by decide : Even 548)

theorem singular_series_pos_evenPair_fiveHundredFifty : 0 < singularSeries (evenPair 550) :=
  singular_series_pos_evenPair (by decide : Even 550)

theorem singular_series_finite_pos_evenPair_fiveHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 542) P :=
  singular_series_finite_pos_evenPair (by decide : Even 542) P

theorem singular_series_finite_pos_evenPair_fiveHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 544) P :=
  singular_series_finite_pos_evenPair (by decide : Even 544) P

theorem singular_series_finite_pos_evenPair_fiveHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 546) P :=
  singular_series_finite_pos_evenPair (by decide : Even 546) P

theorem singular_series_finite_pos_evenPair_fiveHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 548) P :=
  singular_series_finite_pos_evenPair (by decide : Even 548) P

theorem singular_series_finite_pos_evenPair_fiveHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 550) P :=
  singular_series_finite_pos_evenPair (by decide : Even 550) P

theorem nu_p_fiveHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 542) p = if p = 2 ∨ p ∣ 542 then 1 else 2 :=
  nu_p_evenPair (by decide : (542 : ℕ) ≠ 0) (by decide : Even 542) hp

theorem nu_p_fiveHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 544) p = if p = 2 ∨ p ∣ 544 then 1 else 2 :=
  nu_p_evenPair (by decide : (544 : ℕ) ≠ 0) (by decide : Even 544) hp

theorem nu_p_fiveHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 546) p = if p = 2 ∨ p ∣ 546 then 1 else 2 :=
  nu_p_evenPair (by decide : (546 : ℕ) ≠ 0) (by decide : Even 546) hp

theorem nu_p_fiveHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 548) p = if p = 2 ∨ p ∣ 548 then 1 else 2 :=
  nu_p_evenPair (by decide : (548 : ℕ) ≠ 0) (by decide : Even 548) hp

theorem nu_p_fiveHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 550) p = if p = 2 ∨ p ∣ 550 then 1 else 2 :=
  nu_p_evenPair (by decide : (550 : ℕ) ≠ 0) (by decide : Even 550) hp

theorem nu_p_fiveHundredFortyTwo_two : nu_p (evenPair 542) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 542)

theorem localFactor_fiveHundredFortyTwo_two : localFactor (evenPair 542) 2 = 2 :=
  localFactor_evenPair_two (by decide : (542 : ℕ) ≠ 0) (by decide : Even 542)

theorem nu_p_fiveHundredFifty_two : nu_p (evenPair 550) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 550)

theorem localFactor_fiveHundredFifty_two : localFactor (evenPair 550) 2 = 2 :=
  localFactor_evenPair_two (by decide : (550 : ℕ) ≠ 0) (by decide : Even 550)

end Brockian.SingularSeries.Gaps542550
