/-
  Brockian/SingularSeriesGaps442450.lean — even binary gaps n ∈ {442, 444, 446, 448, 450}.

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

namespace Brockian.SingularSeries.Gaps442450

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fourHundredFortyTwo : (evenPair 442).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (442 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredFortyFour : (evenPair 444).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (444 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredFortySix : (evenPair 446).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (446 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredFortyEight : (evenPair 448).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (448 : ℕ) ≠ 0)

theorem evenPair_card_fourHundredFifty : (evenPair 450).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (450 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fourHundredFortyTwo : IsAdmissible (evenPair 442) :=
  isAdmissible_evenPair (by decide : Even 442)

theorem isAdmissible_evenPair_fourHundredFortyFour : IsAdmissible (evenPair 444) :=
  isAdmissible_evenPair (by decide : Even 444)

theorem isAdmissible_evenPair_fourHundredFortySix : IsAdmissible (evenPair 446) :=
  isAdmissible_evenPair (by decide : Even 446)

theorem isAdmissible_evenPair_fourHundredFortyEight : IsAdmissible (evenPair 448) :=
  isAdmissible_evenPair (by decide : Even 448)

theorem isAdmissible_evenPair_fourHundredFifty : IsAdmissible (evenPair 450) :=
  isAdmissible_evenPair (by decide : Even 450)

theorem singular_series_pos_evenPair_fourHundredFortyTwo : 0 < singularSeries (evenPair 442) :=
  singular_series_pos_evenPair (by decide : Even 442)

theorem singular_series_pos_evenPair_fourHundredFortyFour : 0 < singularSeries (evenPair 444) :=
  singular_series_pos_evenPair (by decide : Even 444)

theorem singular_series_pos_evenPair_fourHundredFortySix : 0 < singularSeries (evenPair 446) :=
  singular_series_pos_evenPair (by decide : Even 446)

theorem singular_series_pos_evenPair_fourHundredFortyEight : 0 < singularSeries (evenPair 448) :=
  singular_series_pos_evenPair (by decide : Even 448)

theorem singular_series_pos_evenPair_fourHundredFifty : 0 < singularSeries (evenPair 450) :=
  singular_series_pos_evenPair (by decide : Even 450)

theorem singular_series_finite_pos_evenPair_fourHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 442) P :=
  singular_series_finite_pos_evenPair (by decide : Even 442) P

theorem singular_series_finite_pos_evenPair_fourHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 444) P :=
  singular_series_finite_pos_evenPair (by decide : Even 444) P

theorem singular_series_finite_pos_evenPair_fourHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 446) P :=
  singular_series_finite_pos_evenPair (by decide : Even 446) P

theorem singular_series_finite_pos_evenPair_fourHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 448) P :=
  singular_series_finite_pos_evenPair (by decide : Even 448) P

theorem singular_series_finite_pos_evenPair_fourHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 450) P :=
  singular_series_finite_pos_evenPair (by decide : Even 450) P

theorem nu_p_fourHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 442) p = if p = 2 ∨ p ∣ 442 then 1 else 2 :=
  nu_p_evenPair (by decide : (442 : ℕ) ≠ 0) (by decide : Even 442) hp

theorem nu_p_fourHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 444) p = if p = 2 ∨ p ∣ 444 then 1 else 2 :=
  nu_p_evenPair (by decide : (444 : ℕ) ≠ 0) (by decide : Even 444) hp

theorem nu_p_fourHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 446) p = if p = 2 ∨ p ∣ 446 then 1 else 2 :=
  nu_p_evenPair (by decide : (446 : ℕ) ≠ 0) (by decide : Even 446) hp

theorem nu_p_fourHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 448) p = if p = 2 ∨ p ∣ 448 then 1 else 2 :=
  nu_p_evenPair (by decide : (448 : ℕ) ≠ 0) (by decide : Even 448) hp

theorem nu_p_fourHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 450) p = if p = 2 ∨ p ∣ 450 then 1 else 2 :=
  nu_p_evenPair (by decide : (450 : ℕ) ≠ 0) (by decide : Even 450) hp

theorem nu_p_fourHundredFortyTwo_two : nu_p (evenPair 442) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 442)

theorem localFactor_fourHundredFortyTwo_two : localFactor (evenPair 442) 2 = 2 :=
  localFactor_evenPair_two (by decide : (442 : ℕ) ≠ 0) (by decide : Even 442)

theorem nu_p_fourHundredFifty_two : nu_p (evenPair 450) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 450)

theorem localFactor_fourHundredFifty_two : localFactor (evenPair 450) 2 = 2 :=
  localFactor_evenPair_two (by decide : (450 : ℕ) ≠ 0) (by decide : Even 450)

end Brockian.SingularSeries.Gaps442450
