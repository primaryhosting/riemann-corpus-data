/-
  Brockian/SingularSeriesGaps642650.lean — even binary gaps n ∈ {642, 644, 646, 648, 650}.

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

namespace Brockian.SingularSeries.Gaps642650

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixHundredFortyTwo : (evenPair 642).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (642 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredFortyFour : (evenPair 644).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (644 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredFortySix : (evenPair 646).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (646 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredFortyEight : (evenPair 648).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (648 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredFifty : (evenPair 650).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (650 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixHundredFortyTwo : IsAdmissible (evenPair 642) :=
  isAdmissible_evenPair (by decide : Even 642)

theorem isAdmissible_evenPair_sixHundredFortyFour : IsAdmissible (evenPair 644) :=
  isAdmissible_evenPair (by decide : Even 644)

theorem isAdmissible_evenPair_sixHundredFortySix : IsAdmissible (evenPair 646) :=
  isAdmissible_evenPair (by decide : Even 646)

theorem isAdmissible_evenPair_sixHundredFortyEight : IsAdmissible (evenPair 648) :=
  isAdmissible_evenPair (by decide : Even 648)

theorem isAdmissible_evenPair_sixHundredFifty : IsAdmissible (evenPair 650) :=
  isAdmissible_evenPair (by decide : Even 650)

theorem singular_series_pos_evenPair_sixHundredFortyTwo : 0 < singularSeries (evenPair 642) :=
  singular_series_pos_evenPair (by decide : Even 642)

theorem singular_series_pos_evenPair_sixHundredFortyFour : 0 < singularSeries (evenPair 644) :=
  singular_series_pos_evenPair (by decide : Even 644)

theorem singular_series_pos_evenPair_sixHundredFortySix : 0 < singularSeries (evenPair 646) :=
  singular_series_pos_evenPair (by decide : Even 646)

theorem singular_series_pos_evenPair_sixHundredFortyEight : 0 < singularSeries (evenPair 648) :=
  singular_series_pos_evenPair (by decide : Even 648)

theorem singular_series_pos_evenPair_sixHundredFifty : 0 < singularSeries (evenPair 650) :=
  singular_series_pos_evenPair (by decide : Even 650)

theorem singular_series_finite_pos_evenPair_sixHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 642) P :=
  singular_series_finite_pos_evenPair (by decide : Even 642) P

theorem singular_series_finite_pos_evenPair_sixHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 644) P :=
  singular_series_finite_pos_evenPair (by decide : Even 644) P

theorem singular_series_finite_pos_evenPair_sixHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 646) P :=
  singular_series_finite_pos_evenPair (by decide : Even 646) P

theorem singular_series_finite_pos_evenPair_sixHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 648) P :=
  singular_series_finite_pos_evenPair (by decide : Even 648) P

theorem singular_series_finite_pos_evenPair_sixHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 650) P :=
  singular_series_finite_pos_evenPair (by decide : Even 650) P

theorem nu_p_sixHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 642) p = if p = 2 ∨ p ∣ 642 then 1 else 2 :=
  nu_p_evenPair (by decide : (642 : ℕ) ≠ 0) (by decide : Even 642) hp

theorem nu_p_sixHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 644) p = if p = 2 ∨ p ∣ 644 then 1 else 2 :=
  nu_p_evenPair (by decide : (644 : ℕ) ≠ 0) (by decide : Even 644) hp

theorem nu_p_sixHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 646) p = if p = 2 ∨ p ∣ 646 then 1 else 2 :=
  nu_p_evenPair (by decide : (646 : ℕ) ≠ 0) (by decide : Even 646) hp

theorem nu_p_sixHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 648) p = if p = 2 ∨ p ∣ 648 then 1 else 2 :=
  nu_p_evenPair (by decide : (648 : ℕ) ≠ 0) (by decide : Even 648) hp

theorem nu_p_sixHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 650) p = if p = 2 ∨ p ∣ 650 then 1 else 2 :=
  nu_p_evenPair (by decide : (650 : ℕ) ≠ 0) (by decide : Even 650) hp

theorem nu_p_sixHundredFortyTwo_two : nu_p (evenPair 642) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 642)

theorem localFactor_sixHundredFortyTwo_two : localFactor (evenPair 642) 2 = 2 :=
  localFactor_evenPair_two (by decide : (642 : ℕ) ≠ 0) (by decide : Even 642)

theorem nu_p_sixHundredFifty_two : nu_p (evenPair 650) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 650)

theorem localFactor_sixHundredFifty_two : localFactor (evenPair 650) 2 = 2 :=
  localFactor_evenPair_two (by decide : (650 : ℕ) ≠ 0) (by decide : Even 650)

end Brockian.SingularSeries.Gaps642650
