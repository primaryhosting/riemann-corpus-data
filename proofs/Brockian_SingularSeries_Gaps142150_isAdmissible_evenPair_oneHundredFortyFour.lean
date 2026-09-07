/-
  Brockian/SingularSeriesGaps142150.lean — even binary gaps n ∈ {142, 144, 146, 148, 150}.

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

namespace Brockian.SingularSeries.Gaps142150

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneHundredFortyTwo : (evenPair 142).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (142 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredFortyFour : (evenPair 144).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (144 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredFortySix : (evenPair 146).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (146 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredFortyEight : (evenPair 148).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (148 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredFifty : (evenPair 150).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (150 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneHundredFortyTwo : IsAdmissible (evenPair 142) :=
  isAdmissible_evenPair (by decide : Even 142)

theorem isAdmissible_evenPair_oneHundredFortyFour : IsAdmissible (evenPair 144) :=
  isAdmissible_evenPair (by decide : Even 144)

theorem isAdmissible_evenPair_oneHundredFortySix : IsAdmissible (evenPair 146) :=
  isAdmissible_evenPair (by decide : Even 146)

theorem isAdmissible_evenPair_oneHundredFortyEight : IsAdmissible (evenPair 148) :=
  isAdmissible_evenPair (by decide : Even 148)

theorem isAdmissible_evenPair_oneHundredFifty : IsAdmissible (evenPair 150) :=
  isAdmissible_evenPair (by decide : Even 150)

theorem singular_series_pos_evenPair_oneHundredFortyTwo : 0 < singularSeries (evenPair 142) :=
  singular_series_pos_evenPair (by decide : Even 142)

theorem singular_series_pos_evenPair_oneHundredFortyFour : 0 < singularSeries (evenPair 144) :=
  singular_series_pos_evenPair (by decide : Even 144)

theorem singular_series_pos_evenPair_oneHundredFortySix : 0 < singularSeries (evenPair 146) :=
  singular_series_pos_evenPair (by decide : Even 146)

theorem singular_series_pos_evenPair_oneHundredFortyEight : 0 < singularSeries (evenPair 148) :=
  singular_series_pos_evenPair (by decide : Even 148)

theorem singular_series_pos_evenPair_oneHundredFifty : 0 < singularSeries (evenPair 150) :=
  singular_series_pos_evenPair (by decide : Even 150)

theorem singular_series_finite_pos_evenPair_oneHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 142) P :=
  singular_series_finite_pos_evenPair (by decide : Even 142) P

theorem singular_series_finite_pos_evenPair_oneHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 144) P :=
  singular_series_finite_pos_evenPair (by decide : Even 144) P

theorem singular_series_finite_pos_evenPair_oneHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 146) P :=
  singular_series_finite_pos_evenPair (by decide : Even 146) P

theorem singular_series_finite_pos_evenPair_oneHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 148) P :=
  singular_series_finite_pos_evenPair (by decide : Even 148) P

theorem singular_series_finite_pos_evenPair_oneHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 150) P :=
  singular_series_finite_pos_evenPair (by decide : Even 150) P

theorem nu_p_oneHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 142) p = if p = 2 ∨ p ∣ 142 then 1 else 2 :=
  nu_p_evenPair (by decide : (142 : ℕ) ≠ 0) (by decide : Even 142) hp

theorem nu_p_oneHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 144) p = if p = 2 ∨ p ∣ 144 then 1 else 2 :=
  nu_p_evenPair (by decide : (144 : ℕ) ≠ 0) (by decide : Even 144) hp

theorem nu_p_oneHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 146) p = if p = 2 ∨ p ∣ 146 then 1 else 2 :=
  nu_p_evenPair (by decide : (146 : ℕ) ≠ 0) (by decide : Even 146) hp

theorem nu_p_oneHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 148) p = if p = 2 ∨ p ∣ 148 then 1 else 2 :=
  nu_p_evenPair (by decide : (148 : ℕ) ≠ 0) (by decide : Even 148) hp

theorem nu_p_oneHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 150) p = if p = 2 ∨ p ∣ 150 then 1 else 2 :=
  nu_p_evenPair (by decide : (150 : ℕ) ≠ 0) (by decide : Even 150) hp

theorem nu_p_oneHundredFortyTwo_two : nu_p (evenPair 142) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 142)

theorem localFactor_oneHundredFortyTwo_two : localFactor (evenPair 142) 2 = 2 :=
  localFactor_evenPair_two (by decide : (142 : ℕ) ≠ 0) (by decide : Even 142)

theorem nu_p_oneHundredFifty_two : nu_p (evenPair 150) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 150)

theorem localFactor_oneHundredFifty_two : localFactor (evenPair 150) 2 = 2 :=
  localFactor_evenPair_two (by decide : (150 : ℕ) ≠ 0) (by decide : Even 150)

end Brockian.SingularSeries.Gaps142150
