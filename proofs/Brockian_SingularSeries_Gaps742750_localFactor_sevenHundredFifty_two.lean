/-
  Brockian/SingularSeriesGaps742750.lean — even binary gaps n ∈ {742, 744, 746, 748, 750}.

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

namespace Brockian.SingularSeries.Gaps742750

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sevenHundredFortyTwo : (evenPair 742).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (742 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredFortyFour : (evenPair 744).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (744 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredFortySix : (evenPair 746).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (746 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredFortyEight : (evenPair 748).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (748 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredFifty : (evenPair 750).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (750 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sevenHundredFortyTwo : IsAdmissible (evenPair 742) :=
  isAdmissible_evenPair (by decide : Even 742)

theorem isAdmissible_evenPair_sevenHundredFortyFour : IsAdmissible (evenPair 744) :=
  isAdmissible_evenPair (by decide : Even 744)

theorem isAdmissible_evenPair_sevenHundredFortySix : IsAdmissible (evenPair 746) :=
  isAdmissible_evenPair (by decide : Even 746)

theorem isAdmissible_evenPair_sevenHundredFortyEight : IsAdmissible (evenPair 748) :=
  isAdmissible_evenPair (by decide : Even 748)

theorem isAdmissible_evenPair_sevenHundredFifty : IsAdmissible (evenPair 750) :=
  isAdmissible_evenPair (by decide : Even 750)

theorem singular_series_pos_evenPair_sevenHundredFortyTwo : 0 < singularSeries (evenPair 742) :=
  singular_series_pos_evenPair (by decide : Even 742)

theorem singular_series_pos_evenPair_sevenHundredFortyFour : 0 < singularSeries (evenPair 744) :=
  singular_series_pos_evenPair (by decide : Even 744)

theorem singular_series_pos_evenPair_sevenHundredFortySix : 0 < singularSeries (evenPair 746) :=
  singular_series_pos_evenPair (by decide : Even 746)

theorem singular_series_pos_evenPair_sevenHundredFortyEight : 0 < singularSeries (evenPair 748) :=
  singular_series_pos_evenPair (by decide : Even 748)

theorem singular_series_pos_evenPair_sevenHundredFifty : 0 < singularSeries (evenPair 750) :=
  singular_series_pos_evenPair (by decide : Even 750)

theorem singular_series_finite_pos_evenPair_sevenHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 742) P :=
  singular_series_finite_pos_evenPair (by decide : Even 742) P

theorem singular_series_finite_pos_evenPair_sevenHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 744) P :=
  singular_series_finite_pos_evenPair (by decide : Even 744) P

theorem singular_series_finite_pos_evenPair_sevenHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 746) P :=
  singular_series_finite_pos_evenPair (by decide : Even 746) P

theorem singular_series_finite_pos_evenPair_sevenHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 748) P :=
  singular_series_finite_pos_evenPair (by decide : Even 748) P

theorem singular_series_finite_pos_evenPair_sevenHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 750) P :=
  singular_series_finite_pos_evenPair (by decide : Even 750) P

theorem nu_p_sevenHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 742) p = if p = 2 ∨ p ∣ 742 then 1 else 2 :=
  nu_p_evenPair (by decide : (742 : ℕ) ≠ 0) (by decide : Even 742) hp

theorem nu_p_sevenHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 744) p = if p = 2 ∨ p ∣ 744 then 1 else 2 :=
  nu_p_evenPair (by decide : (744 : ℕ) ≠ 0) (by decide : Even 744) hp

theorem nu_p_sevenHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 746) p = if p = 2 ∨ p ∣ 746 then 1 else 2 :=
  nu_p_evenPair (by decide : (746 : ℕ) ≠ 0) (by decide : Even 746) hp

theorem nu_p_sevenHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 748) p = if p = 2 ∨ p ∣ 748 then 1 else 2 :=
  nu_p_evenPair (by decide : (748 : ℕ) ≠ 0) (by decide : Even 748) hp

theorem nu_p_sevenHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 750) p = if p = 2 ∨ p ∣ 750 then 1 else 2 :=
  nu_p_evenPair (by decide : (750 : ℕ) ≠ 0) (by decide : Even 750) hp

theorem nu_p_sevenHundredFortyTwo_two : nu_p (evenPair 742) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 742)

theorem localFactor_sevenHundredFortyTwo_two : localFactor (evenPair 742) 2 = 2 :=
  localFactor_evenPair_two (by decide : (742 : ℕ) ≠ 0) (by decide : Even 742)

theorem nu_p_sevenHundredFifty_two : nu_p (evenPair 750) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 750)

theorem localFactor_sevenHundredFifty_two : localFactor (evenPair 750) 2 = 2 :=
  localFactor_evenPair_two (by decide : (750 : ℕ) ≠ 0) (by decide : Even 750)

end Brockian.SingularSeries.Gaps742750
