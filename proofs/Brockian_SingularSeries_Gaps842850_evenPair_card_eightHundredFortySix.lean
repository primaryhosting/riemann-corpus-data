/-
  Brockian/SingularSeriesGaps842850.lean — even binary gaps n ∈ {842, 844, 846, 848, 850}.

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

namespace Brockian.SingularSeries.Gaps842850

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightHundredFortyTwo : (evenPair 842).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (842 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredFortyFour : (evenPair 844).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (844 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredFortySix : (evenPair 846).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (846 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredFortyEight : (evenPair 848).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (848 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredFifty : (evenPair 850).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (850 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightHundredFortyTwo : IsAdmissible (evenPair 842) :=
  isAdmissible_evenPair (by decide : Even 842)

theorem isAdmissible_evenPair_eightHundredFortyFour : IsAdmissible (evenPair 844) :=
  isAdmissible_evenPair (by decide : Even 844)

theorem isAdmissible_evenPair_eightHundredFortySix : IsAdmissible (evenPair 846) :=
  isAdmissible_evenPair (by decide : Even 846)

theorem isAdmissible_evenPair_eightHundredFortyEight : IsAdmissible (evenPair 848) :=
  isAdmissible_evenPair (by decide : Even 848)

theorem isAdmissible_evenPair_eightHundredFifty : IsAdmissible (evenPair 850) :=
  isAdmissible_evenPair (by decide : Even 850)

theorem singular_series_pos_evenPair_eightHundredFortyTwo : 0 < singularSeries (evenPair 842) :=
  singular_series_pos_evenPair (by decide : Even 842)

theorem singular_series_pos_evenPair_eightHundredFortyFour : 0 < singularSeries (evenPair 844) :=
  singular_series_pos_evenPair (by decide : Even 844)

theorem singular_series_pos_evenPair_eightHundredFortySix : 0 < singularSeries (evenPair 846) :=
  singular_series_pos_evenPair (by decide : Even 846)

theorem singular_series_pos_evenPair_eightHundredFortyEight : 0 < singularSeries (evenPair 848) :=
  singular_series_pos_evenPair (by decide : Even 848)

theorem singular_series_pos_evenPair_eightHundredFifty : 0 < singularSeries (evenPair 850) :=
  singular_series_pos_evenPair (by decide : Even 850)

theorem singular_series_finite_pos_evenPair_eightHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 842) P :=
  singular_series_finite_pos_evenPair (by decide : Even 842) P

theorem singular_series_finite_pos_evenPair_eightHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 844) P :=
  singular_series_finite_pos_evenPair (by decide : Even 844) P

theorem singular_series_finite_pos_evenPair_eightHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 846) P :=
  singular_series_finite_pos_evenPair (by decide : Even 846) P

theorem singular_series_finite_pos_evenPair_eightHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 848) P :=
  singular_series_finite_pos_evenPair (by decide : Even 848) P

theorem singular_series_finite_pos_evenPair_eightHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 850) P :=
  singular_series_finite_pos_evenPair (by decide : Even 850) P

theorem nu_p_eightHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 842) p = if p = 2 ∨ p ∣ 842 then 1 else 2 :=
  nu_p_evenPair (by decide : (842 : ℕ) ≠ 0) (by decide : Even 842) hp

theorem nu_p_eightHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 844) p = if p = 2 ∨ p ∣ 844 then 1 else 2 :=
  nu_p_evenPair (by decide : (844 : ℕ) ≠ 0) (by decide : Even 844) hp

theorem nu_p_eightHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 846) p = if p = 2 ∨ p ∣ 846 then 1 else 2 :=
  nu_p_evenPair (by decide : (846 : ℕ) ≠ 0) (by decide : Even 846) hp

theorem nu_p_eightHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 848) p = if p = 2 ∨ p ∣ 848 then 1 else 2 :=
  nu_p_evenPair (by decide : (848 : ℕ) ≠ 0) (by decide : Even 848) hp

theorem nu_p_eightHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 850) p = if p = 2 ∨ p ∣ 850 then 1 else 2 :=
  nu_p_evenPair (by decide : (850 : ℕ) ≠ 0) (by decide : Even 850) hp

theorem nu_p_eightHundredFortyTwo_two : nu_p (evenPair 842) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 842)

theorem localFactor_eightHundredFortyTwo_two : localFactor (evenPair 842) 2 = 2 :=
  localFactor_evenPair_two (by decide : (842 : ℕ) ≠ 0) (by decide : Even 842)

theorem nu_p_eightHundredFifty_two : nu_p (evenPair 850) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 850)

theorem localFactor_eightHundredFifty_two : localFactor (evenPair 850) 2 = 2 :=
  localFactor_evenPair_two (by decide : (850 : ℕ) ≠ 0) (by decide : Even 850)

end Brockian.SingularSeries.Gaps842850
