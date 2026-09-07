/-
  Brockian/SingularSeriesGaps792800.lean — even binary gaps n ∈ {792, 794, 796, 798, 800}.

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

namespace Brockian.SingularSeries.Gaps792800

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sevenHundredNinetyTwo : (evenPair 792).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (792 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredNinetyFour : (evenPair 794).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (794 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredNinetySix : (evenPair 796).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (796 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredNinetyEight : (evenPair 798).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (798 : ℕ) ≠ 0)

theorem evenPair_card_eightHundred : (evenPair 800).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (800 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sevenHundredNinetyTwo : IsAdmissible (evenPair 792) :=
  isAdmissible_evenPair (by decide : Even 792)

theorem isAdmissible_evenPair_sevenHundredNinetyFour : IsAdmissible (evenPair 794) :=
  isAdmissible_evenPair (by decide : Even 794)

theorem isAdmissible_evenPair_sevenHundredNinetySix : IsAdmissible (evenPair 796) :=
  isAdmissible_evenPair (by decide : Even 796)

theorem isAdmissible_evenPair_sevenHundredNinetyEight : IsAdmissible (evenPair 798) :=
  isAdmissible_evenPair (by decide : Even 798)

theorem isAdmissible_evenPair_eightHundred : IsAdmissible (evenPair 800) :=
  isAdmissible_evenPair (by decide : Even 800)

theorem singular_series_pos_evenPair_sevenHundredNinetyTwo : 0 < singularSeries (evenPair 792) :=
  singular_series_pos_evenPair (by decide : Even 792)

theorem singular_series_pos_evenPair_sevenHundredNinetyFour : 0 < singularSeries (evenPair 794) :=
  singular_series_pos_evenPair (by decide : Even 794)

theorem singular_series_pos_evenPair_sevenHundredNinetySix : 0 < singularSeries (evenPair 796) :=
  singular_series_pos_evenPair (by decide : Even 796)

theorem singular_series_pos_evenPair_sevenHundredNinetyEight : 0 < singularSeries (evenPair 798) :=
  singular_series_pos_evenPair (by decide : Even 798)

theorem singular_series_pos_evenPair_eightHundred : 0 < singularSeries (evenPair 800) :=
  singular_series_pos_evenPair (by decide : Even 800)

theorem singular_series_finite_pos_evenPair_sevenHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 792) P :=
  singular_series_finite_pos_evenPair (by decide : Even 792) P

theorem singular_series_finite_pos_evenPair_sevenHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 794) P :=
  singular_series_finite_pos_evenPair (by decide : Even 794) P

theorem singular_series_finite_pos_evenPair_sevenHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 796) P :=
  singular_series_finite_pos_evenPair (by decide : Even 796) P

theorem singular_series_finite_pos_evenPair_sevenHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 798) P :=
  singular_series_finite_pos_evenPair (by decide : Even 798) P

theorem singular_series_finite_pos_evenPair_eightHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 800) P :=
  singular_series_finite_pos_evenPair (by decide : Even 800) P

theorem nu_p_sevenHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 792) p = if p = 2 ∨ p ∣ 792 then 1 else 2 :=
  nu_p_evenPair (by decide : (792 : ℕ) ≠ 0) (by decide : Even 792) hp

theorem nu_p_sevenHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 794) p = if p = 2 ∨ p ∣ 794 then 1 else 2 :=
  nu_p_evenPair (by decide : (794 : ℕ) ≠ 0) (by decide : Even 794) hp

theorem nu_p_sevenHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 796) p = if p = 2 ∨ p ∣ 796 then 1 else 2 :=
  nu_p_evenPair (by decide : (796 : ℕ) ≠ 0) (by decide : Even 796) hp

theorem nu_p_sevenHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 798) p = if p = 2 ∨ p ∣ 798 then 1 else 2 :=
  nu_p_evenPair (by decide : (798 : ℕ) ≠ 0) (by decide : Even 798) hp

theorem nu_p_eightHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 800) p = if p = 2 ∨ p ∣ 800 then 1 else 2 :=
  nu_p_evenPair (by decide : (800 : ℕ) ≠ 0) (by decide : Even 800) hp

theorem nu_p_sevenHundredNinetyTwo_two : nu_p (evenPair 792) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 792)

theorem localFactor_sevenHundredNinetyTwo_two : localFactor (evenPair 792) 2 = 2 :=
  localFactor_evenPair_two (by decide : (792 : ℕ) ≠ 0) (by decide : Even 792)

theorem nu_p_eightHundred_two : nu_p (evenPair 800) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 800)

theorem localFactor_eightHundred_two : localFactor (evenPair 800) 2 = 2 :=
  localFactor_evenPair_two (by decide : (800 : ℕ) ≠ 0) (by decide : Even 800)

end Brockian.SingularSeries.Gaps792800
