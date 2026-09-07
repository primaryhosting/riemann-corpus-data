/-
  Brockian/SingularSeriesGaps692700.lean — even binary gaps n ∈ {692, 694, 696, 698, 700}.

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

namespace Brockian.SingularSeries.Gaps692700

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixHundredNinetyTwo : (evenPair 692).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (692 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredNinetyFour : (evenPair 694).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (694 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredNinetySix : (evenPair 696).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (696 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredNinetyEight : (evenPair 698).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (698 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundred : (evenPair 700).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (700 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixHundredNinetyTwo : IsAdmissible (evenPair 692) :=
  isAdmissible_evenPair (by decide : Even 692)

theorem isAdmissible_evenPair_sixHundredNinetyFour : IsAdmissible (evenPair 694) :=
  isAdmissible_evenPair (by decide : Even 694)

theorem isAdmissible_evenPair_sixHundredNinetySix : IsAdmissible (evenPair 696) :=
  isAdmissible_evenPair (by decide : Even 696)

theorem isAdmissible_evenPair_sixHundredNinetyEight : IsAdmissible (evenPair 698) :=
  isAdmissible_evenPair (by decide : Even 698)

theorem isAdmissible_evenPair_sevenHundred : IsAdmissible (evenPair 700) :=
  isAdmissible_evenPair (by decide : Even 700)

theorem singular_series_pos_evenPair_sixHundredNinetyTwo : 0 < singularSeries (evenPair 692) :=
  singular_series_pos_evenPair (by decide : Even 692)

theorem singular_series_pos_evenPair_sixHundredNinetyFour : 0 < singularSeries (evenPair 694) :=
  singular_series_pos_evenPair (by decide : Even 694)

theorem singular_series_pos_evenPair_sixHundredNinetySix : 0 < singularSeries (evenPair 696) :=
  singular_series_pos_evenPair (by decide : Even 696)

theorem singular_series_pos_evenPair_sixHundredNinetyEight : 0 < singularSeries (evenPair 698) :=
  singular_series_pos_evenPair (by decide : Even 698)

theorem singular_series_pos_evenPair_sevenHundred : 0 < singularSeries (evenPair 700) :=
  singular_series_pos_evenPair (by decide : Even 700)

theorem singular_series_finite_pos_evenPair_sixHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 692) P :=
  singular_series_finite_pos_evenPair (by decide : Even 692) P

theorem singular_series_finite_pos_evenPair_sixHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 694) P :=
  singular_series_finite_pos_evenPair (by decide : Even 694) P

theorem singular_series_finite_pos_evenPair_sixHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 696) P :=
  singular_series_finite_pos_evenPair (by decide : Even 696) P

theorem singular_series_finite_pos_evenPair_sixHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 698) P :=
  singular_series_finite_pos_evenPair (by decide : Even 698) P

theorem singular_series_finite_pos_evenPair_sevenHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 700) P :=
  singular_series_finite_pos_evenPair (by decide : Even 700) P

theorem nu_p_sixHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 692) p = if p = 2 ∨ p ∣ 692 then 1 else 2 :=
  nu_p_evenPair (by decide : (692 : ℕ) ≠ 0) (by decide : Even 692) hp

theorem nu_p_sixHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 694) p = if p = 2 ∨ p ∣ 694 then 1 else 2 :=
  nu_p_evenPair (by decide : (694 : ℕ) ≠ 0) (by decide : Even 694) hp

theorem nu_p_sixHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 696) p = if p = 2 ∨ p ∣ 696 then 1 else 2 :=
  nu_p_evenPair (by decide : (696 : ℕ) ≠ 0) (by decide : Even 696) hp

theorem nu_p_sixHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 698) p = if p = 2 ∨ p ∣ 698 then 1 else 2 :=
  nu_p_evenPair (by decide : (698 : ℕ) ≠ 0) (by decide : Even 698) hp

theorem nu_p_sevenHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 700) p = if p = 2 ∨ p ∣ 700 then 1 else 2 :=
  nu_p_evenPair (by decide : (700 : ℕ) ≠ 0) (by decide : Even 700) hp

theorem nu_p_sixHundredNinetyTwo_two : nu_p (evenPair 692) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 692)

theorem localFactor_sixHundredNinetyTwo_two : localFactor (evenPair 692) 2 = 2 :=
  localFactor_evenPair_two (by decide : (692 : ℕ) ≠ 0) (by decide : Even 692)

theorem nu_p_sevenHundred_two : nu_p (evenPair 700) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 700)

theorem localFactor_sevenHundred_two : localFactor (evenPair 700) 2 = 2 :=
  localFactor_evenPair_two (by decide : (700 : ℕ) ≠ 0) (by decide : Even 700)

end Brockian.SingularSeries.Gaps692700
