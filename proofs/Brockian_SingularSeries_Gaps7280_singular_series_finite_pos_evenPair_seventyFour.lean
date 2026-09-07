/-
  Brockian/SingularSeriesGaps7280.lean — even binary gaps n ∈ {72, 74, 76, 78, 80}.

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

namespace Brockian.SingularSeries.Gaps7280

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_seventyTwo : (evenPair 72).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (72 : ℕ) ≠ 0)

theorem evenPair_card_seventyFour : (evenPair 74).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (74 : ℕ) ≠ 0)

theorem evenPair_card_seventySix : (evenPair 76).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (76 : ℕ) ≠ 0)

theorem evenPair_card_seventyEight : (evenPair 78).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (78 : ℕ) ≠ 0)

theorem evenPair_card_eighty : (evenPair 80).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (80 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_seventyTwo : IsAdmissible (evenPair 72) :=
  isAdmissible_evenPair (by decide : Even 72)

theorem isAdmissible_evenPair_seventyFour : IsAdmissible (evenPair 74) :=
  isAdmissible_evenPair (by decide : Even 74)

theorem isAdmissible_evenPair_seventySix : IsAdmissible (evenPair 76) :=
  isAdmissible_evenPair (by decide : Even 76)

theorem isAdmissible_evenPair_seventyEight : IsAdmissible (evenPair 78) :=
  isAdmissible_evenPair (by decide : Even 78)

theorem isAdmissible_evenPair_eighty : IsAdmissible (evenPair 80) :=
  isAdmissible_evenPair (by decide : Even 80)

theorem singular_series_pos_evenPair_seventyTwo : 0 < singularSeries (evenPair 72) :=
  singular_series_pos_evenPair (by decide : Even 72)

theorem singular_series_pos_evenPair_seventyFour : 0 < singularSeries (evenPair 74) :=
  singular_series_pos_evenPair (by decide : Even 74)

theorem singular_series_pos_evenPair_seventySix : 0 < singularSeries (evenPair 76) :=
  singular_series_pos_evenPair (by decide : Even 76)

theorem singular_series_pos_evenPair_seventyEight : 0 < singularSeries (evenPair 78) :=
  singular_series_pos_evenPair (by decide : Even 78)

theorem singular_series_pos_evenPair_eighty : 0 < singularSeries (evenPair 80) :=
  singular_series_pos_evenPair (by decide : Even 80)

theorem singular_series_finite_pos_evenPair_seventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 72) P :=
  singular_series_finite_pos_evenPair (by decide : Even 72) P

theorem singular_series_finite_pos_evenPair_seventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 74) P :=
  singular_series_finite_pos_evenPair (by decide : Even 74) P

theorem singular_series_finite_pos_evenPair_seventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 76) P :=
  singular_series_finite_pos_evenPair (by decide : Even 76) P

theorem singular_series_finite_pos_evenPair_seventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 78) P :=
  singular_series_finite_pos_evenPair (by decide : Even 78) P

theorem singular_series_finite_pos_evenPair_eighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 80) P :=
  singular_series_finite_pos_evenPair (by decide : Even 80) P

theorem nu_p_seventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 72) p = if p = 2 ∨ p ∣ 72 then 1 else 2 :=
  nu_p_evenPair (by decide : (72 : ℕ) ≠ 0) (by decide : Even 72) hp

theorem nu_p_seventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 74) p = if p = 2 ∨ p ∣ 74 then 1 else 2 :=
  nu_p_evenPair (by decide : (74 : ℕ) ≠ 0) (by decide : Even 74) hp

theorem nu_p_seventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 76) p = if p = 2 ∨ p ∣ 76 then 1 else 2 :=
  nu_p_evenPair (by decide : (76 : ℕ) ≠ 0) (by decide : Even 76) hp

theorem nu_p_seventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 78) p = if p = 2 ∨ p ∣ 78 then 1 else 2 :=
  nu_p_evenPair (by decide : (78 : ℕ) ≠ 0) (by decide : Even 78) hp

theorem nu_p_eighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 80) p = if p = 2 ∨ p ∣ 80 then 1 else 2 :=
  nu_p_evenPair (by decide : (80 : ℕ) ≠ 0) (by decide : Even 80) hp

theorem nu_p_seventyTwo_two : nu_p (evenPair 72) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 72)

theorem localFactor_seventyTwo_two : localFactor (evenPair 72) 2 = 2 :=
  localFactor_evenPair_two (by decide : (72 : ℕ) ≠ 0) (by decide : Even 72)

theorem nu_p_eighty_two : nu_p (evenPair 80) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 80)

theorem localFactor_eighty_two : localFactor (evenPair 80) 2 = 2 :=
  localFactor_evenPair_two (by decide : (80 : ℕ) ≠ 0) (by decide : Even 80)

end Brockian.SingularSeries.Gaps7280
