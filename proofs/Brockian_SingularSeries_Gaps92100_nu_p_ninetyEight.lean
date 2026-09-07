/-
  Brockian/SingularSeriesGaps92100.lean — even binary gaps n ∈ {92, 94, 96, 98, 100}.

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

namespace Brockian.SingularSeries.Gaps92100

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_ninetyTwo : (evenPair 92).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (92 : ℕ) ≠ 0)

theorem evenPair_card_ninetyFour : (evenPair 94).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (94 : ℕ) ≠ 0)

theorem evenPair_card_ninetySix : (evenPair 96).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (96 : ℕ) ≠ 0)

theorem evenPair_card_ninetyEight : (evenPair 98).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (98 : ℕ) ≠ 0)

theorem evenPair_card_oneHundred : (evenPair 100).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (100 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_ninetyTwo : IsAdmissible (evenPair 92) :=
  isAdmissible_evenPair (by decide : Even 92)

theorem isAdmissible_evenPair_ninetyFour : IsAdmissible (evenPair 94) :=
  isAdmissible_evenPair (by decide : Even 94)

theorem isAdmissible_evenPair_ninetySix : IsAdmissible (evenPair 96) :=
  isAdmissible_evenPair (by decide : Even 96)

theorem isAdmissible_evenPair_ninetyEight : IsAdmissible (evenPair 98) :=
  isAdmissible_evenPair (by decide : Even 98)

theorem isAdmissible_evenPair_oneHundred : IsAdmissible (evenPair 100) :=
  isAdmissible_evenPair (by decide : Even 100)

theorem singular_series_pos_evenPair_ninetyTwo : 0 < singularSeries (evenPair 92) :=
  singular_series_pos_evenPair (by decide : Even 92)

theorem singular_series_pos_evenPair_ninetyFour : 0 < singularSeries (evenPair 94) :=
  singular_series_pos_evenPair (by decide : Even 94)

theorem singular_series_pos_evenPair_ninetySix : 0 < singularSeries (evenPair 96) :=
  singular_series_pos_evenPair (by decide : Even 96)

theorem singular_series_pos_evenPair_ninetyEight : 0 < singularSeries (evenPair 98) :=
  singular_series_pos_evenPair (by decide : Even 98)

theorem singular_series_pos_evenPair_oneHundred : 0 < singularSeries (evenPair 100) :=
  singular_series_pos_evenPair (by decide : Even 100)

theorem singular_series_finite_pos_evenPair_ninetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 92) P :=
  singular_series_finite_pos_evenPair (by decide : Even 92) P

theorem singular_series_finite_pos_evenPair_ninetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 94) P :=
  singular_series_finite_pos_evenPair (by decide : Even 94) P

theorem singular_series_finite_pos_evenPair_ninetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 96) P :=
  singular_series_finite_pos_evenPair (by decide : Even 96) P

theorem singular_series_finite_pos_evenPair_ninetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 98) P :=
  singular_series_finite_pos_evenPair (by decide : Even 98) P

theorem singular_series_finite_pos_evenPair_oneHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 100) P :=
  singular_series_finite_pos_evenPair (by decide : Even 100) P

theorem nu_p_ninetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 92) p = if p = 2 ∨ p ∣ 92 then 1 else 2 :=
  nu_p_evenPair (by decide : (92 : ℕ) ≠ 0) (by decide : Even 92) hp

theorem nu_p_ninetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 94) p = if p = 2 ∨ p ∣ 94 then 1 else 2 :=
  nu_p_evenPair (by decide : (94 : ℕ) ≠ 0) (by decide : Even 94) hp

theorem nu_p_ninetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 96) p = if p = 2 ∨ p ∣ 96 then 1 else 2 :=
  nu_p_evenPair (by decide : (96 : ℕ) ≠ 0) (by decide : Even 96) hp

theorem nu_p_ninetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 98) p = if p = 2 ∨ p ∣ 98 then 1 else 2 :=
  nu_p_evenPair (by decide : (98 : ℕ) ≠ 0) (by decide : Even 98) hp

theorem nu_p_oneHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 100) p = if p = 2 ∨ p ∣ 100 then 1 else 2 :=
  nu_p_evenPair (by decide : (100 : ℕ) ≠ 0) (by decide : Even 100) hp

theorem nu_p_ninetyTwo_two : nu_p (evenPair 92) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 92)

theorem localFactor_ninetyTwo_two : localFactor (evenPair 92) 2 = 2 :=
  localFactor_evenPair_two (by decide : (92 : ℕ) ≠ 0) (by decide : Even 92)

theorem nu_p_oneHundred_two : nu_p (evenPair 100) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 100)

theorem localFactor_oneHundred_two : localFactor (evenPair 100) 2 = 2 :=
  localFactor_evenPair_two (by decide : (100 : ℕ) ≠ 0) (by decide : Even 100)

end Brockian.SingularSeries.Gaps92100
