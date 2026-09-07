/-
  Brockian/SingularSeriesGaps192200.lean — even binary gaps n ∈ {192, 194, 196, 198, 200}.

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

namespace Brockian.SingularSeries.Gaps192200

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneHundredNinetyTwo : (evenPair 192).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (192 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredNinetyFour : (evenPair 194).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (194 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredNinetySix : (evenPair 196).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (196 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredNinetyEight : (evenPair 198).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (198 : ℕ) ≠ 0)

theorem evenPair_card_twoHundred : (evenPair 200).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (200 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneHundredNinetyTwo : IsAdmissible (evenPair 192) :=
  isAdmissible_evenPair (by decide : Even 192)

theorem isAdmissible_evenPair_oneHundredNinetyFour : IsAdmissible (evenPair 194) :=
  isAdmissible_evenPair (by decide : Even 194)

theorem isAdmissible_evenPair_oneHundredNinetySix : IsAdmissible (evenPair 196) :=
  isAdmissible_evenPair (by decide : Even 196)

theorem isAdmissible_evenPair_oneHundredNinetyEight : IsAdmissible (evenPair 198) :=
  isAdmissible_evenPair (by decide : Even 198)

theorem isAdmissible_evenPair_twoHundred : IsAdmissible (evenPair 200) :=
  isAdmissible_evenPair (by decide : Even 200)

theorem singular_series_pos_evenPair_oneHundredNinetyTwo : 0 < singularSeries (evenPair 192) :=
  singular_series_pos_evenPair (by decide : Even 192)

theorem singular_series_pos_evenPair_oneHundredNinetyFour : 0 < singularSeries (evenPair 194) :=
  singular_series_pos_evenPair (by decide : Even 194)

theorem singular_series_pos_evenPair_oneHundredNinetySix : 0 < singularSeries (evenPair 196) :=
  singular_series_pos_evenPair (by decide : Even 196)

theorem singular_series_pos_evenPair_oneHundredNinetyEight : 0 < singularSeries (evenPair 198) :=
  singular_series_pos_evenPair (by decide : Even 198)

theorem singular_series_pos_evenPair_twoHundred : 0 < singularSeries (evenPair 200) :=
  singular_series_pos_evenPair (by decide : Even 200)

theorem singular_series_finite_pos_evenPair_oneHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 192) P :=
  singular_series_finite_pos_evenPair (by decide : Even 192) P

theorem singular_series_finite_pos_evenPair_oneHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 194) P :=
  singular_series_finite_pos_evenPair (by decide : Even 194) P

theorem singular_series_finite_pos_evenPair_oneHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 196) P :=
  singular_series_finite_pos_evenPair (by decide : Even 196) P

theorem singular_series_finite_pos_evenPair_oneHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 198) P :=
  singular_series_finite_pos_evenPair (by decide : Even 198) P

theorem singular_series_finite_pos_evenPair_twoHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 200) P :=
  singular_series_finite_pos_evenPair (by decide : Even 200) P

theorem nu_p_oneHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 192) p = if p = 2 ∨ p ∣ 192 then 1 else 2 :=
  nu_p_evenPair (by decide : (192 : ℕ) ≠ 0) (by decide : Even 192) hp

theorem nu_p_oneHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 194) p = if p = 2 ∨ p ∣ 194 then 1 else 2 :=
  nu_p_evenPair (by decide : (194 : ℕ) ≠ 0) (by decide : Even 194) hp

theorem nu_p_oneHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 196) p = if p = 2 ∨ p ∣ 196 then 1 else 2 :=
  nu_p_evenPair (by decide : (196 : ℕ) ≠ 0) (by decide : Even 196) hp

theorem nu_p_oneHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 198) p = if p = 2 ∨ p ∣ 198 then 1 else 2 :=
  nu_p_evenPair (by decide : (198 : ℕ) ≠ 0) (by decide : Even 198) hp

theorem nu_p_twoHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 200) p = if p = 2 ∨ p ∣ 200 then 1 else 2 :=
  nu_p_evenPair (by decide : (200 : ℕ) ≠ 0) (by decide : Even 200) hp

theorem nu_p_oneHundredNinetyTwo_two : nu_p (evenPair 192) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 192)

theorem localFactor_oneHundredNinetyTwo_two : localFactor (evenPair 192) 2 = 2 :=
  localFactor_evenPair_two (by decide : (192 : ℕ) ≠ 0) (by decide : Even 192)

theorem nu_p_twoHundred_two : nu_p (evenPair 200) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 200)

theorem localFactor_twoHundred_two : localFactor (evenPair 200) 2 = 2 :=
  localFactor_evenPair_two (by decide : (200 : ℕ) ≠ 0) (by decide : Even 200)

end Brockian.SingularSeries.Gaps192200
