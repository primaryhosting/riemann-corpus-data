/-
  Brockian/SingularSeriesGaps122130.lean — even binary gaps n ∈ {122, 124, 126, 128, 130}.

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

namespace Brockian.SingularSeries.Gaps122130

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
theorem evenPair_card_oneHundredTwentyTwo : (evenPair 122).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (122 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredTwentyFour : (evenPair 124).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (124 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredTwentySix : (evenPair 126).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (126 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredTwentyEight : (evenPair 128).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (128 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredThirty : (evenPair 130).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (130 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneHundredTwentyTwo : IsAdmissible (evenPair 122) :=
  isAdmissible_evenPair (by decide : Even 122)

theorem isAdmissible_evenPair_oneHundredTwentyFour : IsAdmissible (evenPair 124) :=
  isAdmissible_evenPair (by decide : Even 124)

theorem isAdmissible_evenPair_oneHundredTwentySix : IsAdmissible (evenPair 126) :=
  isAdmissible_evenPair (by decide : Even 126)

theorem isAdmissible_evenPair_oneHundredTwentyEight : IsAdmissible (evenPair 128) :=
  isAdmissible_evenPair (by decide : Even 128)

theorem isAdmissible_evenPair_oneHundredThirty : IsAdmissible (evenPair 130) :=
  isAdmissible_evenPair (by decide : Even 130)

theorem singular_series_pos_evenPair_oneHundredTwentyTwo : 0 < singularSeries (evenPair 122) :=
  singular_series_pos_evenPair (by decide : Even 122)

theorem singular_series_pos_evenPair_oneHundredTwentyFour : 0 < singularSeries (evenPair 124) :=
  singular_series_pos_evenPair (by decide : Even 124)

theorem singular_series_pos_evenPair_oneHundredTwentySix : 0 < singularSeries (evenPair 126) :=
  singular_series_pos_evenPair (by decide : Even 126)

theorem singular_series_pos_evenPair_oneHundredTwentyEight : 0 < singularSeries (evenPair 128) :=
  singular_series_pos_evenPair (by decide : Even 128)

theorem singular_series_pos_evenPair_oneHundredThirty : 0 < singularSeries (evenPair 130) :=
  singular_series_pos_evenPair (by decide : Even 130)

theorem singular_series_finite_pos_evenPair_oneHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 122) P :=
  singular_series_finite_pos_evenPair (by decide : Even 122) P

theorem singular_series_finite_pos_evenPair_oneHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 124) P :=
  singular_series_finite_pos_evenPair (by decide : Even 124) P

theorem singular_series_finite_pos_evenPair_oneHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 126) P :=
  singular_series_finite_pos_evenPair (by decide : Even 126) P

theorem singular_series_finite_pos_evenPair_oneHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 128) P :=
  singular_series_finite_pos_evenPair (by decide : Even 128) P

theorem singular_series_finite_pos_evenPair_oneHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 130) P :=
  singular_series_finite_pos_evenPair (by decide : Even 130) P

theorem nu_p_oneHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 122) p = if p = 2 ∨ p ∣ 122 then 1 else 2 :=
  nu_p_evenPair (by decide : (122 : ℕ) ≠ 0) (by decide : Even 122) hp

theorem nu_p_oneHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 124) p = if p = 2 ∨ p ∣ 124 then 1 else 2 :=
  nu_p_evenPair (by decide : (124 : ℕ) ≠ 0) (by decide : Even 124) hp

theorem nu_p_oneHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 126) p = if p = 2 ∨ p ∣ 126 then 1 else 2 :=
  nu_p_evenPair (by decide : (126 : ℕ) ≠ 0) (by decide : Even 126) hp

theorem nu_p_oneHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 128) p = if p = 2 ∨ p ∣ 128 then 1 else 2 :=
  nu_p_evenPair (by decide : (128 : ℕ) ≠ 0) (by decide : Even 128) hp

theorem nu_p_oneHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 130) p = if p = 2 ∨ p ∣ 130 then 1 else 2 :=
  nu_p_evenPair (by decide : (130 : ℕ) ≠ 0) (by decide : Even 130) hp

theorem nu_p_oneHundredTwentyTwo_two : nu_p (evenPair 122) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 122)

theorem localFactor_oneHundredTwentyTwo_two : localFactor (evenPair 122) 2 = 2 :=
  localFactor_evenPair_two (by decide : (122 : ℕ) ≠ 0) (by decide : Even 122)

theorem nu_p_oneHundredThirty_two : nu_p (evenPair 130) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 130)

theorem localFactor_oneHundredThirty_two : localFactor (evenPair 130) 2 = 2 :=
  localFactor_evenPair_two (by decide : (130 : ℕ) ≠ 0) (by decide : Even 130)

end Brockian.SingularSeries.Gaps122130
