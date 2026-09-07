/-
  Brockian/SingularSeriesGaps11221130.lean — even binary gaps n ∈ {1122, 1124, 1126, 1128, 1130}.

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

namespace Brockian.SingularSeries.Gaps11221130

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandOneHundredTwentyTwo : (evenPair 1122).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1122 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredTwentyFour : (evenPair 1124).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1124 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredTwentySix : (evenPair 1126).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1126 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredTwentyEight : (evenPair 1128).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1128 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredThirty : (evenPair 1130).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1130 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandOneHundredTwentyTwo : IsAdmissible (evenPair 1122) :=
  isAdmissible_evenPair (by decide : Even 1122)

theorem isAdmissible_evenPair_oneThousandOneHundredTwentyFour : IsAdmissible (evenPair 1124) :=
  isAdmissible_evenPair (by decide : Even 1124)

theorem isAdmissible_evenPair_oneThousandOneHundredTwentySix : IsAdmissible (evenPair 1126) :=
  isAdmissible_evenPair (by decide : Even 1126)

theorem isAdmissible_evenPair_oneThousandOneHundredTwentyEight : IsAdmissible (evenPair 1128) :=
  isAdmissible_evenPair (by decide : Even 1128)

theorem isAdmissible_evenPair_oneThousandOneHundredThirty : IsAdmissible (evenPair 1130) :=
  isAdmissible_evenPair (by decide : Even 1130)

theorem singular_series_pos_evenPair_oneThousandOneHundredTwentyTwo : 0 < singularSeries (evenPair 1122) :=
  singular_series_pos_evenPair (by decide : Even 1122)

theorem singular_series_pos_evenPair_oneThousandOneHundredTwentyFour : 0 < singularSeries (evenPair 1124) :=
  singular_series_pos_evenPair (by decide : Even 1124)

theorem singular_series_pos_evenPair_oneThousandOneHundredTwentySix : 0 < singularSeries (evenPair 1126) :=
  singular_series_pos_evenPair (by decide : Even 1126)

theorem singular_series_pos_evenPair_oneThousandOneHundredTwentyEight : 0 < singularSeries (evenPair 1128) :=
  singular_series_pos_evenPair (by decide : Even 1128)

theorem singular_series_pos_evenPair_oneThousandOneHundredThirty : 0 < singularSeries (evenPair 1130) :=
  singular_series_pos_evenPair (by decide : Even 1130)

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1122) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1122) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1124) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1124) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1126) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1126) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1128) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1128) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1130) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1130) P

theorem nu_p_oneThousandOneHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1122) p = if p = 2 ∨ p ∣ 1122 then 1 else 2 :=
  nu_p_evenPair (by decide : (1122 : ℕ) ≠ 0) (by decide : Even 1122) hp

theorem nu_p_oneThousandOneHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1124) p = if p = 2 ∨ p ∣ 1124 then 1 else 2 :=
  nu_p_evenPair (by decide : (1124 : ℕ) ≠ 0) (by decide : Even 1124) hp

theorem nu_p_oneThousandOneHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1126) p = if p = 2 ∨ p ∣ 1126 then 1 else 2 :=
  nu_p_evenPair (by decide : (1126 : ℕ) ≠ 0) (by decide : Even 1126) hp

theorem nu_p_oneThousandOneHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1128) p = if p = 2 ∨ p ∣ 1128 then 1 else 2 :=
  nu_p_evenPair (by decide : (1128 : ℕ) ≠ 0) (by decide : Even 1128) hp

theorem nu_p_oneThousandOneHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1130) p = if p = 2 ∨ p ∣ 1130 then 1 else 2 :=
  nu_p_evenPair (by decide : (1130 : ℕ) ≠ 0) (by decide : Even 1130) hp

theorem nu_p_oneThousandOneHundredTwentyTwo_two : nu_p (evenPair 1122) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1122)

theorem localFactor_oneThousandOneHundredTwentyTwo_two : localFactor (evenPair 1122) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1122 : ℕ) ≠ 0) (by decide : Even 1122)

theorem nu_p_oneThousandOneHundredThirty_two : nu_p (evenPair 1130) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1130)

theorem localFactor_oneThousandOneHundredThirty_two : localFactor (evenPair 1130) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1130 : ℕ) ≠ 0) (by decide : Even 1130)

end Brockian.SingularSeries.Gaps11221130
