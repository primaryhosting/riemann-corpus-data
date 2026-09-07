/-
  Brockian/SingularSeriesGaps21222130.lean — even binary gaps n ∈ {2122, 2124, 2126, 2128, 2130}.

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

namespace Brockian.SingularSeries.Gaps21222130

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandOneHundredTwentyTwo : (evenPair 2122).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2122 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredTwentyFour : (evenPair 2124).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2124 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredTwentySix : (evenPair 2126).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2126 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredTwentyEight : (evenPair 2128).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2128 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredThirty : (evenPair 2130).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2130 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandOneHundredTwentyTwo : IsAdmissible (evenPair 2122) :=
  isAdmissible_evenPair (by decide : Even 2122)

theorem isAdmissible_evenPair_twoThousandOneHundredTwentyFour : IsAdmissible (evenPair 2124) :=
  isAdmissible_evenPair (by decide : Even 2124)

theorem isAdmissible_evenPair_twoThousandOneHundredTwentySix : IsAdmissible (evenPair 2126) :=
  isAdmissible_evenPair (by decide : Even 2126)

theorem isAdmissible_evenPair_twoThousandOneHundredTwentyEight : IsAdmissible (evenPair 2128) :=
  isAdmissible_evenPair (by decide : Even 2128)

theorem isAdmissible_evenPair_twoThousandOneHundredThirty : IsAdmissible (evenPair 2130) :=
  isAdmissible_evenPair (by decide : Even 2130)

theorem singular_series_pos_evenPair_twoThousandOneHundredTwentyTwo : 0 < singularSeries (evenPair 2122) :=
  singular_series_pos_evenPair (by decide : Even 2122)

theorem singular_series_pos_evenPair_twoThousandOneHundredTwentyFour : 0 < singularSeries (evenPair 2124) :=
  singular_series_pos_evenPair (by decide : Even 2124)

theorem singular_series_pos_evenPair_twoThousandOneHundredTwentySix : 0 < singularSeries (evenPair 2126) :=
  singular_series_pos_evenPair (by decide : Even 2126)

theorem singular_series_pos_evenPair_twoThousandOneHundredTwentyEight : 0 < singularSeries (evenPair 2128) :=
  singular_series_pos_evenPair (by decide : Even 2128)

theorem singular_series_pos_evenPair_twoThousandOneHundredThirty : 0 < singularSeries (evenPair 2130) :=
  singular_series_pos_evenPair (by decide : Even 2130)

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2122) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2122) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2124) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2124) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2126) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2126) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2128) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2128) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2130) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2130) P

theorem nu_p_twoThousandOneHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2122) p = if p = 2 ∨ p ∣ 2122 then 1 else 2 :=
  nu_p_evenPair (by decide : (2122 : ℕ) ≠ 0) (by decide : Even 2122) hp

theorem nu_p_twoThousandOneHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2124) p = if p = 2 ∨ p ∣ 2124 then 1 else 2 :=
  nu_p_evenPair (by decide : (2124 : ℕ) ≠ 0) (by decide : Even 2124) hp

theorem nu_p_twoThousandOneHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2126) p = if p = 2 ∨ p ∣ 2126 then 1 else 2 :=
  nu_p_evenPair (by decide : (2126 : ℕ) ≠ 0) (by decide : Even 2126) hp

theorem nu_p_twoThousandOneHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2128) p = if p = 2 ∨ p ∣ 2128 then 1 else 2 :=
  nu_p_evenPair (by decide : (2128 : ℕ) ≠ 0) (by decide : Even 2128) hp

theorem nu_p_twoThousandOneHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2130) p = if p = 2 ∨ p ∣ 2130 then 1 else 2 :=
  nu_p_evenPair (by decide : (2130 : ℕ) ≠ 0) (by decide : Even 2130) hp

theorem nu_p_twoThousandOneHundredTwentyTwo_two : nu_p (evenPair 2122) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2122)

theorem localFactor_twoThousandOneHundredTwentyTwo_two : localFactor (evenPair 2122) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2122 : ℕ) ≠ 0) (by decide : Even 2122)

theorem nu_p_twoThousandOneHundredThirty_two : nu_p (evenPair 2130) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2130)

theorem localFactor_twoThousandOneHundredThirty_two : localFactor (evenPair 2130) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2130 : ℕ) ≠ 0) (by decide : Even 2130)

end Brockian.SingularSeries.Gaps21222130
