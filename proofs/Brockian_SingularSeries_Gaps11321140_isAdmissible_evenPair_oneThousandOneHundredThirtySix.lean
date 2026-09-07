/-
  Brockian/SingularSeriesGaps11321140.lean — even binary gaps n ∈ {1132, 1134, 1136, 1138, 1140}.

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

namespace Brockian.SingularSeries.Gaps11321140

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandOneHundredThirtyTwo : (evenPair 1132).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1132 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredThirtyFour : (evenPair 1134).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1134 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredThirtySix : (evenPair 1136).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1136 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredThirtyEight : (evenPair 1138).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1138 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredForty : (evenPair 1140).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1140 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandOneHundredThirtyTwo : IsAdmissible (evenPair 1132) :=
  isAdmissible_evenPair (by decide : Even 1132)

theorem isAdmissible_evenPair_oneThousandOneHundredThirtyFour : IsAdmissible (evenPair 1134) :=
  isAdmissible_evenPair (by decide : Even 1134)

theorem isAdmissible_evenPair_oneThousandOneHundredThirtySix : IsAdmissible (evenPair 1136) :=
  isAdmissible_evenPair (by decide : Even 1136)

theorem isAdmissible_evenPair_oneThousandOneHundredThirtyEight : IsAdmissible (evenPair 1138) :=
  isAdmissible_evenPair (by decide : Even 1138)

theorem isAdmissible_evenPair_oneThousandOneHundredForty : IsAdmissible (evenPair 1140) :=
  isAdmissible_evenPair (by decide : Even 1140)

theorem singular_series_pos_evenPair_oneThousandOneHundredThirtyTwo : 0 < singularSeries (evenPair 1132) :=
  singular_series_pos_evenPair (by decide : Even 1132)

theorem singular_series_pos_evenPair_oneThousandOneHundredThirtyFour : 0 < singularSeries (evenPair 1134) :=
  singular_series_pos_evenPair (by decide : Even 1134)

theorem singular_series_pos_evenPair_oneThousandOneHundredThirtySix : 0 < singularSeries (evenPair 1136) :=
  singular_series_pos_evenPair (by decide : Even 1136)

theorem singular_series_pos_evenPair_oneThousandOneHundredThirtyEight : 0 < singularSeries (evenPair 1138) :=
  singular_series_pos_evenPair (by decide : Even 1138)

theorem singular_series_pos_evenPair_oneThousandOneHundredForty : 0 < singularSeries (evenPair 1140) :=
  singular_series_pos_evenPair (by decide : Even 1140)

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1132) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1132) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1134) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1134) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1136) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1136) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1138) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1138) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1140) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1140) P

theorem nu_p_oneThousandOneHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1132) p = if p = 2 ∨ p ∣ 1132 then 1 else 2 :=
  nu_p_evenPair (by decide : (1132 : ℕ) ≠ 0) (by decide : Even 1132) hp

theorem nu_p_oneThousandOneHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1134) p = if p = 2 ∨ p ∣ 1134 then 1 else 2 :=
  nu_p_evenPair (by decide : (1134 : ℕ) ≠ 0) (by decide : Even 1134) hp

theorem nu_p_oneThousandOneHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1136) p = if p = 2 ∨ p ∣ 1136 then 1 else 2 :=
  nu_p_evenPair (by decide : (1136 : ℕ) ≠ 0) (by decide : Even 1136) hp

theorem nu_p_oneThousandOneHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1138) p = if p = 2 ∨ p ∣ 1138 then 1 else 2 :=
  nu_p_evenPair (by decide : (1138 : ℕ) ≠ 0) (by decide : Even 1138) hp

theorem nu_p_oneThousandOneHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1140) p = if p = 2 ∨ p ∣ 1140 then 1 else 2 :=
  nu_p_evenPair (by decide : (1140 : ℕ) ≠ 0) (by decide : Even 1140) hp

theorem nu_p_oneThousandOneHundredThirtyTwo_two : nu_p (evenPair 1132) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1132)

theorem localFactor_oneThousandOneHundredThirtyTwo_two : localFactor (evenPair 1132) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1132 : ℕ) ≠ 0) (by decide : Even 1132)

theorem nu_p_oneThousandOneHundredForty_two : nu_p (evenPair 1140) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1140)

theorem localFactor_oneThousandOneHundredForty_two : localFactor (evenPair 1140) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1140 : ℕ) ≠ 0) (by decide : Even 1140)

end Brockian.SingularSeries.Gaps11321140
