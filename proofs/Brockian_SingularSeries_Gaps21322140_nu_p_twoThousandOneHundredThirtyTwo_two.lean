/-
  Brockian/SingularSeriesGaps21322140.lean — even binary gaps n ∈ {2132, 2134, 2136, 2138, 2140}.

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

namespace Brockian.SingularSeries.Gaps21322140

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandOneHundredThirtyTwo : (evenPair 2132).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2132 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredThirtyFour : (evenPair 2134).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2134 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredThirtySix : (evenPair 2136).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2136 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredThirtyEight : (evenPair 2138).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2138 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredForty : (evenPair 2140).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2140 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandOneHundredThirtyTwo : IsAdmissible (evenPair 2132) :=
  isAdmissible_evenPair (by decide : Even 2132)

theorem isAdmissible_evenPair_twoThousandOneHundredThirtyFour : IsAdmissible (evenPair 2134) :=
  isAdmissible_evenPair (by decide : Even 2134)

theorem isAdmissible_evenPair_twoThousandOneHundredThirtySix : IsAdmissible (evenPair 2136) :=
  isAdmissible_evenPair (by decide : Even 2136)

theorem isAdmissible_evenPair_twoThousandOneHundredThirtyEight : IsAdmissible (evenPair 2138) :=
  isAdmissible_evenPair (by decide : Even 2138)

theorem isAdmissible_evenPair_twoThousandOneHundredForty : IsAdmissible (evenPair 2140) :=
  isAdmissible_evenPair (by decide : Even 2140)

theorem singular_series_pos_evenPair_twoThousandOneHundredThirtyTwo : 0 < singularSeries (evenPair 2132) :=
  singular_series_pos_evenPair (by decide : Even 2132)

theorem singular_series_pos_evenPair_twoThousandOneHundredThirtyFour : 0 < singularSeries (evenPair 2134) :=
  singular_series_pos_evenPair (by decide : Even 2134)

theorem singular_series_pos_evenPair_twoThousandOneHundredThirtySix : 0 < singularSeries (evenPair 2136) :=
  singular_series_pos_evenPair (by decide : Even 2136)

theorem singular_series_pos_evenPair_twoThousandOneHundredThirtyEight : 0 < singularSeries (evenPair 2138) :=
  singular_series_pos_evenPair (by decide : Even 2138)

theorem singular_series_pos_evenPair_twoThousandOneHundredForty : 0 < singularSeries (evenPair 2140) :=
  singular_series_pos_evenPair (by decide : Even 2140)

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2132) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2132) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2134) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2134) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2136) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2136) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2138) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2138) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2140) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2140) P

theorem nu_p_twoThousandOneHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2132) p = if p = 2 ∨ p ∣ 2132 then 1 else 2 :=
  nu_p_evenPair (by decide : (2132 : ℕ) ≠ 0) (by decide : Even 2132) hp

theorem nu_p_twoThousandOneHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2134) p = if p = 2 ∨ p ∣ 2134 then 1 else 2 :=
  nu_p_evenPair (by decide : (2134 : ℕ) ≠ 0) (by decide : Even 2134) hp

theorem nu_p_twoThousandOneHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2136) p = if p = 2 ∨ p ∣ 2136 then 1 else 2 :=
  nu_p_evenPair (by decide : (2136 : ℕ) ≠ 0) (by decide : Even 2136) hp

theorem nu_p_twoThousandOneHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2138) p = if p = 2 ∨ p ∣ 2138 then 1 else 2 :=
  nu_p_evenPair (by decide : (2138 : ℕ) ≠ 0) (by decide : Even 2138) hp

theorem nu_p_twoThousandOneHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2140) p = if p = 2 ∨ p ∣ 2140 then 1 else 2 :=
  nu_p_evenPair (by decide : (2140 : ℕ) ≠ 0) (by decide : Even 2140) hp

theorem nu_p_twoThousandOneHundredThirtyTwo_two : nu_p (evenPair 2132) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2132)

theorem localFactor_twoThousandOneHundredThirtyTwo_two : localFactor (evenPair 2132) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2132 : ℕ) ≠ 0) (by decide : Even 2132)

theorem nu_p_twoThousandOneHundredForty_two : nu_p (evenPair 2140) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2140)

theorem localFactor_twoThousandOneHundredForty_two : localFactor (evenPair 2140) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2140 : ℕ) ≠ 0) (by decide : Even 2140)

end Brockian.SingularSeries.Gaps21322140
