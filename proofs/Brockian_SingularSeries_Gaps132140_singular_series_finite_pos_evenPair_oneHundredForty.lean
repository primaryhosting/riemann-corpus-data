/-
  Brockian/SingularSeriesGaps132140.lean — even binary gaps n ∈ {132, 134, 136, 138, 140}.

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

namespace Brockian.SingularSeries.Gaps132140

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneHundredThirtyTwo : (evenPair 132).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (132 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredThirtyFour : (evenPair 134).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (134 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredThirtySix : (evenPair 136).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (136 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredThirtyEight : (evenPair 138).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (138 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredForty : (evenPair 140).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (140 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneHundredThirtyTwo : IsAdmissible (evenPair 132) :=
  isAdmissible_evenPair (by decide : Even 132)

theorem isAdmissible_evenPair_oneHundredThirtyFour : IsAdmissible (evenPair 134) :=
  isAdmissible_evenPair (by decide : Even 134)

theorem isAdmissible_evenPair_oneHundredThirtySix : IsAdmissible (evenPair 136) :=
  isAdmissible_evenPair (by decide : Even 136)

theorem isAdmissible_evenPair_oneHundredThirtyEight : IsAdmissible (evenPair 138) :=
  isAdmissible_evenPair (by decide : Even 138)

theorem isAdmissible_evenPair_oneHundredForty : IsAdmissible (evenPair 140) :=
  isAdmissible_evenPair (by decide : Even 140)

theorem singular_series_pos_evenPair_oneHundredThirtyTwo : 0 < singularSeries (evenPair 132) :=
  singular_series_pos_evenPair (by decide : Even 132)

theorem singular_series_pos_evenPair_oneHundredThirtyFour : 0 < singularSeries (evenPair 134) :=
  singular_series_pos_evenPair (by decide : Even 134)

theorem singular_series_pos_evenPair_oneHundredThirtySix : 0 < singularSeries (evenPair 136) :=
  singular_series_pos_evenPair (by decide : Even 136)

theorem singular_series_pos_evenPair_oneHundredThirtyEight : 0 < singularSeries (evenPair 138) :=
  singular_series_pos_evenPair (by decide : Even 138)

theorem singular_series_pos_evenPair_oneHundredForty : 0 < singularSeries (evenPair 140) :=
  singular_series_pos_evenPair (by decide : Even 140)

theorem singular_series_finite_pos_evenPair_oneHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 132) P :=
  singular_series_finite_pos_evenPair (by decide : Even 132) P

theorem singular_series_finite_pos_evenPair_oneHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 134) P :=
  singular_series_finite_pos_evenPair (by decide : Even 134) P

theorem singular_series_finite_pos_evenPair_oneHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 136) P :=
  singular_series_finite_pos_evenPair (by decide : Even 136) P

theorem singular_series_finite_pos_evenPair_oneHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 138) P :=
  singular_series_finite_pos_evenPair (by decide : Even 138) P

theorem singular_series_finite_pos_evenPair_oneHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 140) P :=
  singular_series_finite_pos_evenPair (by decide : Even 140) P

theorem nu_p_oneHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 132) p = if p = 2 ∨ p ∣ 132 then 1 else 2 :=
  nu_p_evenPair (by decide : (132 : ℕ) ≠ 0) (by decide : Even 132) hp

theorem nu_p_oneHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 134) p = if p = 2 ∨ p ∣ 134 then 1 else 2 :=
  nu_p_evenPair (by decide : (134 : ℕ) ≠ 0) (by decide : Even 134) hp

theorem nu_p_oneHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 136) p = if p = 2 ∨ p ∣ 136 then 1 else 2 :=
  nu_p_evenPair (by decide : (136 : ℕ) ≠ 0) (by decide : Even 136) hp

theorem nu_p_oneHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 138) p = if p = 2 ∨ p ∣ 138 then 1 else 2 :=
  nu_p_evenPair (by decide : (138 : ℕ) ≠ 0) (by decide : Even 138) hp

theorem nu_p_oneHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 140) p = if p = 2 ∨ p ∣ 140 then 1 else 2 :=
  nu_p_evenPair (by decide : (140 : ℕ) ≠ 0) (by decide : Even 140) hp

theorem nu_p_oneHundredThirtyTwo_two : nu_p (evenPair 132) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 132)

theorem localFactor_oneHundredThirtyTwo_two : localFactor (evenPair 132) 2 = 2 :=
  localFactor_evenPair_two (by decide : (132 : ℕ) ≠ 0) (by decide : Even 132)

theorem nu_p_oneHundredForty_two : nu_p (evenPair 140) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 140)

theorem localFactor_oneHundredForty_two : localFactor (evenPair 140) 2 = 2 :=
  localFactor_evenPair_two (by decide : (140 : ℕ) ≠ 0) (by decide : Even 140)

end Brockian.SingularSeries.Gaps132140
