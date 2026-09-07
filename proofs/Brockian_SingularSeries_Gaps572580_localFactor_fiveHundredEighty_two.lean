/-
  Brockian/SingularSeriesGaps572580.lean — even binary gaps n ∈ {572, 574, 576, 578, 580}.

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

namespace Brockian.SingularSeries.Gaps572580

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiveHundredSeventyTwo : (evenPair 572).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (572 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredSeventyFour : (evenPair 574).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (574 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredSeventySix : (evenPair 576).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (576 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredSeventyEight : (evenPair 578).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (578 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredEighty : (evenPair 580).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (580 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiveHundredSeventyTwo : IsAdmissible (evenPair 572) :=
  isAdmissible_evenPair (by decide : Even 572)

theorem isAdmissible_evenPair_fiveHundredSeventyFour : IsAdmissible (evenPair 574) :=
  isAdmissible_evenPair (by decide : Even 574)

theorem isAdmissible_evenPair_fiveHundredSeventySix : IsAdmissible (evenPair 576) :=
  isAdmissible_evenPair (by decide : Even 576)

theorem isAdmissible_evenPair_fiveHundredSeventyEight : IsAdmissible (evenPair 578) :=
  isAdmissible_evenPair (by decide : Even 578)

theorem isAdmissible_evenPair_fiveHundredEighty : IsAdmissible (evenPair 580) :=
  isAdmissible_evenPair (by decide : Even 580)

theorem singular_series_pos_evenPair_fiveHundredSeventyTwo : 0 < singularSeries (evenPair 572) :=
  singular_series_pos_evenPair (by decide : Even 572)

theorem singular_series_pos_evenPair_fiveHundredSeventyFour : 0 < singularSeries (evenPair 574) :=
  singular_series_pos_evenPair (by decide : Even 574)

theorem singular_series_pos_evenPair_fiveHundredSeventySix : 0 < singularSeries (evenPair 576) :=
  singular_series_pos_evenPair (by decide : Even 576)

theorem singular_series_pos_evenPair_fiveHundredSeventyEight : 0 < singularSeries (evenPair 578) :=
  singular_series_pos_evenPair (by decide : Even 578)

theorem singular_series_pos_evenPair_fiveHundredEighty : 0 < singularSeries (evenPair 580) :=
  singular_series_pos_evenPair (by decide : Even 580)

theorem singular_series_finite_pos_evenPair_fiveHundredSeventyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 572) P :=
  singular_series_finite_pos_evenPair (by decide : Even 572) P

theorem singular_series_finite_pos_evenPair_fiveHundredSeventyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 574) P :=
  singular_series_finite_pos_evenPair (by decide : Even 574) P

theorem singular_series_finite_pos_evenPair_fiveHundredSeventySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 576) P :=
  singular_series_finite_pos_evenPair (by decide : Even 576) P

theorem singular_series_finite_pos_evenPair_fiveHundredSeventyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 578) P :=
  singular_series_finite_pos_evenPair (by decide : Even 578) P

theorem singular_series_finite_pos_evenPair_fiveHundredEighty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 580) P :=
  singular_series_finite_pos_evenPair (by decide : Even 580) P

theorem nu_p_fiveHundredSeventyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 572) p = if p = 2 ∨ p ∣ 572 then 1 else 2 :=
  nu_p_evenPair (by decide : (572 : ℕ) ≠ 0) (by decide : Even 572) hp

theorem nu_p_fiveHundredSeventyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 574) p = if p = 2 ∨ p ∣ 574 then 1 else 2 :=
  nu_p_evenPair (by decide : (574 : ℕ) ≠ 0) (by decide : Even 574) hp

theorem nu_p_fiveHundredSeventySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 576) p = if p = 2 ∨ p ∣ 576 then 1 else 2 :=
  nu_p_evenPair (by decide : (576 : ℕ) ≠ 0) (by decide : Even 576) hp

theorem nu_p_fiveHundredSeventyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 578) p = if p = 2 ∨ p ∣ 578 then 1 else 2 :=
  nu_p_evenPair (by decide : (578 : ℕ) ≠ 0) (by decide : Even 578) hp

theorem nu_p_fiveHundredEighty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 580) p = if p = 2 ∨ p ∣ 580 then 1 else 2 :=
  nu_p_evenPair (by decide : (580 : ℕ) ≠ 0) (by decide : Even 580) hp

theorem nu_p_fiveHundredSeventyTwo_two : nu_p (evenPair 572) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 572)

theorem localFactor_fiveHundredSeventyTwo_two : localFactor (evenPair 572) 2 = 2 :=
  localFactor_evenPair_two (by decide : (572 : ℕ) ≠ 0) (by decide : Even 572)

theorem nu_p_fiveHundredEighty_two : nu_p (evenPair 580) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 580)

theorem localFactor_fiveHundredEighty_two : localFactor (evenPair 580) 2 = 2 :=
  localFactor_evenPair_two (by decide : (580 : ℕ) ≠ 0) (by decide : Even 580)

end Brockian.SingularSeries.Gaps572580
