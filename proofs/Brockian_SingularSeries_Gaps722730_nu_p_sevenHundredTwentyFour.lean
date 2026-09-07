/-
  Brockian/SingularSeriesGaps722730.lean — even binary gaps n ∈ {722, 724, 726, 728, 730}.

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

namespace Brockian.SingularSeries.Gaps722730

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sevenHundredTwentyTwo : (evenPair 722).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (722 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredTwentyFour : (evenPair 724).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (724 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredTwentySix : (evenPair 726).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (726 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredTwentyEight : (evenPair 728).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (728 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredThirty : (evenPair 730).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (730 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sevenHundredTwentyTwo : IsAdmissible (evenPair 722) :=
  isAdmissible_evenPair (by decide : Even 722)

theorem isAdmissible_evenPair_sevenHundredTwentyFour : IsAdmissible (evenPair 724) :=
  isAdmissible_evenPair (by decide : Even 724)

theorem isAdmissible_evenPair_sevenHundredTwentySix : IsAdmissible (evenPair 726) :=
  isAdmissible_evenPair (by decide : Even 726)

theorem isAdmissible_evenPair_sevenHundredTwentyEight : IsAdmissible (evenPair 728) :=
  isAdmissible_evenPair (by decide : Even 728)

theorem isAdmissible_evenPair_sevenHundredThirty : IsAdmissible (evenPair 730) :=
  isAdmissible_evenPair (by decide : Even 730)

theorem singular_series_pos_evenPair_sevenHundredTwentyTwo : 0 < singularSeries (evenPair 722) :=
  singular_series_pos_evenPair (by decide : Even 722)

theorem singular_series_pos_evenPair_sevenHundredTwentyFour : 0 < singularSeries (evenPair 724) :=
  singular_series_pos_evenPair (by decide : Even 724)

theorem singular_series_pos_evenPair_sevenHundredTwentySix : 0 < singularSeries (evenPair 726) :=
  singular_series_pos_evenPair (by decide : Even 726)

theorem singular_series_pos_evenPair_sevenHundredTwentyEight : 0 < singularSeries (evenPair 728) :=
  singular_series_pos_evenPair (by decide : Even 728)

theorem singular_series_pos_evenPair_sevenHundredThirty : 0 < singularSeries (evenPair 730) :=
  singular_series_pos_evenPair (by decide : Even 730)

theorem singular_series_finite_pos_evenPair_sevenHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 722) P :=
  singular_series_finite_pos_evenPair (by decide : Even 722) P

theorem singular_series_finite_pos_evenPair_sevenHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 724) P :=
  singular_series_finite_pos_evenPair (by decide : Even 724) P

theorem singular_series_finite_pos_evenPair_sevenHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 726) P :=
  singular_series_finite_pos_evenPair (by decide : Even 726) P

theorem singular_series_finite_pos_evenPair_sevenHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 728) P :=
  singular_series_finite_pos_evenPair (by decide : Even 728) P

theorem singular_series_finite_pos_evenPair_sevenHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 730) P :=
  singular_series_finite_pos_evenPair (by decide : Even 730) P

theorem nu_p_sevenHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 722) p = if p = 2 ∨ p ∣ 722 then 1 else 2 :=
  nu_p_evenPair (by decide : (722 : ℕ) ≠ 0) (by decide : Even 722) hp

theorem nu_p_sevenHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 724) p = if p = 2 ∨ p ∣ 724 then 1 else 2 :=
  nu_p_evenPair (by decide : (724 : ℕ) ≠ 0) (by decide : Even 724) hp

theorem nu_p_sevenHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 726) p = if p = 2 ∨ p ∣ 726 then 1 else 2 :=
  nu_p_evenPair (by decide : (726 : ℕ) ≠ 0) (by decide : Even 726) hp

theorem nu_p_sevenHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 728) p = if p = 2 ∨ p ∣ 728 then 1 else 2 :=
  nu_p_evenPair (by decide : (728 : ℕ) ≠ 0) (by decide : Even 728) hp

theorem nu_p_sevenHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 730) p = if p = 2 ∨ p ∣ 730 then 1 else 2 :=
  nu_p_evenPair (by decide : (730 : ℕ) ≠ 0) (by decide : Even 730) hp

theorem nu_p_sevenHundredTwentyTwo_two : nu_p (evenPair 722) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 722)

theorem localFactor_sevenHundredTwentyTwo_two : localFactor (evenPair 722) 2 = 2 :=
  localFactor_evenPair_two (by decide : (722 : ℕ) ≠ 0) (by decide : Even 722)

theorem nu_p_sevenHundredThirty_two : nu_p (evenPair 730) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 730)

theorem localFactor_sevenHundredThirty_two : localFactor (evenPair 730) 2 = 2 :=
  localFactor_evenPair_two (by decide : (730 : ℕ) ≠ 0) (by decide : Even 730)

end Brockian.SingularSeries.Gaps722730
