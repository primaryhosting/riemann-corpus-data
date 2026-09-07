/-
  Brockian/SingularSeriesGaps582590.lean — even binary gaps n ∈ {582, 584, 586, 588, 590}.

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

namespace Brockian.SingularSeries.Gaps582590

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiveHundredEightyTwo : (evenPair 582).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (582 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredEightyFour : (evenPair 584).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (584 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredEightySix : (evenPair 586).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (586 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredEightyEight : (evenPair 588).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (588 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredNinety : (evenPair 590).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (590 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiveHundredEightyTwo : IsAdmissible (evenPair 582) :=
  isAdmissible_evenPair (by decide : Even 582)

theorem isAdmissible_evenPair_fiveHundredEightyFour : IsAdmissible (evenPair 584) :=
  isAdmissible_evenPair (by decide : Even 584)

theorem isAdmissible_evenPair_fiveHundredEightySix : IsAdmissible (evenPair 586) :=
  isAdmissible_evenPair (by decide : Even 586)

theorem isAdmissible_evenPair_fiveHundredEightyEight : IsAdmissible (evenPair 588) :=
  isAdmissible_evenPair (by decide : Even 588)

theorem isAdmissible_evenPair_fiveHundredNinety : IsAdmissible (evenPair 590) :=
  isAdmissible_evenPair (by decide : Even 590)

theorem singular_series_pos_evenPair_fiveHundredEightyTwo : 0 < singularSeries (evenPair 582) :=
  singular_series_pos_evenPair (by decide : Even 582)

theorem singular_series_pos_evenPair_fiveHundredEightyFour : 0 < singularSeries (evenPair 584) :=
  singular_series_pos_evenPair (by decide : Even 584)

theorem singular_series_pos_evenPair_fiveHundredEightySix : 0 < singularSeries (evenPair 586) :=
  singular_series_pos_evenPair (by decide : Even 586)

theorem singular_series_pos_evenPair_fiveHundredEightyEight : 0 < singularSeries (evenPair 588) :=
  singular_series_pos_evenPair (by decide : Even 588)

theorem singular_series_pos_evenPair_fiveHundredNinety : 0 < singularSeries (evenPair 590) :=
  singular_series_pos_evenPair (by decide : Even 590)

theorem singular_series_finite_pos_evenPair_fiveHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 582) P :=
  singular_series_finite_pos_evenPair (by decide : Even 582) P

theorem singular_series_finite_pos_evenPair_fiveHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 584) P :=
  singular_series_finite_pos_evenPair (by decide : Even 584) P

theorem singular_series_finite_pos_evenPair_fiveHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 586) P :=
  singular_series_finite_pos_evenPair (by decide : Even 586) P

theorem singular_series_finite_pos_evenPair_fiveHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 588) P :=
  singular_series_finite_pos_evenPair (by decide : Even 588) P

theorem singular_series_finite_pos_evenPair_fiveHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 590) P :=
  singular_series_finite_pos_evenPair (by decide : Even 590) P

theorem nu_p_fiveHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 582) p = if p = 2 ∨ p ∣ 582 then 1 else 2 :=
  nu_p_evenPair (by decide : (582 : ℕ) ≠ 0) (by decide : Even 582) hp

theorem nu_p_fiveHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 584) p = if p = 2 ∨ p ∣ 584 then 1 else 2 :=
  nu_p_evenPair (by decide : (584 : ℕ) ≠ 0) (by decide : Even 584) hp

theorem nu_p_fiveHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 586) p = if p = 2 ∨ p ∣ 586 then 1 else 2 :=
  nu_p_evenPair (by decide : (586 : ℕ) ≠ 0) (by decide : Even 586) hp

theorem nu_p_fiveHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 588) p = if p = 2 ∨ p ∣ 588 then 1 else 2 :=
  nu_p_evenPair (by decide : (588 : ℕ) ≠ 0) (by decide : Even 588) hp

theorem nu_p_fiveHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 590) p = if p = 2 ∨ p ∣ 590 then 1 else 2 :=
  nu_p_evenPair (by decide : (590 : ℕ) ≠ 0) (by decide : Even 590) hp

theorem nu_p_fiveHundredEightyTwo_two : nu_p (evenPair 582) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 582)

theorem localFactor_fiveHundredEightyTwo_two : localFactor (evenPair 582) 2 = 2 :=
  localFactor_evenPair_two (by decide : (582 : ℕ) ≠ 0) (by decide : Even 582)

theorem nu_p_fiveHundredNinety_two : nu_p (evenPair 590) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 590)

theorem localFactor_fiveHundredNinety_two : localFactor (evenPair 590) 2 = 2 :=
  localFactor_evenPair_two (by decide : (590 : ℕ) ≠ 0) (by decide : Even 590)

end Brockian.SingularSeries.Gaps582590
