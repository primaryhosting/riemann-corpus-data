/-
  Brockian/SingularSeriesGaps622630.lean — even binary gaps n ∈ {622, 624, 626, 628, 630}.

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

namespace Brockian.SingularSeries.Gaps622630

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixHundredTwentyTwo : (evenPair 622).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (622 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredTwentyFour : (evenPair 624).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (624 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredTwentySix : (evenPair 626).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (626 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredTwentyEight : (evenPair 628).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (628 : ℕ) ≠ 0)

theorem evenPair_card_sixHundredThirty : (evenPair 630).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (630 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixHundredTwentyTwo : IsAdmissible (evenPair 622) :=
  isAdmissible_evenPair (by decide : Even 622)

theorem isAdmissible_evenPair_sixHundredTwentyFour : IsAdmissible (evenPair 624) :=
  isAdmissible_evenPair (by decide : Even 624)

theorem isAdmissible_evenPair_sixHundredTwentySix : IsAdmissible (evenPair 626) :=
  isAdmissible_evenPair (by decide : Even 626)

theorem isAdmissible_evenPair_sixHundredTwentyEight : IsAdmissible (evenPair 628) :=
  isAdmissible_evenPair (by decide : Even 628)

theorem isAdmissible_evenPair_sixHundredThirty : IsAdmissible (evenPair 630) :=
  isAdmissible_evenPair (by decide : Even 630)

theorem singular_series_pos_evenPair_sixHundredTwentyTwo : 0 < singularSeries (evenPair 622) :=
  singular_series_pos_evenPair (by decide : Even 622)

theorem singular_series_pos_evenPair_sixHundredTwentyFour : 0 < singularSeries (evenPair 624) :=
  singular_series_pos_evenPair (by decide : Even 624)

theorem singular_series_pos_evenPair_sixHundredTwentySix : 0 < singularSeries (evenPair 626) :=
  singular_series_pos_evenPair (by decide : Even 626)

theorem singular_series_pos_evenPair_sixHundredTwentyEight : 0 < singularSeries (evenPair 628) :=
  singular_series_pos_evenPair (by decide : Even 628)

theorem singular_series_pos_evenPair_sixHundredThirty : 0 < singularSeries (evenPair 630) :=
  singular_series_pos_evenPair (by decide : Even 630)

theorem singular_series_finite_pos_evenPair_sixHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 622) P :=
  singular_series_finite_pos_evenPair (by decide : Even 622) P

theorem singular_series_finite_pos_evenPair_sixHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 624) P :=
  singular_series_finite_pos_evenPair (by decide : Even 624) P

theorem singular_series_finite_pos_evenPair_sixHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 626) P :=
  singular_series_finite_pos_evenPair (by decide : Even 626) P

theorem singular_series_finite_pos_evenPair_sixHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 628) P :=
  singular_series_finite_pos_evenPair (by decide : Even 628) P

theorem singular_series_finite_pos_evenPair_sixHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 630) P :=
  singular_series_finite_pos_evenPair (by decide : Even 630) P

theorem nu_p_sixHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 622) p = if p = 2 ∨ p ∣ 622 then 1 else 2 :=
  nu_p_evenPair (by decide : (622 : ℕ) ≠ 0) (by decide : Even 622) hp

theorem nu_p_sixHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 624) p = if p = 2 ∨ p ∣ 624 then 1 else 2 :=
  nu_p_evenPair (by decide : (624 : ℕ) ≠ 0) (by decide : Even 624) hp

theorem nu_p_sixHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 626) p = if p = 2 ∨ p ∣ 626 then 1 else 2 :=
  nu_p_evenPair (by decide : (626 : ℕ) ≠ 0) (by decide : Even 626) hp

theorem nu_p_sixHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 628) p = if p = 2 ∨ p ∣ 628 then 1 else 2 :=
  nu_p_evenPair (by decide : (628 : ℕ) ≠ 0) (by decide : Even 628) hp

theorem nu_p_sixHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 630) p = if p = 2 ∨ p ∣ 630 then 1 else 2 :=
  nu_p_evenPair (by decide : (630 : ℕ) ≠ 0) (by decide : Even 630) hp

theorem nu_p_sixHundredTwentyTwo_two : nu_p (evenPair 622) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 622)

theorem localFactor_sixHundredTwentyTwo_two : localFactor (evenPair 622) 2 = 2 :=
  localFactor_evenPair_two (by decide : (622 : ℕ) ≠ 0) (by decide : Even 622)

theorem nu_p_sixHundredThirty_two : nu_p (evenPair 630) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 630)

theorem localFactor_sixHundredThirty_two : localFactor (evenPair 630) 2 = 2 :=
  localFactor_evenPair_two (by decide : (630 : ℕ) ≠ 0) (by decide : Even 630)

end Brockian.SingularSeries.Gaps622630
