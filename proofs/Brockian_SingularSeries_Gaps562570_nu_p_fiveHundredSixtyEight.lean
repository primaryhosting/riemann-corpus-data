/-
  Brockian/SingularSeriesGaps562570.lean — even binary gaps n ∈ {562, 564, 566, 568, 570}.

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

namespace Brockian.SingularSeries.Gaps562570

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiveHundredSixtyTwo : (evenPair 562).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (562 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredSixtyFour : (evenPair 564).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (564 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredSixtySix : (evenPair 566).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (566 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredSixtyEight : (evenPair 568).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (568 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredSeventy : (evenPair 570).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (570 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiveHundredSixtyTwo : IsAdmissible (evenPair 562) :=
  isAdmissible_evenPair (by decide : Even 562)

theorem isAdmissible_evenPair_fiveHundredSixtyFour : IsAdmissible (evenPair 564) :=
  isAdmissible_evenPair (by decide : Even 564)

theorem isAdmissible_evenPair_fiveHundredSixtySix : IsAdmissible (evenPair 566) :=
  isAdmissible_evenPair (by decide : Even 566)

theorem isAdmissible_evenPair_fiveHundredSixtyEight : IsAdmissible (evenPair 568) :=
  isAdmissible_evenPair (by decide : Even 568)

theorem isAdmissible_evenPair_fiveHundredSeventy : IsAdmissible (evenPair 570) :=
  isAdmissible_evenPair (by decide : Even 570)

theorem singular_series_pos_evenPair_fiveHundredSixtyTwo : 0 < singularSeries (evenPair 562) :=
  singular_series_pos_evenPair (by decide : Even 562)

theorem singular_series_pos_evenPair_fiveHundredSixtyFour : 0 < singularSeries (evenPair 564) :=
  singular_series_pos_evenPair (by decide : Even 564)

theorem singular_series_pos_evenPair_fiveHundredSixtySix : 0 < singularSeries (evenPair 566) :=
  singular_series_pos_evenPair (by decide : Even 566)

theorem singular_series_pos_evenPair_fiveHundredSixtyEight : 0 < singularSeries (evenPair 568) :=
  singular_series_pos_evenPair (by decide : Even 568)

theorem singular_series_pos_evenPair_fiveHundredSeventy : 0 < singularSeries (evenPair 570) :=
  singular_series_pos_evenPair (by decide : Even 570)

theorem singular_series_finite_pos_evenPair_fiveHundredSixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 562) P :=
  singular_series_finite_pos_evenPair (by decide : Even 562) P

theorem singular_series_finite_pos_evenPair_fiveHundredSixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 564) P :=
  singular_series_finite_pos_evenPair (by decide : Even 564) P

theorem singular_series_finite_pos_evenPair_fiveHundredSixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 566) P :=
  singular_series_finite_pos_evenPair (by decide : Even 566) P

theorem singular_series_finite_pos_evenPair_fiveHundredSixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 568) P :=
  singular_series_finite_pos_evenPair (by decide : Even 568) P

theorem singular_series_finite_pos_evenPair_fiveHundredSeventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 570) P :=
  singular_series_finite_pos_evenPair (by decide : Even 570) P

theorem nu_p_fiveHundredSixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 562) p = if p = 2 ∨ p ∣ 562 then 1 else 2 :=
  nu_p_evenPair (by decide : (562 : ℕ) ≠ 0) (by decide : Even 562) hp

theorem nu_p_fiveHundredSixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 564) p = if p = 2 ∨ p ∣ 564 then 1 else 2 :=
  nu_p_evenPair (by decide : (564 : ℕ) ≠ 0) (by decide : Even 564) hp

theorem nu_p_fiveHundredSixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 566) p = if p = 2 ∨ p ∣ 566 then 1 else 2 :=
  nu_p_evenPair (by decide : (566 : ℕ) ≠ 0) (by decide : Even 566) hp

theorem nu_p_fiveHundredSixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 568) p = if p = 2 ∨ p ∣ 568 then 1 else 2 :=
  nu_p_evenPair (by decide : (568 : ℕ) ≠ 0) (by decide : Even 568) hp

theorem nu_p_fiveHundredSeventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 570) p = if p = 2 ∨ p ∣ 570 then 1 else 2 :=
  nu_p_evenPair (by decide : (570 : ℕ) ≠ 0) (by decide : Even 570) hp

theorem nu_p_fiveHundredSixtyTwo_two : nu_p (evenPair 562) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 562)

theorem localFactor_fiveHundredSixtyTwo_two : localFactor (evenPair 562) 2 = 2 :=
  localFactor_evenPair_two (by decide : (562 : ℕ) ≠ 0) (by decide : Even 562)

theorem nu_p_fiveHundredSeventy_two : nu_p (evenPair 570) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 570)

theorem localFactor_fiveHundredSeventy_two : localFactor (evenPair 570) 2 = 2 :=
  localFactor_evenPair_two (by decide : (570 : ℕ) ≠ 0) (by decide : Even 570)

end Brockian.SingularSeries.Gaps562570
