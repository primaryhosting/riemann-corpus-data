/-
  Brockian/SingularSeriesGaps592600.lean — even binary gaps n ∈ {592, 594, 596, 598, 600}.

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

namespace Brockian.SingularSeries.Gaps592600

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiveHundredNinetyTwo : (evenPair 592).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (592 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredNinetyFour : (evenPair 594).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (594 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredNinetySix : (evenPair 596).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (596 : ℕ) ≠ 0)

theorem evenPair_card_fiveHundredNinetyEight : (evenPair 598).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (598 : ℕ) ≠ 0)

theorem evenPair_card_sixHundred : (evenPair 600).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (600 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiveHundredNinetyTwo : IsAdmissible (evenPair 592) :=
  isAdmissible_evenPair (by decide : Even 592)

theorem isAdmissible_evenPair_fiveHundredNinetyFour : IsAdmissible (evenPair 594) :=
  isAdmissible_evenPair (by decide : Even 594)

theorem isAdmissible_evenPair_fiveHundredNinetySix : IsAdmissible (evenPair 596) :=
  isAdmissible_evenPair (by decide : Even 596)

theorem isAdmissible_evenPair_fiveHundredNinetyEight : IsAdmissible (evenPair 598) :=
  isAdmissible_evenPair (by decide : Even 598)

theorem isAdmissible_evenPair_sixHundred : IsAdmissible (evenPair 600) :=
  isAdmissible_evenPair (by decide : Even 600)

theorem singular_series_pos_evenPair_fiveHundredNinetyTwo : 0 < singularSeries (evenPair 592) :=
  singular_series_pos_evenPair (by decide : Even 592)

theorem singular_series_pos_evenPair_fiveHundredNinetyFour : 0 < singularSeries (evenPair 594) :=
  singular_series_pos_evenPair (by decide : Even 594)

theorem singular_series_pos_evenPair_fiveHundredNinetySix : 0 < singularSeries (evenPair 596) :=
  singular_series_pos_evenPair (by decide : Even 596)

theorem singular_series_pos_evenPair_fiveHundredNinetyEight : 0 < singularSeries (evenPair 598) :=
  singular_series_pos_evenPair (by decide : Even 598)

theorem singular_series_pos_evenPair_sixHundred : 0 < singularSeries (evenPair 600) :=
  singular_series_pos_evenPair (by decide : Even 600)

theorem singular_series_finite_pos_evenPair_fiveHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 592) P :=
  singular_series_finite_pos_evenPair (by decide : Even 592) P

theorem singular_series_finite_pos_evenPair_fiveHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 594) P :=
  singular_series_finite_pos_evenPair (by decide : Even 594) P

theorem singular_series_finite_pos_evenPair_fiveHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 596) P :=
  singular_series_finite_pos_evenPair (by decide : Even 596) P

theorem singular_series_finite_pos_evenPair_fiveHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 598) P :=
  singular_series_finite_pos_evenPair (by decide : Even 598) P

theorem singular_series_finite_pos_evenPair_sixHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 600) P :=
  singular_series_finite_pos_evenPair (by decide : Even 600) P

theorem nu_p_fiveHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 592) p = if p = 2 ∨ p ∣ 592 then 1 else 2 :=
  nu_p_evenPair (by decide : (592 : ℕ) ≠ 0) (by decide : Even 592) hp

theorem nu_p_fiveHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 594) p = if p = 2 ∨ p ∣ 594 then 1 else 2 :=
  nu_p_evenPair (by decide : (594 : ℕ) ≠ 0) (by decide : Even 594) hp

theorem nu_p_fiveHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 596) p = if p = 2 ∨ p ∣ 596 then 1 else 2 :=
  nu_p_evenPair (by decide : (596 : ℕ) ≠ 0) (by decide : Even 596) hp

theorem nu_p_fiveHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 598) p = if p = 2 ∨ p ∣ 598 then 1 else 2 :=
  nu_p_evenPair (by decide : (598 : ℕ) ≠ 0) (by decide : Even 598) hp

theorem nu_p_sixHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 600) p = if p = 2 ∨ p ∣ 600 then 1 else 2 :=
  nu_p_evenPair (by decide : (600 : ℕ) ≠ 0) (by decide : Even 600) hp

theorem nu_p_fiveHundredNinetyTwo_two : nu_p (evenPair 592) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 592)

theorem localFactor_fiveHundredNinetyTwo_two : localFactor (evenPair 592) 2 = 2 :=
  localFactor_evenPair_two (by decide : (592 : ℕ) ≠ 0) (by decide : Even 592)

theorem nu_p_sixHundred_two : nu_p (evenPair 600) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 600)

theorem localFactor_sixHundred_two : localFactor (evenPair 600) 2 = 2 :=
  localFactor_evenPair_two (by decide : (600 : ℕ) ≠ 0) (by decide : Even 600)

end Brockian.SingularSeries.Gaps592600
