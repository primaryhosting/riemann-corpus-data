/-
  Brockian/SingularSeriesGaps732740.lean — even binary gaps n ∈ {732, 734, 736, 738, 740}.

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

namespace Brockian.SingularSeries.Gaps732740

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sevenHundredThirtyTwo : (evenPair 732).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (732 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredThirtyFour : (evenPair 734).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (734 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredThirtySix : (evenPair 736).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (736 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredThirtyEight : (evenPair 738).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (738 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredForty : (evenPair 740).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (740 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sevenHundredThirtyTwo : IsAdmissible (evenPair 732) :=
  isAdmissible_evenPair (by decide : Even 732)

theorem isAdmissible_evenPair_sevenHundredThirtyFour : IsAdmissible (evenPair 734) :=
  isAdmissible_evenPair (by decide : Even 734)

theorem isAdmissible_evenPair_sevenHundredThirtySix : IsAdmissible (evenPair 736) :=
  isAdmissible_evenPair (by decide : Even 736)

theorem isAdmissible_evenPair_sevenHundredThirtyEight : IsAdmissible (evenPair 738) :=
  isAdmissible_evenPair (by decide : Even 738)

theorem isAdmissible_evenPair_sevenHundredForty : IsAdmissible (evenPair 740) :=
  isAdmissible_evenPair (by decide : Even 740)

theorem singular_series_pos_evenPair_sevenHundredThirtyTwo : 0 < singularSeries (evenPair 732) :=
  singular_series_pos_evenPair (by decide : Even 732)

theorem singular_series_pos_evenPair_sevenHundredThirtyFour : 0 < singularSeries (evenPair 734) :=
  singular_series_pos_evenPair (by decide : Even 734)

theorem singular_series_pos_evenPair_sevenHundredThirtySix : 0 < singularSeries (evenPair 736) :=
  singular_series_pos_evenPair (by decide : Even 736)

theorem singular_series_pos_evenPair_sevenHundredThirtyEight : 0 < singularSeries (evenPair 738) :=
  singular_series_pos_evenPair (by decide : Even 738)

theorem singular_series_pos_evenPair_sevenHundredForty : 0 < singularSeries (evenPair 740) :=
  singular_series_pos_evenPair (by decide : Even 740)

theorem singular_series_finite_pos_evenPair_sevenHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 732) P :=
  singular_series_finite_pos_evenPair (by decide : Even 732) P

theorem singular_series_finite_pos_evenPair_sevenHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 734) P :=
  singular_series_finite_pos_evenPair (by decide : Even 734) P

theorem singular_series_finite_pos_evenPair_sevenHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 736) P :=
  singular_series_finite_pos_evenPair (by decide : Even 736) P

theorem singular_series_finite_pos_evenPair_sevenHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 738) P :=
  singular_series_finite_pos_evenPair (by decide : Even 738) P

theorem singular_series_finite_pos_evenPair_sevenHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 740) P :=
  singular_series_finite_pos_evenPair (by decide : Even 740) P

theorem nu_p_sevenHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 732) p = if p = 2 ∨ p ∣ 732 then 1 else 2 :=
  nu_p_evenPair (by decide : (732 : ℕ) ≠ 0) (by decide : Even 732) hp

theorem nu_p_sevenHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 734) p = if p = 2 ∨ p ∣ 734 then 1 else 2 :=
  nu_p_evenPair (by decide : (734 : ℕ) ≠ 0) (by decide : Even 734) hp

theorem nu_p_sevenHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 736) p = if p = 2 ∨ p ∣ 736 then 1 else 2 :=
  nu_p_evenPair (by decide : (736 : ℕ) ≠ 0) (by decide : Even 736) hp

theorem nu_p_sevenHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 738) p = if p = 2 ∨ p ∣ 738 then 1 else 2 :=
  nu_p_evenPair (by decide : (738 : ℕ) ≠ 0) (by decide : Even 738) hp

theorem nu_p_sevenHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 740) p = if p = 2 ∨ p ∣ 740 then 1 else 2 :=
  nu_p_evenPair (by decide : (740 : ℕ) ≠ 0) (by decide : Even 740) hp

theorem nu_p_sevenHundredThirtyTwo_two : nu_p (evenPair 732) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 732)

theorem localFactor_sevenHundredThirtyTwo_two : localFactor (evenPair 732) 2 = 2 :=
  localFactor_evenPair_two (by decide : (732 : ℕ) ≠ 0) (by decide : Even 732)

theorem nu_p_sevenHundredForty_two : nu_p (evenPair 740) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 740)

theorem localFactor_sevenHundredForty_two : localFactor (evenPair 740) 2 = 2 :=
  localFactor_evenPair_two (by decide : (740 : ℕ) ≠ 0) (by decide : Even 740)

end Brockian.SingularSeries.Gaps732740
