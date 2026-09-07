/-
  Brockian/SingularSeriesGaps832840.lean — even binary gaps n ∈ {832, 834, 836, 838, 840}.

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

namespace Brockian.SingularSeries.Gaps832840

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightHundredThirtyTwo : (evenPair 832).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (832 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredThirtyFour : (evenPair 834).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (834 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredThirtySix : (evenPair 836).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (836 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredThirtyEight : (evenPair 838).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (838 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredForty : (evenPair 840).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (840 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightHundredThirtyTwo : IsAdmissible (evenPair 832) :=
  isAdmissible_evenPair (by decide : Even 832)

theorem isAdmissible_evenPair_eightHundredThirtyFour : IsAdmissible (evenPair 834) :=
  isAdmissible_evenPair (by decide : Even 834)

theorem isAdmissible_evenPair_eightHundredThirtySix : IsAdmissible (evenPair 836) :=
  isAdmissible_evenPair (by decide : Even 836)

theorem isAdmissible_evenPair_eightHundredThirtyEight : IsAdmissible (evenPair 838) :=
  isAdmissible_evenPair (by decide : Even 838)

theorem isAdmissible_evenPair_eightHundredForty : IsAdmissible (evenPair 840) :=
  isAdmissible_evenPair (by decide : Even 840)

theorem singular_series_pos_evenPair_eightHundredThirtyTwo : 0 < singularSeries (evenPair 832) :=
  singular_series_pos_evenPair (by decide : Even 832)

theorem singular_series_pos_evenPair_eightHundredThirtyFour : 0 < singularSeries (evenPair 834) :=
  singular_series_pos_evenPair (by decide : Even 834)

theorem singular_series_pos_evenPair_eightHundredThirtySix : 0 < singularSeries (evenPair 836) :=
  singular_series_pos_evenPair (by decide : Even 836)

theorem singular_series_pos_evenPair_eightHundredThirtyEight : 0 < singularSeries (evenPair 838) :=
  singular_series_pos_evenPair (by decide : Even 838)

theorem singular_series_pos_evenPair_eightHundredForty : 0 < singularSeries (evenPair 840) :=
  singular_series_pos_evenPair (by decide : Even 840)

theorem singular_series_finite_pos_evenPair_eightHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 832) P :=
  singular_series_finite_pos_evenPair (by decide : Even 832) P

theorem singular_series_finite_pos_evenPair_eightHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 834) P :=
  singular_series_finite_pos_evenPair (by decide : Even 834) P

theorem singular_series_finite_pos_evenPair_eightHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 836) P :=
  singular_series_finite_pos_evenPair (by decide : Even 836) P

theorem singular_series_finite_pos_evenPair_eightHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 838) P :=
  singular_series_finite_pos_evenPair (by decide : Even 838) P

theorem singular_series_finite_pos_evenPair_eightHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 840) P :=
  singular_series_finite_pos_evenPair (by decide : Even 840) P

theorem nu_p_eightHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 832) p = if p = 2 ∨ p ∣ 832 then 1 else 2 :=
  nu_p_evenPair (by decide : (832 : ℕ) ≠ 0) (by decide : Even 832) hp

theorem nu_p_eightHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 834) p = if p = 2 ∨ p ∣ 834 then 1 else 2 :=
  nu_p_evenPair (by decide : (834 : ℕ) ≠ 0) (by decide : Even 834) hp

theorem nu_p_eightHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 836) p = if p = 2 ∨ p ∣ 836 then 1 else 2 :=
  nu_p_evenPair (by decide : (836 : ℕ) ≠ 0) (by decide : Even 836) hp

theorem nu_p_eightHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 838) p = if p = 2 ∨ p ∣ 838 then 1 else 2 :=
  nu_p_evenPair (by decide : (838 : ℕ) ≠ 0) (by decide : Even 838) hp

theorem nu_p_eightHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 840) p = if p = 2 ∨ p ∣ 840 then 1 else 2 :=
  nu_p_evenPair (by decide : (840 : ℕ) ≠ 0) (by decide : Even 840) hp

theorem nu_p_eightHundredThirtyTwo_two : nu_p (evenPair 832) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 832)

theorem localFactor_eightHundredThirtyTwo_two : localFactor (evenPair 832) 2 = 2 :=
  localFactor_evenPair_two (by decide : (832 : ℕ) ≠ 0) (by decide : Even 832)

theorem nu_p_eightHundredForty_two : nu_p (evenPair 840) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 840)

theorem localFactor_eightHundredForty_two : localFactor (evenPair 840) 2 = 2 :=
  localFactor_evenPair_two (by decide : (840 : ℕ) ≠ 0) (by decide : Even 840)

end Brockian.SingularSeries.Gaps832840
