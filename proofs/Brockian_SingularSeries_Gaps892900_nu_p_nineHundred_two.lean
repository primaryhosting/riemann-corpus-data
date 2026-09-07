/-
  Brockian/SingularSeriesGaps892900.lean — even binary gaps n ∈ {892, 894, 896, 898, 900}.

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

namespace Brockian.SingularSeries.Gaps892900

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightHundredNinetyTwo : (evenPair 892).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (892 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredNinetyFour : (evenPair 894).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (894 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredNinetySix : (evenPair 896).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (896 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredNinetyEight : (evenPair 898).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (898 : ℕ) ≠ 0)

theorem evenPair_card_nineHundred : (evenPair 900).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (900 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightHundredNinetyTwo : IsAdmissible (evenPair 892) :=
  isAdmissible_evenPair (by decide : Even 892)

theorem isAdmissible_evenPair_eightHundredNinetyFour : IsAdmissible (evenPair 894) :=
  isAdmissible_evenPair (by decide : Even 894)

theorem isAdmissible_evenPair_eightHundredNinetySix : IsAdmissible (evenPair 896) :=
  isAdmissible_evenPair (by decide : Even 896)

theorem isAdmissible_evenPair_eightHundredNinetyEight : IsAdmissible (evenPair 898) :=
  isAdmissible_evenPair (by decide : Even 898)

theorem isAdmissible_evenPair_nineHundred : IsAdmissible (evenPair 900) :=
  isAdmissible_evenPair (by decide : Even 900)

theorem singular_series_pos_evenPair_eightHundredNinetyTwo : 0 < singularSeries (evenPair 892) :=
  singular_series_pos_evenPair (by decide : Even 892)

theorem singular_series_pos_evenPair_eightHundredNinetyFour : 0 < singularSeries (evenPair 894) :=
  singular_series_pos_evenPair (by decide : Even 894)

theorem singular_series_pos_evenPair_eightHundredNinetySix : 0 < singularSeries (evenPair 896) :=
  singular_series_pos_evenPair (by decide : Even 896)

theorem singular_series_pos_evenPair_eightHundredNinetyEight : 0 < singularSeries (evenPair 898) :=
  singular_series_pos_evenPair (by decide : Even 898)

theorem singular_series_pos_evenPair_nineHundred : 0 < singularSeries (evenPair 900) :=
  singular_series_pos_evenPair (by decide : Even 900)

theorem singular_series_finite_pos_evenPair_eightHundredNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 892) P :=
  singular_series_finite_pos_evenPair (by decide : Even 892) P

theorem singular_series_finite_pos_evenPair_eightHundredNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 894) P :=
  singular_series_finite_pos_evenPair (by decide : Even 894) P

theorem singular_series_finite_pos_evenPair_eightHundredNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 896) P :=
  singular_series_finite_pos_evenPair (by decide : Even 896) P

theorem singular_series_finite_pos_evenPair_eightHundredNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 898) P :=
  singular_series_finite_pos_evenPair (by decide : Even 898) P

theorem singular_series_finite_pos_evenPair_nineHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 900) P :=
  singular_series_finite_pos_evenPair (by decide : Even 900) P

theorem nu_p_eightHundredNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 892) p = if p = 2 ∨ p ∣ 892 then 1 else 2 :=
  nu_p_evenPair (by decide : (892 : ℕ) ≠ 0) (by decide : Even 892) hp

theorem nu_p_eightHundredNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 894) p = if p = 2 ∨ p ∣ 894 then 1 else 2 :=
  nu_p_evenPair (by decide : (894 : ℕ) ≠ 0) (by decide : Even 894) hp

theorem nu_p_eightHundredNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 896) p = if p = 2 ∨ p ∣ 896 then 1 else 2 :=
  nu_p_evenPair (by decide : (896 : ℕ) ≠ 0) (by decide : Even 896) hp

theorem nu_p_eightHundredNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 898) p = if p = 2 ∨ p ∣ 898 then 1 else 2 :=
  nu_p_evenPair (by decide : (898 : ℕ) ≠ 0) (by decide : Even 898) hp

theorem nu_p_nineHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 900) p = if p = 2 ∨ p ∣ 900 then 1 else 2 :=
  nu_p_evenPair (by decide : (900 : ℕ) ≠ 0) (by decide : Even 900) hp

theorem nu_p_eightHundredNinetyTwo_two : nu_p (evenPair 892) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 892)

theorem localFactor_eightHundredNinetyTwo_two : localFactor (evenPair 892) 2 = 2 :=
  localFactor_evenPair_two (by decide : (892 : ℕ) ≠ 0) (by decide : Even 892)

theorem nu_p_nineHundred_two : nu_p (evenPair 900) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 900)

theorem localFactor_nineHundred_two : localFactor (evenPair 900) 2 = 2 :=
  localFactor_evenPair_two (by decide : (900 : ℕ) ≠ 0) (by decide : Even 900)

end Brockian.SingularSeries.Gaps892900
