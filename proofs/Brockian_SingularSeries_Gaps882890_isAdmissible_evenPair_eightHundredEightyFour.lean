/-
  Brockian/SingularSeriesGaps882890.lean — even binary gaps n ∈ {882, 884, 886, 888, 890}.

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

namespace Brockian.SingularSeries.Gaps882890

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightHundredEightyTwo : (evenPair 882).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (882 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredEightyFour : (evenPair 884).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (884 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredEightySix : (evenPair 886).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (886 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredEightyEight : (evenPair 888).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (888 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredNinety : (evenPair 890).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (890 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightHundredEightyTwo : IsAdmissible (evenPair 882) :=
  isAdmissible_evenPair (by decide : Even 882)

theorem isAdmissible_evenPair_eightHundredEightyFour : IsAdmissible (evenPair 884) :=
  isAdmissible_evenPair (by decide : Even 884)

theorem isAdmissible_evenPair_eightHundredEightySix : IsAdmissible (evenPair 886) :=
  isAdmissible_evenPair (by decide : Even 886)

theorem isAdmissible_evenPair_eightHundredEightyEight : IsAdmissible (evenPair 888) :=
  isAdmissible_evenPair (by decide : Even 888)

theorem isAdmissible_evenPair_eightHundredNinety : IsAdmissible (evenPair 890) :=
  isAdmissible_evenPair (by decide : Even 890)

theorem singular_series_pos_evenPair_eightHundredEightyTwo : 0 < singularSeries (evenPair 882) :=
  singular_series_pos_evenPair (by decide : Even 882)

theorem singular_series_pos_evenPair_eightHundredEightyFour : 0 < singularSeries (evenPair 884) :=
  singular_series_pos_evenPair (by decide : Even 884)

theorem singular_series_pos_evenPair_eightHundredEightySix : 0 < singularSeries (evenPair 886) :=
  singular_series_pos_evenPair (by decide : Even 886)

theorem singular_series_pos_evenPair_eightHundredEightyEight : 0 < singularSeries (evenPair 888) :=
  singular_series_pos_evenPair (by decide : Even 888)

theorem singular_series_pos_evenPair_eightHundredNinety : 0 < singularSeries (evenPair 890) :=
  singular_series_pos_evenPair (by decide : Even 890)

theorem singular_series_finite_pos_evenPair_eightHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 882) P :=
  singular_series_finite_pos_evenPair (by decide : Even 882) P

theorem singular_series_finite_pos_evenPair_eightHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 884) P :=
  singular_series_finite_pos_evenPair (by decide : Even 884) P

theorem singular_series_finite_pos_evenPair_eightHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 886) P :=
  singular_series_finite_pos_evenPair (by decide : Even 886) P

theorem singular_series_finite_pos_evenPair_eightHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 888) P :=
  singular_series_finite_pos_evenPair (by decide : Even 888) P

theorem singular_series_finite_pos_evenPair_eightHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 890) P :=
  singular_series_finite_pos_evenPair (by decide : Even 890) P

theorem nu_p_eightHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 882) p = if p = 2 ∨ p ∣ 882 then 1 else 2 :=
  nu_p_evenPair (by decide : (882 : ℕ) ≠ 0) (by decide : Even 882) hp

theorem nu_p_eightHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 884) p = if p = 2 ∨ p ∣ 884 then 1 else 2 :=
  nu_p_evenPair (by decide : (884 : ℕ) ≠ 0) (by decide : Even 884) hp

theorem nu_p_eightHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 886) p = if p = 2 ∨ p ∣ 886 then 1 else 2 :=
  nu_p_evenPair (by decide : (886 : ℕ) ≠ 0) (by decide : Even 886) hp

theorem nu_p_eightHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 888) p = if p = 2 ∨ p ∣ 888 then 1 else 2 :=
  nu_p_evenPair (by decide : (888 : ℕ) ≠ 0) (by decide : Even 888) hp

theorem nu_p_eightHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 890) p = if p = 2 ∨ p ∣ 890 then 1 else 2 :=
  nu_p_evenPair (by decide : (890 : ℕ) ≠ 0) (by decide : Even 890) hp

theorem nu_p_eightHundredEightyTwo_two : nu_p (evenPair 882) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 882)

theorem localFactor_eightHundredEightyTwo_two : localFactor (evenPair 882) 2 = 2 :=
  localFactor_evenPair_two (by decide : (882 : ℕ) ≠ 0) (by decide : Even 882)

theorem nu_p_eightHundredNinety_two : nu_p (evenPair 890) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 890)

theorem localFactor_eightHundredNinety_two : localFactor (evenPair 890) 2 = 2 :=
  localFactor_evenPair_two (by decide : (890 : ℕ) ≠ 0) (by decide : Even 890)

end Brockian.SingularSeries.Gaps882890
