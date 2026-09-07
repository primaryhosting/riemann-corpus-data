/-
  Brockian/SingularSeriesGaps982990.lean — even binary gaps n ∈ {982, 984, 986, 988, 990}.

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

namespace Brockian.SingularSeries.Gaps982990

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_nineHundredEightyTwo : (evenPair 982).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (982 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredEightyFour : (evenPair 984).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (984 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredEightySix : (evenPair 986).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (986 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredEightyEight : (evenPair 988).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (988 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredNinety : (evenPair 990).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (990 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_nineHundredEightyTwo : IsAdmissible (evenPair 982) :=
  isAdmissible_evenPair (by decide : Even 982)

theorem isAdmissible_evenPair_nineHundredEightyFour : IsAdmissible (evenPair 984) :=
  isAdmissible_evenPair (by decide : Even 984)

theorem isAdmissible_evenPair_nineHundredEightySix : IsAdmissible (evenPair 986) :=
  isAdmissible_evenPair (by decide : Even 986)

theorem isAdmissible_evenPair_nineHundredEightyEight : IsAdmissible (evenPair 988) :=
  isAdmissible_evenPair (by decide : Even 988)

theorem isAdmissible_evenPair_nineHundredNinety : IsAdmissible (evenPair 990) :=
  isAdmissible_evenPair (by decide : Even 990)

theorem singular_series_pos_evenPair_nineHundredEightyTwo : 0 < singularSeries (evenPair 982) :=
  singular_series_pos_evenPair (by decide : Even 982)

theorem singular_series_pos_evenPair_nineHundredEightyFour : 0 < singularSeries (evenPair 984) :=
  singular_series_pos_evenPair (by decide : Even 984)

theorem singular_series_pos_evenPair_nineHundredEightySix : 0 < singularSeries (evenPair 986) :=
  singular_series_pos_evenPair (by decide : Even 986)

theorem singular_series_pos_evenPair_nineHundredEightyEight : 0 < singularSeries (evenPair 988) :=
  singular_series_pos_evenPair (by decide : Even 988)

theorem singular_series_pos_evenPair_nineHundredNinety : 0 < singularSeries (evenPair 990) :=
  singular_series_pos_evenPair (by decide : Even 990)

theorem singular_series_finite_pos_evenPair_nineHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 982) P :=
  singular_series_finite_pos_evenPair (by decide : Even 982) P

theorem singular_series_finite_pos_evenPair_nineHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 984) P :=
  singular_series_finite_pos_evenPair (by decide : Even 984) P

theorem singular_series_finite_pos_evenPair_nineHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 986) P :=
  singular_series_finite_pos_evenPair (by decide : Even 986) P

theorem singular_series_finite_pos_evenPair_nineHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 988) P :=
  singular_series_finite_pos_evenPair (by decide : Even 988) P

theorem singular_series_finite_pos_evenPair_nineHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 990) P :=
  singular_series_finite_pos_evenPair (by decide : Even 990) P

theorem nu_p_nineHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 982) p = if p = 2 ∨ p ∣ 982 then 1 else 2 :=
  nu_p_evenPair (by decide : (982 : ℕ) ≠ 0) (by decide : Even 982) hp

theorem nu_p_nineHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 984) p = if p = 2 ∨ p ∣ 984 then 1 else 2 :=
  nu_p_evenPair (by decide : (984 : ℕ) ≠ 0) (by decide : Even 984) hp

theorem nu_p_nineHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 986) p = if p = 2 ∨ p ∣ 986 then 1 else 2 :=
  nu_p_evenPair (by decide : (986 : ℕ) ≠ 0) (by decide : Even 986) hp

theorem nu_p_nineHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 988) p = if p = 2 ∨ p ∣ 988 then 1 else 2 :=
  nu_p_evenPair (by decide : (988 : ℕ) ≠ 0) (by decide : Even 988) hp

theorem nu_p_nineHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 990) p = if p = 2 ∨ p ∣ 990 then 1 else 2 :=
  nu_p_evenPair (by decide : (990 : ℕ) ≠ 0) (by decide : Even 990) hp

theorem nu_p_nineHundredEightyTwo_two : nu_p (evenPair 982) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 982)

theorem localFactor_nineHundredEightyTwo_two : localFactor (evenPair 982) 2 = 2 :=
  localFactor_evenPair_two (by decide : (982 : ℕ) ≠ 0) (by decide : Even 982)

theorem nu_p_nineHundredNinety_two : nu_p (evenPair 990) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 990)

theorem localFactor_nineHundredNinety_two : localFactor (evenPair 990) 2 = 2 :=
  localFactor_evenPair_two (by decide : (990 : ℕ) ≠ 0) (by decide : Even 990)

end Brockian.SingularSeries.Gaps982990
