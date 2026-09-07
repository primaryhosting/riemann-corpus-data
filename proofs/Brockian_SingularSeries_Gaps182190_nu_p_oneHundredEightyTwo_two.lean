/-
  Brockian/SingularSeriesGaps182190.lean — even binary gaps n ∈ {182, 184, 186, 188, 190}.

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

namespace Brockian.SingularSeries.Gaps182190

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneHundredEightyTwo : (evenPair 182).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (182 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredEightyFour : (evenPair 184).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (184 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredEightySix : (evenPair 186).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (186 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredEightyEight : (evenPair 188).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (188 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredNinety : (evenPair 190).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (190 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneHundredEightyTwo : IsAdmissible (evenPair 182) :=
  isAdmissible_evenPair (by decide : Even 182)

theorem isAdmissible_evenPair_oneHundredEightyFour : IsAdmissible (evenPair 184) :=
  isAdmissible_evenPair (by decide : Even 184)

theorem isAdmissible_evenPair_oneHundredEightySix : IsAdmissible (evenPair 186) :=
  isAdmissible_evenPair (by decide : Even 186)

theorem isAdmissible_evenPair_oneHundredEightyEight : IsAdmissible (evenPair 188) :=
  isAdmissible_evenPair (by decide : Even 188)

theorem isAdmissible_evenPair_oneHundredNinety : IsAdmissible (evenPair 190) :=
  isAdmissible_evenPair (by decide : Even 190)

theorem singular_series_pos_evenPair_oneHundredEightyTwo : 0 < singularSeries (evenPair 182) :=
  singular_series_pos_evenPair (by decide : Even 182)

theorem singular_series_pos_evenPair_oneHundredEightyFour : 0 < singularSeries (evenPair 184) :=
  singular_series_pos_evenPair (by decide : Even 184)

theorem singular_series_pos_evenPair_oneHundredEightySix : 0 < singularSeries (evenPair 186) :=
  singular_series_pos_evenPair (by decide : Even 186)

theorem singular_series_pos_evenPair_oneHundredEightyEight : 0 < singularSeries (evenPair 188) :=
  singular_series_pos_evenPair (by decide : Even 188)

theorem singular_series_pos_evenPair_oneHundredNinety : 0 < singularSeries (evenPair 190) :=
  singular_series_pos_evenPair (by decide : Even 190)

theorem singular_series_finite_pos_evenPair_oneHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 182) P :=
  singular_series_finite_pos_evenPair (by decide : Even 182) P

theorem singular_series_finite_pos_evenPair_oneHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 184) P :=
  singular_series_finite_pos_evenPair (by decide : Even 184) P

theorem singular_series_finite_pos_evenPair_oneHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 186) P :=
  singular_series_finite_pos_evenPair (by decide : Even 186) P

theorem singular_series_finite_pos_evenPair_oneHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 188) P :=
  singular_series_finite_pos_evenPair (by decide : Even 188) P

theorem singular_series_finite_pos_evenPair_oneHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 190) P :=
  singular_series_finite_pos_evenPair (by decide : Even 190) P

theorem nu_p_oneHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 182) p = if p = 2 ∨ p ∣ 182 then 1 else 2 :=
  nu_p_evenPair (by decide : (182 : ℕ) ≠ 0) (by decide : Even 182) hp

theorem nu_p_oneHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 184) p = if p = 2 ∨ p ∣ 184 then 1 else 2 :=
  nu_p_evenPair (by decide : (184 : ℕ) ≠ 0) (by decide : Even 184) hp

theorem nu_p_oneHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 186) p = if p = 2 ∨ p ∣ 186 then 1 else 2 :=
  nu_p_evenPair (by decide : (186 : ℕ) ≠ 0) (by decide : Even 186) hp

theorem nu_p_oneHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 188) p = if p = 2 ∨ p ∣ 188 then 1 else 2 :=
  nu_p_evenPair (by decide : (188 : ℕ) ≠ 0) (by decide : Even 188) hp

theorem nu_p_oneHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 190) p = if p = 2 ∨ p ∣ 190 then 1 else 2 :=
  nu_p_evenPair (by decide : (190 : ℕ) ≠ 0) (by decide : Even 190) hp

theorem nu_p_oneHundredEightyTwo_two : nu_p (evenPair 182) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 182)

theorem localFactor_oneHundredEightyTwo_two : localFactor (evenPair 182) 2 = 2 :=
  localFactor_evenPair_two (by decide : (182 : ℕ) ≠ 0) (by decide : Even 182)

theorem nu_p_oneHundredNinety_two : nu_p (evenPair 190) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 190)

theorem localFactor_oneHundredNinety_two : localFactor (evenPair 190) 2 = 2 :=
  localFactor_evenPair_two (by decide : (190 : ℕ) ≠ 0) (by decide : Even 190)

end Brockian.SingularSeries.Gaps182190
