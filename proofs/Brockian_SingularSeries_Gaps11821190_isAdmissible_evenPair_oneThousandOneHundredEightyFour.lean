/-
  Brockian/SingularSeriesGaps11821190.lean — even binary gaps n ∈ {1182, 1184, 1186, 1188, 1190}.

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

namespace Brockian.SingularSeries.Gaps11821190

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandOneHundredEightyTwo : (evenPair 1182).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1182 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredEightyFour : (evenPair 1184).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1184 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredEightySix : (evenPair 1186).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1186 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredEightyEight : (evenPair 1188).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1188 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredNinety : (evenPair 1190).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1190 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandOneHundredEightyTwo : IsAdmissible (evenPair 1182) :=
  isAdmissible_evenPair (by decide : Even 1182)

theorem isAdmissible_evenPair_oneThousandOneHundredEightyFour : IsAdmissible (evenPair 1184) :=
  isAdmissible_evenPair (by decide : Even 1184)

theorem isAdmissible_evenPair_oneThousandOneHundredEightySix : IsAdmissible (evenPair 1186) :=
  isAdmissible_evenPair (by decide : Even 1186)

theorem isAdmissible_evenPair_oneThousandOneHundredEightyEight : IsAdmissible (evenPair 1188) :=
  isAdmissible_evenPair (by decide : Even 1188)

theorem isAdmissible_evenPair_oneThousandOneHundredNinety : IsAdmissible (evenPair 1190) :=
  isAdmissible_evenPair (by decide : Even 1190)

theorem singular_series_pos_evenPair_oneThousandOneHundredEightyTwo : 0 < singularSeries (evenPair 1182) :=
  singular_series_pos_evenPair (by decide : Even 1182)

theorem singular_series_pos_evenPair_oneThousandOneHundredEightyFour : 0 < singularSeries (evenPair 1184) :=
  singular_series_pos_evenPair (by decide : Even 1184)

theorem singular_series_pos_evenPair_oneThousandOneHundredEightySix : 0 < singularSeries (evenPair 1186) :=
  singular_series_pos_evenPair (by decide : Even 1186)

theorem singular_series_pos_evenPair_oneThousandOneHundredEightyEight : 0 < singularSeries (evenPair 1188) :=
  singular_series_pos_evenPair (by decide : Even 1188)

theorem singular_series_pos_evenPair_oneThousandOneHundredNinety : 0 < singularSeries (evenPair 1190) :=
  singular_series_pos_evenPair (by decide : Even 1190)

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1182) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1182) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1184) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1184) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1186) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1186) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1188) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1188) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1190) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1190) P

theorem nu_p_oneThousandOneHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1182) p = if p = 2 ∨ p ∣ 1182 then 1 else 2 :=
  nu_p_evenPair (by decide : (1182 : ℕ) ≠ 0) (by decide : Even 1182) hp

theorem nu_p_oneThousandOneHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1184) p = if p = 2 ∨ p ∣ 1184 then 1 else 2 :=
  nu_p_evenPair (by decide : (1184 : ℕ) ≠ 0) (by decide : Even 1184) hp

theorem nu_p_oneThousandOneHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1186) p = if p = 2 ∨ p ∣ 1186 then 1 else 2 :=
  nu_p_evenPair (by decide : (1186 : ℕ) ≠ 0) (by decide : Even 1186) hp

theorem nu_p_oneThousandOneHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1188) p = if p = 2 ∨ p ∣ 1188 then 1 else 2 :=
  nu_p_evenPair (by decide : (1188 : ℕ) ≠ 0) (by decide : Even 1188) hp

theorem nu_p_oneThousandOneHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1190) p = if p = 2 ∨ p ∣ 1190 then 1 else 2 :=
  nu_p_evenPair (by decide : (1190 : ℕ) ≠ 0) (by decide : Even 1190) hp

theorem nu_p_oneThousandOneHundredEightyTwo_two : nu_p (evenPair 1182) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1182)

theorem localFactor_oneThousandOneHundredEightyTwo_two : localFactor (evenPair 1182) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1182 : ℕ) ≠ 0) (by decide : Even 1182)

theorem nu_p_oneThousandOneHundredNinety_two : nu_p (evenPair 1190) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1190)

theorem localFactor_oneThousandOneHundredNinety_two : localFactor (evenPair 1190) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1190 : ℕ) ≠ 0) (by decide : Even 1190)

end Brockian.SingularSeries.Gaps11821190
