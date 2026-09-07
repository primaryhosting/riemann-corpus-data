/-
  Brockian/SingularSeriesGaps21822190.lean — even binary gaps n ∈ {2182, 2184, 2186, 2188, 2190}.

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

namespace Brockian.SingularSeries.Gaps21822190

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandOneHundredEightyTwo : (evenPair 2182).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2182 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredEightyFour : (evenPair 2184).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2184 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredEightySix : (evenPair 2186).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2186 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredEightyEight : (evenPair 2188).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2188 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredNinety : (evenPair 2190).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2190 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandOneHundredEightyTwo : IsAdmissible (evenPair 2182) :=
  isAdmissible_evenPair (by decide : Even 2182)

theorem isAdmissible_evenPair_twoThousandOneHundredEightyFour : IsAdmissible (evenPair 2184) :=
  isAdmissible_evenPair (by decide : Even 2184)

theorem isAdmissible_evenPair_twoThousandOneHundredEightySix : IsAdmissible (evenPair 2186) :=
  isAdmissible_evenPair (by decide : Even 2186)

theorem isAdmissible_evenPair_twoThousandOneHundredEightyEight : IsAdmissible (evenPair 2188) :=
  isAdmissible_evenPair (by decide : Even 2188)

theorem isAdmissible_evenPair_twoThousandOneHundredNinety : IsAdmissible (evenPair 2190) :=
  isAdmissible_evenPair (by decide : Even 2190)

theorem singular_series_pos_evenPair_twoThousandOneHundredEightyTwo : 0 < singularSeries (evenPair 2182) :=
  singular_series_pos_evenPair (by decide : Even 2182)

theorem singular_series_pos_evenPair_twoThousandOneHundredEightyFour : 0 < singularSeries (evenPair 2184) :=
  singular_series_pos_evenPair (by decide : Even 2184)

theorem singular_series_pos_evenPair_twoThousandOneHundredEightySix : 0 < singularSeries (evenPair 2186) :=
  singular_series_pos_evenPair (by decide : Even 2186)

theorem singular_series_pos_evenPair_twoThousandOneHundredEightyEight : 0 < singularSeries (evenPair 2188) :=
  singular_series_pos_evenPair (by decide : Even 2188)

theorem singular_series_pos_evenPair_twoThousandOneHundredNinety : 0 < singularSeries (evenPair 2190) :=
  singular_series_pos_evenPair (by decide : Even 2190)

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredEightyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2182) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2182) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredEightyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2184) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2184) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredEightySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2186) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2186) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredEightyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2188) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2188) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredNinety (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2190) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2190) P

theorem nu_p_twoThousandOneHundredEightyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2182) p = if p = 2 ∨ p ∣ 2182 then 1 else 2 :=
  nu_p_evenPair (by decide : (2182 : ℕ) ≠ 0) (by decide : Even 2182) hp

theorem nu_p_twoThousandOneHundredEightyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2184) p = if p = 2 ∨ p ∣ 2184 then 1 else 2 :=
  nu_p_evenPair (by decide : (2184 : ℕ) ≠ 0) (by decide : Even 2184) hp

theorem nu_p_twoThousandOneHundredEightySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2186) p = if p = 2 ∨ p ∣ 2186 then 1 else 2 :=
  nu_p_evenPair (by decide : (2186 : ℕ) ≠ 0) (by decide : Even 2186) hp

theorem nu_p_twoThousandOneHundredEightyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2188) p = if p = 2 ∨ p ∣ 2188 then 1 else 2 :=
  nu_p_evenPair (by decide : (2188 : ℕ) ≠ 0) (by decide : Even 2188) hp

theorem nu_p_twoThousandOneHundredNinety (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2190) p = if p = 2 ∨ p ∣ 2190 then 1 else 2 :=
  nu_p_evenPair (by decide : (2190 : ℕ) ≠ 0) (by decide : Even 2190) hp

theorem nu_p_twoThousandOneHundredEightyTwo_two : nu_p (evenPair 2182) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2182)

theorem localFactor_twoThousandOneHundredEightyTwo_two : localFactor (evenPair 2182) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2182 : ℕ) ≠ 0) (by decide : Even 2182)

theorem nu_p_twoThousandOneHundredNinety_two : nu_p (evenPair 2190) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2190)

theorem localFactor_twoThousandOneHundredNinety_two : localFactor (evenPair 2190) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2190 : ℕ) ≠ 0) (by decide : Even 2190)

end Brockian.SingularSeries.Gaps21822190
