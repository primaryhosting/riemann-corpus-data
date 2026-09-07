/-
  Brockian/SingularSeriesGaps10921100.lean — even binary gaps n ∈ {1092, 1094, 1096, 1098, 1100}.

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

namespace Brockian.SingularSeries.Gaps10921100

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNinetyTwo : (evenPair 1092).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1092 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNinetyFour : (evenPair 1094).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1094 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNinetySix : (evenPair 1096).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1096 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNinetyEight : (evenPair 1098).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1098 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundred : (evenPair 1100).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1100 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNinetyTwo : IsAdmissible (evenPair 1092) :=
  isAdmissible_evenPair (by decide : Even 1092)

theorem isAdmissible_evenPair_oneThousandNinetyFour : IsAdmissible (evenPair 1094) :=
  isAdmissible_evenPair (by decide : Even 1094)

theorem isAdmissible_evenPair_oneThousandNinetySix : IsAdmissible (evenPair 1096) :=
  isAdmissible_evenPair (by decide : Even 1096)

theorem isAdmissible_evenPair_oneThousandNinetyEight : IsAdmissible (evenPair 1098) :=
  isAdmissible_evenPair (by decide : Even 1098)

theorem isAdmissible_evenPair_oneThousandOneHundred : IsAdmissible (evenPair 1100) :=
  isAdmissible_evenPair (by decide : Even 1100)

theorem singular_series_pos_evenPair_oneThousandNinetyTwo : 0 < singularSeries (evenPair 1092) :=
  singular_series_pos_evenPair (by decide : Even 1092)

theorem singular_series_pos_evenPair_oneThousandNinetyFour : 0 < singularSeries (evenPair 1094) :=
  singular_series_pos_evenPair (by decide : Even 1094)

theorem singular_series_pos_evenPair_oneThousandNinetySix : 0 < singularSeries (evenPair 1096) :=
  singular_series_pos_evenPair (by decide : Even 1096)

theorem singular_series_pos_evenPair_oneThousandNinetyEight : 0 < singularSeries (evenPair 1098) :=
  singular_series_pos_evenPair (by decide : Even 1098)

theorem singular_series_pos_evenPair_oneThousandOneHundred : 0 < singularSeries (evenPair 1100) :=
  singular_series_pos_evenPair (by decide : Even 1100)

theorem singular_series_finite_pos_evenPair_oneThousandNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1092) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1092) P

theorem singular_series_finite_pos_evenPair_oneThousandNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1094) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1094) P

theorem singular_series_finite_pos_evenPair_oneThousandNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1096) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1096) P

theorem singular_series_finite_pos_evenPair_oneThousandNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1098) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1098) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1100) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1100) P

theorem nu_p_oneThousandNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1092) p = if p = 2 ∨ p ∣ 1092 then 1 else 2 :=
  nu_p_evenPair (by decide : (1092 : ℕ) ≠ 0) (by decide : Even 1092) hp

theorem nu_p_oneThousandNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1094) p = if p = 2 ∨ p ∣ 1094 then 1 else 2 :=
  nu_p_evenPair (by decide : (1094 : ℕ) ≠ 0) (by decide : Even 1094) hp

theorem nu_p_oneThousandNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1096) p = if p = 2 ∨ p ∣ 1096 then 1 else 2 :=
  nu_p_evenPair (by decide : (1096 : ℕ) ≠ 0) (by decide : Even 1096) hp

theorem nu_p_oneThousandNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1098) p = if p = 2 ∨ p ∣ 1098 then 1 else 2 :=
  nu_p_evenPair (by decide : (1098 : ℕ) ≠ 0) (by decide : Even 1098) hp

theorem nu_p_oneThousandOneHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1100) p = if p = 2 ∨ p ∣ 1100 then 1 else 2 :=
  nu_p_evenPair (by decide : (1100 : ℕ) ≠ 0) (by decide : Even 1100) hp

theorem nu_p_oneThousandNinetyTwo_two : nu_p (evenPair 1092) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1092)

theorem localFactor_oneThousandNinetyTwo_two : localFactor (evenPair 1092) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1092 : ℕ) ≠ 0) (by decide : Even 1092)

theorem nu_p_oneThousandOneHundred_two : nu_p (evenPair 1100) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1100)

theorem localFactor_oneThousandOneHundred_two : localFactor (evenPair 1100) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1100 : ℕ) ≠ 0) (by decide : Even 1100)

end Brockian.SingularSeries.Gaps10921100
