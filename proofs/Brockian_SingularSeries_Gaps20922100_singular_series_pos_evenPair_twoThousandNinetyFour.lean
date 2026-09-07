/-
  Brockian/SingularSeriesGaps20922100.lean — even binary gaps n ∈ {2092, 2094, 2096, 2098, 2100}.

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

namespace Brockian.SingularSeries.Gaps20922100

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandNinetyTwo : (evenPair 2092).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2092 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandNinetyFour : (evenPair 2094).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2094 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandNinetySix : (evenPair 2096).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2096 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandNinetyEight : (evenPair 2098).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2098 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundred : (evenPair 2100).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2100 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandNinetyTwo : IsAdmissible (evenPair 2092) :=
  isAdmissible_evenPair (by decide : Even 2092)

theorem isAdmissible_evenPair_twoThousandNinetyFour : IsAdmissible (evenPair 2094) :=
  isAdmissible_evenPair (by decide : Even 2094)

theorem isAdmissible_evenPair_twoThousandNinetySix : IsAdmissible (evenPair 2096) :=
  isAdmissible_evenPair (by decide : Even 2096)

theorem isAdmissible_evenPair_twoThousandNinetyEight : IsAdmissible (evenPair 2098) :=
  isAdmissible_evenPair (by decide : Even 2098)

theorem isAdmissible_evenPair_twoThousandOneHundred : IsAdmissible (evenPair 2100) :=
  isAdmissible_evenPair (by decide : Even 2100)

theorem singular_series_pos_evenPair_twoThousandNinetyTwo : 0 < singularSeries (evenPair 2092) :=
  singular_series_pos_evenPair (by decide : Even 2092)

theorem singular_series_pos_evenPair_twoThousandNinetyFour : 0 < singularSeries (evenPair 2094) :=
  singular_series_pos_evenPair (by decide : Even 2094)

theorem singular_series_pos_evenPair_twoThousandNinetySix : 0 < singularSeries (evenPair 2096) :=
  singular_series_pos_evenPair (by decide : Even 2096)

theorem singular_series_pos_evenPair_twoThousandNinetyEight : 0 < singularSeries (evenPair 2098) :=
  singular_series_pos_evenPair (by decide : Even 2098)

theorem singular_series_pos_evenPair_twoThousandOneHundred : 0 < singularSeries (evenPair 2100) :=
  singular_series_pos_evenPair (by decide : Even 2100)

theorem singular_series_finite_pos_evenPair_twoThousandNinetyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2092) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2092) P

theorem singular_series_finite_pos_evenPair_twoThousandNinetyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2094) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2094) P

theorem singular_series_finite_pos_evenPair_twoThousandNinetySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2096) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2096) P

theorem singular_series_finite_pos_evenPair_twoThousandNinetyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2098) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2098) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundred (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2100) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2100) P

theorem nu_p_twoThousandNinetyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2092) p = if p = 2 ∨ p ∣ 2092 then 1 else 2 :=
  nu_p_evenPair (by decide : (2092 : ℕ) ≠ 0) (by decide : Even 2092) hp

theorem nu_p_twoThousandNinetyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2094) p = if p = 2 ∨ p ∣ 2094 then 1 else 2 :=
  nu_p_evenPair (by decide : (2094 : ℕ) ≠ 0) (by decide : Even 2094) hp

theorem nu_p_twoThousandNinetySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2096) p = if p = 2 ∨ p ∣ 2096 then 1 else 2 :=
  nu_p_evenPair (by decide : (2096 : ℕ) ≠ 0) (by decide : Even 2096) hp

theorem nu_p_twoThousandNinetyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2098) p = if p = 2 ∨ p ∣ 2098 then 1 else 2 :=
  nu_p_evenPair (by decide : (2098 : ℕ) ≠ 0) (by decide : Even 2098) hp

theorem nu_p_twoThousandOneHundred (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2100) p = if p = 2 ∨ p ∣ 2100 then 1 else 2 :=
  nu_p_evenPair (by decide : (2100 : ℕ) ≠ 0) (by decide : Even 2100) hp

theorem nu_p_twoThousandNinetyTwo_two : nu_p (evenPair 2092) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2092)

theorem localFactor_twoThousandNinetyTwo_two : localFactor (evenPair 2092) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2092 : ℕ) ≠ 0) (by decide : Even 2092)

theorem nu_p_twoThousandOneHundred_two : nu_p (evenPair 2100) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2100)

theorem localFactor_twoThousandOneHundred_two : localFactor (evenPair 2100) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2100 : ℕ) ≠ 0) (by decide : Even 2100)

end Brockian.SingularSeries.Gaps20922100
