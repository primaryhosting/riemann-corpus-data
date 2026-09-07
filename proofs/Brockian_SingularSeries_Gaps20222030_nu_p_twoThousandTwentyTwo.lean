/-
  Brockian/SingularSeriesGaps20222030.lean — even binary gaps n ∈ {2022, 2024, 2026, 2028, 2030}.

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

namespace Brockian.SingularSeries.Gaps20222030

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandTwentyTwo : (evenPair 2022).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2022 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandTwentyFour : (evenPair 2024).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2024 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandTwentySix : (evenPair 2026).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2026 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandTwentyEight : (evenPair 2028).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2028 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandThirty : (evenPair 2030).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2030 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandTwentyTwo : IsAdmissible (evenPair 2022) :=
  isAdmissible_evenPair (by decide : Even 2022)

theorem isAdmissible_evenPair_twoThousandTwentyFour : IsAdmissible (evenPair 2024) :=
  isAdmissible_evenPair (by decide : Even 2024)

theorem isAdmissible_evenPair_twoThousandTwentySix : IsAdmissible (evenPair 2026) :=
  isAdmissible_evenPair (by decide : Even 2026)

theorem isAdmissible_evenPair_twoThousandTwentyEight : IsAdmissible (evenPair 2028) :=
  isAdmissible_evenPair (by decide : Even 2028)

theorem isAdmissible_evenPair_twoThousandThirty : IsAdmissible (evenPair 2030) :=
  isAdmissible_evenPair (by decide : Even 2030)

theorem singular_series_pos_evenPair_twoThousandTwentyTwo : 0 < singularSeries (evenPair 2022) :=
  singular_series_pos_evenPair (by decide : Even 2022)

theorem singular_series_pos_evenPair_twoThousandTwentyFour : 0 < singularSeries (evenPair 2024) :=
  singular_series_pos_evenPair (by decide : Even 2024)

theorem singular_series_pos_evenPair_twoThousandTwentySix : 0 < singularSeries (evenPair 2026) :=
  singular_series_pos_evenPair (by decide : Even 2026)

theorem singular_series_pos_evenPair_twoThousandTwentyEight : 0 < singularSeries (evenPair 2028) :=
  singular_series_pos_evenPair (by decide : Even 2028)

theorem singular_series_pos_evenPair_twoThousandThirty : 0 < singularSeries (evenPair 2030) :=
  singular_series_pos_evenPair (by decide : Even 2030)

theorem singular_series_finite_pos_evenPair_twoThousandTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2022) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2022) P

theorem singular_series_finite_pos_evenPair_twoThousandTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2024) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2024) P

theorem singular_series_finite_pos_evenPair_twoThousandTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2026) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2026) P

theorem singular_series_finite_pos_evenPair_twoThousandTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2028) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2028) P

theorem singular_series_finite_pos_evenPair_twoThousandThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2030) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2030) P

theorem nu_p_twoThousandTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2022) p = if p = 2 ∨ p ∣ 2022 then 1 else 2 :=
  nu_p_evenPair (by decide : (2022 : ℕ) ≠ 0) (by decide : Even 2022) hp

theorem nu_p_twoThousandTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2024) p = if p = 2 ∨ p ∣ 2024 then 1 else 2 :=
  nu_p_evenPair (by decide : (2024 : ℕ) ≠ 0) (by decide : Even 2024) hp

theorem nu_p_twoThousandTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2026) p = if p = 2 ∨ p ∣ 2026 then 1 else 2 :=
  nu_p_evenPair (by decide : (2026 : ℕ) ≠ 0) (by decide : Even 2026) hp

theorem nu_p_twoThousandTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2028) p = if p = 2 ∨ p ∣ 2028 then 1 else 2 :=
  nu_p_evenPair (by decide : (2028 : ℕ) ≠ 0) (by decide : Even 2028) hp

theorem nu_p_twoThousandThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2030) p = if p = 2 ∨ p ∣ 2030 then 1 else 2 :=
  nu_p_evenPair (by decide : (2030 : ℕ) ≠ 0) (by decide : Even 2030) hp

theorem nu_p_twoThousandTwentyTwo_two : nu_p (evenPair 2022) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2022)

theorem localFactor_twoThousandTwentyTwo_two : localFactor (evenPair 2022) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2022 : ℕ) ≠ 0) (by decide : Even 2022)

theorem nu_p_twoThousandThirty_two : nu_p (evenPair 2030) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2030)

theorem localFactor_twoThousandThirty_two : localFactor (evenPair 2030) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2030 : ℕ) ≠ 0) (by decide : Even 2030)

end Brockian.SingularSeries.Gaps20222030
