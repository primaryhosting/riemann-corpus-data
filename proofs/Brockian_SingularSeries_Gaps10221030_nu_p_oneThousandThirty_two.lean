/-
  Brockian/SingularSeriesGaps10221030.lean — even binary gaps n ∈ {1022, 1024, 1026, 1028, 1030}.

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

namespace Brockian.SingularSeries.Gaps10221030

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandTwentyTwo : (evenPair 1022).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1022 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwentyFour : (evenPair 1024).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1024 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwentySix : (evenPair 1026).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1026 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandTwentyEight : (evenPair 1028).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1028 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThirty : (evenPair 1030).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1030 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandTwentyTwo : IsAdmissible (evenPair 1022) :=
  isAdmissible_evenPair (by decide : Even 1022)

theorem isAdmissible_evenPair_oneThousandTwentyFour : IsAdmissible (evenPair 1024) :=
  isAdmissible_evenPair (by decide : Even 1024)

theorem isAdmissible_evenPair_oneThousandTwentySix : IsAdmissible (evenPair 1026) :=
  isAdmissible_evenPair (by decide : Even 1026)

theorem isAdmissible_evenPair_oneThousandTwentyEight : IsAdmissible (evenPair 1028) :=
  isAdmissible_evenPair (by decide : Even 1028)

theorem isAdmissible_evenPair_oneThousandThirty : IsAdmissible (evenPair 1030) :=
  isAdmissible_evenPair (by decide : Even 1030)

theorem singular_series_pos_evenPair_oneThousandTwentyTwo : 0 < singularSeries (evenPair 1022) :=
  singular_series_pos_evenPair (by decide : Even 1022)

theorem singular_series_pos_evenPair_oneThousandTwentyFour : 0 < singularSeries (evenPair 1024) :=
  singular_series_pos_evenPair (by decide : Even 1024)

theorem singular_series_pos_evenPair_oneThousandTwentySix : 0 < singularSeries (evenPair 1026) :=
  singular_series_pos_evenPair (by decide : Even 1026)

theorem singular_series_pos_evenPair_oneThousandTwentyEight : 0 < singularSeries (evenPair 1028) :=
  singular_series_pos_evenPair (by decide : Even 1028)

theorem singular_series_pos_evenPair_oneThousandThirty : 0 < singularSeries (evenPair 1030) :=
  singular_series_pos_evenPair (by decide : Even 1030)

theorem singular_series_finite_pos_evenPair_oneThousandTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1022) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1022) P

theorem singular_series_finite_pos_evenPair_oneThousandTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1024) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1024) P

theorem singular_series_finite_pos_evenPair_oneThousandTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1026) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1026) P

theorem singular_series_finite_pos_evenPair_oneThousandTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1028) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1028) P

theorem singular_series_finite_pos_evenPair_oneThousandThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1030) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1030) P

theorem nu_p_oneThousandTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1022) p = if p = 2 ∨ p ∣ 1022 then 1 else 2 :=
  nu_p_evenPair (by decide : (1022 : ℕ) ≠ 0) (by decide : Even 1022) hp

theorem nu_p_oneThousandTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1024) p = if p = 2 ∨ p ∣ 1024 then 1 else 2 :=
  nu_p_evenPair (by decide : (1024 : ℕ) ≠ 0) (by decide : Even 1024) hp

theorem nu_p_oneThousandTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1026) p = if p = 2 ∨ p ∣ 1026 then 1 else 2 :=
  nu_p_evenPair (by decide : (1026 : ℕ) ≠ 0) (by decide : Even 1026) hp

theorem nu_p_oneThousandTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1028) p = if p = 2 ∨ p ∣ 1028 then 1 else 2 :=
  nu_p_evenPair (by decide : (1028 : ℕ) ≠ 0) (by decide : Even 1028) hp

theorem nu_p_oneThousandThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1030) p = if p = 2 ∨ p ∣ 1030 then 1 else 2 :=
  nu_p_evenPair (by decide : (1030 : ℕ) ≠ 0) (by decide : Even 1030) hp

theorem nu_p_oneThousandTwentyTwo_two : nu_p (evenPair 1022) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1022)

theorem localFactor_oneThousandTwentyTwo_two : localFactor (evenPair 1022) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1022 : ℕ) ≠ 0) (by decide : Even 1022)

theorem nu_p_oneThousandThirty_two : nu_p (evenPair 1030) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1030)

theorem localFactor_oneThousandThirty_two : localFactor (evenPair 1030) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1030 : ℕ) ≠ 0) (by decide : Even 1030)

end Brockian.SingularSeries.Gaps10221030
