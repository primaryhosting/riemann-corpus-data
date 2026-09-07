/-
  Brockian/SingularSeriesGaps18221830.lean — even binary gaps n ∈ {1822, 1824, 1826, 1828, 1830}.

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

namespace Brockian.SingularSeries.Gaps18221830

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightHundredTwentyTwo : (evenPair 1822).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1822 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredTwentyFour : (evenPair 1824).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1824 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredTwentySix : (evenPair 1826).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1826 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredTwentyEight : (evenPair 1828).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1828 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredThirty : (evenPair 1830).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1830 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightHundredTwentyTwo : IsAdmissible (evenPair 1822) :=
  isAdmissible_evenPair (by decide : Even 1822)

theorem isAdmissible_evenPair_oneThousandEightHundredTwentyFour : IsAdmissible (evenPair 1824) :=
  isAdmissible_evenPair (by decide : Even 1824)

theorem isAdmissible_evenPair_oneThousandEightHundredTwentySix : IsAdmissible (evenPair 1826) :=
  isAdmissible_evenPair (by decide : Even 1826)

theorem isAdmissible_evenPair_oneThousandEightHundredTwentyEight : IsAdmissible (evenPair 1828) :=
  isAdmissible_evenPair (by decide : Even 1828)

theorem isAdmissible_evenPair_oneThousandEightHundredThirty : IsAdmissible (evenPair 1830) :=
  isAdmissible_evenPair (by decide : Even 1830)

theorem singular_series_pos_evenPair_oneThousandEightHundredTwentyTwo : 0 < singularSeries (evenPair 1822) :=
  singular_series_pos_evenPair (by decide : Even 1822)

theorem singular_series_pos_evenPair_oneThousandEightHundredTwentyFour : 0 < singularSeries (evenPair 1824) :=
  singular_series_pos_evenPair (by decide : Even 1824)

theorem singular_series_pos_evenPair_oneThousandEightHundredTwentySix : 0 < singularSeries (evenPair 1826) :=
  singular_series_pos_evenPair (by decide : Even 1826)

theorem singular_series_pos_evenPair_oneThousandEightHundredTwentyEight : 0 < singularSeries (evenPair 1828) :=
  singular_series_pos_evenPair (by decide : Even 1828)

theorem singular_series_pos_evenPair_oneThousandEightHundredThirty : 0 < singularSeries (evenPair 1830) :=
  singular_series_pos_evenPair (by decide : Even 1830)

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1822) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1822) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1824) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1824) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1826) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1826) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1828) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1828) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1830) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1830) P

theorem nu_p_oneThousandEightHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1822) p = if p = 2 ∨ p ∣ 1822 then 1 else 2 :=
  nu_p_evenPair (by decide : (1822 : ℕ) ≠ 0) (by decide : Even 1822) hp

theorem nu_p_oneThousandEightHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1824) p = if p = 2 ∨ p ∣ 1824 then 1 else 2 :=
  nu_p_evenPair (by decide : (1824 : ℕ) ≠ 0) (by decide : Even 1824) hp

theorem nu_p_oneThousandEightHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1826) p = if p = 2 ∨ p ∣ 1826 then 1 else 2 :=
  nu_p_evenPair (by decide : (1826 : ℕ) ≠ 0) (by decide : Even 1826) hp

theorem nu_p_oneThousandEightHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1828) p = if p = 2 ∨ p ∣ 1828 then 1 else 2 :=
  nu_p_evenPair (by decide : (1828 : ℕ) ≠ 0) (by decide : Even 1828) hp

theorem nu_p_oneThousandEightHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1830) p = if p = 2 ∨ p ∣ 1830 then 1 else 2 :=
  nu_p_evenPair (by decide : (1830 : ℕ) ≠ 0) (by decide : Even 1830) hp

theorem nu_p_oneThousandEightHundredTwentyTwo_two : nu_p (evenPair 1822) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1822)

theorem localFactor_oneThousandEightHundredTwentyTwo_two : localFactor (evenPair 1822) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1822 : ℕ) ≠ 0) (by decide : Even 1822)

theorem nu_p_oneThousandEightHundredThirty_two : nu_p (evenPair 1830) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1830)

theorem localFactor_oneThousandEightHundredThirty_two : localFactor (evenPair 1830) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1830 : ℕ) ≠ 0) (by decide : Even 1830)

end Brockian.SingularSeries.Gaps18221830
