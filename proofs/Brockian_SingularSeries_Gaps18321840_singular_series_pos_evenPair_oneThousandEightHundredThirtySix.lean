/-
  Brockian/SingularSeriesGaps18321840.lean — even binary gaps n ∈ {1832, 1834, 1836, 1838, 1840}.

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

namespace Brockian.SingularSeries.Gaps18321840

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightHundredThirtyTwo : (evenPair 1832).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1832 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredThirtyFour : (evenPair 1834).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1834 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredThirtySix : (evenPair 1836).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1836 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredThirtyEight : (evenPair 1838).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1838 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredForty : (evenPair 1840).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1840 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightHundredThirtyTwo : IsAdmissible (evenPair 1832) :=
  isAdmissible_evenPair (by decide : Even 1832)

theorem isAdmissible_evenPair_oneThousandEightHundredThirtyFour : IsAdmissible (evenPair 1834) :=
  isAdmissible_evenPair (by decide : Even 1834)

theorem isAdmissible_evenPair_oneThousandEightHundredThirtySix : IsAdmissible (evenPair 1836) :=
  isAdmissible_evenPair (by decide : Even 1836)

theorem isAdmissible_evenPair_oneThousandEightHundredThirtyEight : IsAdmissible (evenPair 1838) :=
  isAdmissible_evenPair (by decide : Even 1838)

theorem isAdmissible_evenPair_oneThousandEightHundredForty : IsAdmissible (evenPair 1840) :=
  isAdmissible_evenPair (by decide : Even 1840)

theorem singular_series_pos_evenPair_oneThousandEightHundredThirtyTwo : 0 < singularSeries (evenPair 1832) :=
  singular_series_pos_evenPair (by decide : Even 1832)

theorem singular_series_pos_evenPair_oneThousandEightHundredThirtyFour : 0 < singularSeries (evenPair 1834) :=
  singular_series_pos_evenPair (by decide : Even 1834)

theorem singular_series_pos_evenPair_oneThousandEightHundredThirtySix : 0 < singularSeries (evenPair 1836) :=
  singular_series_pos_evenPair (by decide : Even 1836)

theorem singular_series_pos_evenPair_oneThousandEightHundredThirtyEight : 0 < singularSeries (evenPair 1838) :=
  singular_series_pos_evenPair (by decide : Even 1838)

theorem singular_series_pos_evenPair_oneThousandEightHundredForty : 0 < singularSeries (evenPair 1840) :=
  singular_series_pos_evenPair (by decide : Even 1840)

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1832) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1832) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1834) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1834) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1836) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1836) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1838) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1838) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1840) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1840) P

theorem nu_p_oneThousandEightHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1832) p = if p = 2 ∨ p ∣ 1832 then 1 else 2 :=
  nu_p_evenPair (by decide : (1832 : ℕ) ≠ 0) (by decide : Even 1832) hp

theorem nu_p_oneThousandEightHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1834) p = if p = 2 ∨ p ∣ 1834 then 1 else 2 :=
  nu_p_evenPair (by decide : (1834 : ℕ) ≠ 0) (by decide : Even 1834) hp

theorem nu_p_oneThousandEightHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1836) p = if p = 2 ∨ p ∣ 1836 then 1 else 2 :=
  nu_p_evenPair (by decide : (1836 : ℕ) ≠ 0) (by decide : Even 1836) hp

theorem nu_p_oneThousandEightHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1838) p = if p = 2 ∨ p ∣ 1838 then 1 else 2 :=
  nu_p_evenPair (by decide : (1838 : ℕ) ≠ 0) (by decide : Even 1838) hp

theorem nu_p_oneThousandEightHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1840) p = if p = 2 ∨ p ∣ 1840 then 1 else 2 :=
  nu_p_evenPair (by decide : (1840 : ℕ) ≠ 0) (by decide : Even 1840) hp

theorem nu_p_oneThousandEightHundredThirtyTwo_two : nu_p (evenPair 1832) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1832)

theorem localFactor_oneThousandEightHundredThirtyTwo_two : localFactor (evenPair 1832) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1832 : ℕ) ≠ 0) (by decide : Even 1832)

theorem nu_p_oneThousandEightHundredForty_two : nu_p (evenPair 1840) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1840)

theorem localFactor_oneThousandEightHundredForty_two : localFactor (evenPair 1840) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1840 : ℕ) ≠ 0) (by decide : Even 1840)

end Brockian.SingularSeries.Gaps18321840
