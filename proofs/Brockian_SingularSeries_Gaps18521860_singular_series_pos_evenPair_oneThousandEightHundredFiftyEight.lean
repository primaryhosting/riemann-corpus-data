/-
  Brockian/SingularSeriesGaps18521860.lean — even binary gaps n ∈ {1852, 1854, 1856, 1858, 1860}.

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

namespace Brockian.SingularSeries.Gaps18521860

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandEightHundredFiftyTwo : (evenPair 1852).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1852 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredFiftyFour : (evenPair 1854).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1854 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredFiftySix : (evenPair 1856).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1856 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredFiftyEight : (evenPair 1858).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1858 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandEightHundredSixty : (evenPair 1860).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1860 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandEightHundredFiftyTwo : IsAdmissible (evenPair 1852) :=
  isAdmissible_evenPair (by decide : Even 1852)

theorem isAdmissible_evenPair_oneThousandEightHundredFiftyFour : IsAdmissible (evenPair 1854) :=
  isAdmissible_evenPair (by decide : Even 1854)

theorem isAdmissible_evenPair_oneThousandEightHundredFiftySix : IsAdmissible (evenPair 1856) :=
  isAdmissible_evenPair (by decide : Even 1856)

theorem isAdmissible_evenPair_oneThousandEightHundredFiftyEight : IsAdmissible (evenPair 1858) :=
  isAdmissible_evenPair (by decide : Even 1858)

theorem isAdmissible_evenPair_oneThousandEightHundredSixty : IsAdmissible (evenPair 1860) :=
  isAdmissible_evenPair (by decide : Even 1860)

theorem singular_series_pos_evenPair_oneThousandEightHundredFiftyTwo : 0 < singularSeries (evenPair 1852) :=
  singular_series_pos_evenPair (by decide : Even 1852)

theorem singular_series_pos_evenPair_oneThousandEightHundredFiftyFour : 0 < singularSeries (evenPair 1854) :=
  singular_series_pos_evenPair (by decide : Even 1854)

theorem singular_series_pos_evenPair_oneThousandEightHundredFiftySix : 0 < singularSeries (evenPair 1856) :=
  singular_series_pos_evenPair (by decide : Even 1856)

theorem singular_series_pos_evenPair_oneThousandEightHundredFiftyEight : 0 < singularSeries (evenPair 1858) :=
  singular_series_pos_evenPair (by decide : Even 1858)

theorem singular_series_pos_evenPair_oneThousandEightHundredSixty : 0 < singularSeries (evenPair 1860) :=
  singular_series_pos_evenPair (by decide : Even 1860)

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1852) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1852) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1854) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1854) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1856) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1856) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1858) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1858) P

theorem singular_series_finite_pos_evenPair_oneThousandEightHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1860) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1860) P

theorem nu_p_oneThousandEightHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1852) p = if p = 2 ∨ p ∣ 1852 then 1 else 2 :=
  nu_p_evenPair (by decide : (1852 : ℕ) ≠ 0) (by decide : Even 1852) hp

theorem nu_p_oneThousandEightHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1854) p = if p = 2 ∨ p ∣ 1854 then 1 else 2 :=
  nu_p_evenPair (by decide : (1854 : ℕ) ≠ 0) (by decide : Even 1854) hp

theorem nu_p_oneThousandEightHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1856) p = if p = 2 ∨ p ∣ 1856 then 1 else 2 :=
  nu_p_evenPair (by decide : (1856 : ℕ) ≠ 0) (by decide : Even 1856) hp

theorem nu_p_oneThousandEightHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1858) p = if p = 2 ∨ p ∣ 1858 then 1 else 2 :=
  nu_p_evenPair (by decide : (1858 : ℕ) ≠ 0) (by decide : Even 1858) hp

theorem nu_p_oneThousandEightHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1860) p = if p = 2 ∨ p ∣ 1860 then 1 else 2 :=
  nu_p_evenPair (by decide : (1860 : ℕ) ≠ 0) (by decide : Even 1860) hp

theorem nu_p_oneThousandEightHundredFiftyTwo_two : nu_p (evenPair 1852) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1852)

theorem localFactor_oneThousandEightHundredFiftyTwo_two : localFactor (evenPair 1852) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1852 : ℕ) ≠ 0) (by decide : Even 1852)

theorem nu_p_oneThousandEightHundredSixty_two : nu_p (evenPair 1860) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1860)

theorem localFactor_oneThousandEightHundredSixty_two : localFactor (evenPair 1860) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1860 : ℕ) ≠ 0) (by decide : Even 1860)

end Brockian.SingularSeries.Gaps18521860
