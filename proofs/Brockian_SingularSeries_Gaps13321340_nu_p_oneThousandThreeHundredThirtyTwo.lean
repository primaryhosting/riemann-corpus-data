/-
  Brockian/SingularSeriesGaps13321340.lean — even binary gaps n ∈ {1332, 1334, 1336, 1338, 1340}.

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

namespace Brockian.SingularSeries.Gaps13321340

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandThreeHundredThirtyTwo : (evenPair 1332).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1332 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredThirtyFour : (evenPair 1334).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1334 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredThirtySix : (evenPair 1336).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1336 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredThirtyEight : (evenPair 1338).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1338 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandThreeHundredForty : (evenPair 1340).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1340 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandThreeHundredThirtyTwo : IsAdmissible (evenPair 1332) :=
  isAdmissible_evenPair (by decide : Even 1332)

theorem isAdmissible_evenPair_oneThousandThreeHundredThirtyFour : IsAdmissible (evenPair 1334) :=
  isAdmissible_evenPair (by decide : Even 1334)

theorem isAdmissible_evenPair_oneThousandThreeHundredThirtySix : IsAdmissible (evenPair 1336) :=
  isAdmissible_evenPair (by decide : Even 1336)

theorem isAdmissible_evenPair_oneThousandThreeHundredThirtyEight : IsAdmissible (evenPair 1338) :=
  isAdmissible_evenPair (by decide : Even 1338)

theorem isAdmissible_evenPair_oneThousandThreeHundredForty : IsAdmissible (evenPair 1340) :=
  isAdmissible_evenPair (by decide : Even 1340)

theorem singular_series_pos_evenPair_oneThousandThreeHundredThirtyTwo : 0 < singularSeries (evenPair 1332) :=
  singular_series_pos_evenPair (by decide : Even 1332)

theorem singular_series_pos_evenPair_oneThousandThreeHundredThirtyFour : 0 < singularSeries (evenPair 1334) :=
  singular_series_pos_evenPair (by decide : Even 1334)

theorem singular_series_pos_evenPair_oneThousandThreeHundredThirtySix : 0 < singularSeries (evenPair 1336) :=
  singular_series_pos_evenPair (by decide : Even 1336)

theorem singular_series_pos_evenPair_oneThousandThreeHundredThirtyEight : 0 < singularSeries (evenPair 1338) :=
  singular_series_pos_evenPair (by decide : Even 1338)

theorem singular_series_pos_evenPair_oneThousandThreeHundredForty : 0 < singularSeries (evenPair 1340) :=
  singular_series_pos_evenPair (by decide : Even 1340)

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1332) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1332) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1334) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1334) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1336) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1336) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1338) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1338) P

theorem singular_series_finite_pos_evenPair_oneThousandThreeHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1340) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1340) P

theorem nu_p_oneThousandThreeHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1332) p = if p = 2 ∨ p ∣ 1332 then 1 else 2 :=
  nu_p_evenPair (by decide : (1332 : ℕ) ≠ 0) (by decide : Even 1332) hp

theorem nu_p_oneThousandThreeHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1334) p = if p = 2 ∨ p ∣ 1334 then 1 else 2 :=
  nu_p_evenPair (by decide : (1334 : ℕ) ≠ 0) (by decide : Even 1334) hp

theorem nu_p_oneThousandThreeHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1336) p = if p = 2 ∨ p ∣ 1336 then 1 else 2 :=
  nu_p_evenPair (by decide : (1336 : ℕ) ≠ 0) (by decide : Even 1336) hp

theorem nu_p_oneThousandThreeHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1338) p = if p = 2 ∨ p ∣ 1338 then 1 else 2 :=
  nu_p_evenPair (by decide : (1338 : ℕ) ≠ 0) (by decide : Even 1338) hp

theorem nu_p_oneThousandThreeHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1340) p = if p = 2 ∨ p ∣ 1340 then 1 else 2 :=
  nu_p_evenPair (by decide : (1340 : ℕ) ≠ 0) (by decide : Even 1340) hp

theorem nu_p_oneThousandThreeHundredThirtyTwo_two : nu_p (evenPair 1332) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1332)

theorem localFactor_oneThousandThreeHundredThirtyTwo_two : localFactor (evenPair 1332) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1332 : ℕ) ≠ 0) (by decide : Even 1332)

theorem nu_p_oneThousandThreeHundredForty_two : nu_p (evenPair 1340) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1340)

theorem localFactor_oneThousandThreeHundredForty_two : localFactor (evenPair 1340) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1340 : ℕ) ≠ 0) (by decide : Even 1340)

end Brockian.SingularSeries.Gaps13321340
