/-
  Brockian/SingularSeriesGaps14521460.lean — even binary gaps n ∈ {1452, 1454, 1456, 1458, 1460}.

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

namespace Brockian.SingularSeries.Gaps14521460

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFourHundredFiftyTwo : (evenPair 1452).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1452 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredFiftyFour : (evenPair 1454).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1454 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredFiftySix : (evenPair 1456).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1456 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredFiftyEight : (evenPair 1458).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1458 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredSixty : (evenPair 1460).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1460 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFourHundredFiftyTwo : IsAdmissible (evenPair 1452) :=
  isAdmissible_evenPair (by decide : Even 1452)

theorem isAdmissible_evenPair_oneThousandFourHundredFiftyFour : IsAdmissible (evenPair 1454) :=
  isAdmissible_evenPair (by decide : Even 1454)

theorem isAdmissible_evenPair_oneThousandFourHundredFiftySix : IsAdmissible (evenPair 1456) :=
  isAdmissible_evenPair (by decide : Even 1456)

theorem isAdmissible_evenPair_oneThousandFourHundredFiftyEight : IsAdmissible (evenPair 1458) :=
  isAdmissible_evenPair (by decide : Even 1458)

theorem isAdmissible_evenPair_oneThousandFourHundredSixty : IsAdmissible (evenPair 1460) :=
  isAdmissible_evenPair (by decide : Even 1460)

theorem singular_series_pos_evenPair_oneThousandFourHundredFiftyTwo : 0 < singularSeries (evenPair 1452) :=
  singular_series_pos_evenPair (by decide : Even 1452)

theorem singular_series_pos_evenPair_oneThousandFourHundredFiftyFour : 0 < singularSeries (evenPair 1454) :=
  singular_series_pos_evenPair (by decide : Even 1454)

theorem singular_series_pos_evenPair_oneThousandFourHundredFiftySix : 0 < singularSeries (evenPair 1456) :=
  singular_series_pos_evenPair (by decide : Even 1456)

theorem singular_series_pos_evenPair_oneThousandFourHundredFiftyEight : 0 < singularSeries (evenPair 1458) :=
  singular_series_pos_evenPair (by decide : Even 1458)

theorem singular_series_pos_evenPair_oneThousandFourHundredSixty : 0 < singularSeries (evenPair 1460) :=
  singular_series_pos_evenPair (by decide : Even 1460)

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1452) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1452) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1454) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1454) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1456) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1456) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1458) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1458) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1460) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1460) P

theorem nu_p_oneThousandFourHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1452) p = if p = 2 ∨ p ∣ 1452 then 1 else 2 :=
  nu_p_evenPair (by decide : (1452 : ℕ) ≠ 0) (by decide : Even 1452) hp

theorem nu_p_oneThousandFourHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1454) p = if p = 2 ∨ p ∣ 1454 then 1 else 2 :=
  nu_p_evenPair (by decide : (1454 : ℕ) ≠ 0) (by decide : Even 1454) hp

theorem nu_p_oneThousandFourHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1456) p = if p = 2 ∨ p ∣ 1456 then 1 else 2 :=
  nu_p_evenPair (by decide : (1456 : ℕ) ≠ 0) (by decide : Even 1456) hp

theorem nu_p_oneThousandFourHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1458) p = if p = 2 ∨ p ∣ 1458 then 1 else 2 :=
  nu_p_evenPair (by decide : (1458 : ℕ) ≠ 0) (by decide : Even 1458) hp

theorem nu_p_oneThousandFourHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1460) p = if p = 2 ∨ p ∣ 1460 then 1 else 2 :=
  nu_p_evenPair (by decide : (1460 : ℕ) ≠ 0) (by decide : Even 1460) hp

theorem nu_p_oneThousandFourHundredFiftyTwo_two : nu_p (evenPair 1452) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1452)

theorem localFactor_oneThousandFourHundredFiftyTwo_two : localFactor (evenPair 1452) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1452 : ℕ) ≠ 0) (by decide : Even 1452)

theorem nu_p_oneThousandFourHundredSixty_two : nu_p (evenPair 1460) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1460)

theorem localFactor_oneThousandFourHundredSixty_two : localFactor (evenPair 1460) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1460 : ℕ) ≠ 0) (by decide : Even 1460)

end Brockian.SingularSeries.Gaps14521460
