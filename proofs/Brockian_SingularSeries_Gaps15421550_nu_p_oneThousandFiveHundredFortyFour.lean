/-
  Brockian/SingularSeriesGaps15421550.lean — even binary gaps n ∈ {1542, 1544, 1546, 1548, 1550}.

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

namespace Brockian.SingularSeries.Gaps15421550

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiveHundredFortyTwo : (evenPair 1542).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1542 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredFortyFour : (evenPair 1544).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1544 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredFortySix : (evenPair 1546).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1546 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredFortyEight : (evenPair 1548).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1548 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredFifty : (evenPair 1550).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1550 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiveHundredFortyTwo : IsAdmissible (evenPair 1542) :=
  isAdmissible_evenPair (by decide : Even 1542)

theorem isAdmissible_evenPair_oneThousandFiveHundredFortyFour : IsAdmissible (evenPair 1544) :=
  isAdmissible_evenPair (by decide : Even 1544)

theorem isAdmissible_evenPair_oneThousandFiveHundredFortySix : IsAdmissible (evenPair 1546) :=
  isAdmissible_evenPair (by decide : Even 1546)

theorem isAdmissible_evenPair_oneThousandFiveHundredFortyEight : IsAdmissible (evenPair 1548) :=
  isAdmissible_evenPair (by decide : Even 1548)

theorem isAdmissible_evenPair_oneThousandFiveHundredFifty : IsAdmissible (evenPair 1550) :=
  isAdmissible_evenPair (by decide : Even 1550)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFortyTwo : 0 < singularSeries (evenPair 1542) :=
  singular_series_pos_evenPair (by decide : Even 1542)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFortyFour : 0 < singularSeries (evenPair 1544) :=
  singular_series_pos_evenPair (by decide : Even 1544)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFortySix : 0 < singularSeries (evenPair 1546) :=
  singular_series_pos_evenPair (by decide : Even 1546)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFortyEight : 0 < singularSeries (evenPair 1548) :=
  singular_series_pos_evenPair (by decide : Even 1548)

theorem singular_series_pos_evenPair_oneThousandFiveHundredFifty : 0 < singularSeries (evenPair 1550) :=
  singular_series_pos_evenPair (by decide : Even 1550)

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1542) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1542) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1544) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1544) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1546) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1546) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1548) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1548) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1550) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1550) P

theorem nu_p_oneThousandFiveHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1542) p = if p = 2 ∨ p ∣ 1542 then 1 else 2 :=
  nu_p_evenPair (by decide : (1542 : ℕ) ≠ 0) (by decide : Even 1542) hp

theorem nu_p_oneThousandFiveHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1544) p = if p = 2 ∨ p ∣ 1544 then 1 else 2 :=
  nu_p_evenPair (by decide : (1544 : ℕ) ≠ 0) (by decide : Even 1544) hp

theorem nu_p_oneThousandFiveHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1546) p = if p = 2 ∨ p ∣ 1546 then 1 else 2 :=
  nu_p_evenPair (by decide : (1546 : ℕ) ≠ 0) (by decide : Even 1546) hp

theorem nu_p_oneThousandFiveHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1548) p = if p = 2 ∨ p ∣ 1548 then 1 else 2 :=
  nu_p_evenPair (by decide : (1548 : ℕ) ≠ 0) (by decide : Even 1548) hp

theorem nu_p_oneThousandFiveHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1550) p = if p = 2 ∨ p ∣ 1550 then 1 else 2 :=
  nu_p_evenPair (by decide : (1550 : ℕ) ≠ 0) (by decide : Even 1550) hp

theorem nu_p_oneThousandFiveHundredFortyTwo_two : nu_p (evenPair 1542) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1542)

theorem localFactor_oneThousandFiveHundredFortyTwo_two : localFactor (evenPair 1542) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1542 : ℕ) ≠ 0) (by decide : Even 1542)

theorem nu_p_oneThousandFiveHundredFifty_two : nu_p (evenPair 1550) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1550)

theorem localFactor_oneThousandFiveHundredFifty_two : localFactor (evenPair 1550) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1550 : ℕ) ≠ 0) (by decide : Even 1550)

end Brockian.SingularSeries.Gaps15421550
