/-
  Brockian/SingularSeriesGaps15321540.lean — even binary gaps n ∈ {1532, 1534, 1536, 1538, 1540}.

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

namespace Brockian.SingularSeries.Gaps15321540

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFiveHundredThirtyTwo : (evenPair 1532).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1532 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredThirtyFour : (evenPair 1534).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1534 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredThirtySix : (evenPair 1536).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1536 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredThirtyEight : (evenPair 1538).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1538 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFiveHundredForty : (evenPair 1540).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1540 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFiveHundredThirtyTwo : IsAdmissible (evenPair 1532) :=
  isAdmissible_evenPair (by decide : Even 1532)

theorem isAdmissible_evenPair_oneThousandFiveHundredThirtyFour : IsAdmissible (evenPair 1534) :=
  isAdmissible_evenPair (by decide : Even 1534)

theorem isAdmissible_evenPair_oneThousandFiveHundredThirtySix : IsAdmissible (evenPair 1536) :=
  isAdmissible_evenPair (by decide : Even 1536)

theorem isAdmissible_evenPair_oneThousandFiveHundredThirtyEight : IsAdmissible (evenPair 1538) :=
  isAdmissible_evenPair (by decide : Even 1538)

theorem isAdmissible_evenPair_oneThousandFiveHundredForty : IsAdmissible (evenPair 1540) :=
  isAdmissible_evenPair (by decide : Even 1540)

theorem singular_series_pos_evenPair_oneThousandFiveHundredThirtyTwo : 0 < singularSeries (evenPair 1532) :=
  singular_series_pos_evenPair (by decide : Even 1532)

theorem singular_series_pos_evenPair_oneThousandFiveHundredThirtyFour : 0 < singularSeries (evenPair 1534) :=
  singular_series_pos_evenPair (by decide : Even 1534)

theorem singular_series_pos_evenPair_oneThousandFiveHundredThirtySix : 0 < singularSeries (evenPair 1536) :=
  singular_series_pos_evenPair (by decide : Even 1536)

theorem singular_series_pos_evenPair_oneThousandFiveHundredThirtyEight : 0 < singularSeries (evenPair 1538) :=
  singular_series_pos_evenPair (by decide : Even 1538)

theorem singular_series_pos_evenPair_oneThousandFiveHundredForty : 0 < singularSeries (evenPair 1540) :=
  singular_series_pos_evenPair (by decide : Even 1540)

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredThirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1532) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1532) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredThirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1534) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1534) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredThirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1536) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1536) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredThirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1538) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1538) P

theorem singular_series_finite_pos_evenPair_oneThousandFiveHundredForty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1540) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1540) P

theorem nu_p_oneThousandFiveHundredThirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1532) p = if p = 2 ∨ p ∣ 1532 then 1 else 2 :=
  nu_p_evenPair (by decide : (1532 : ℕ) ≠ 0) (by decide : Even 1532) hp

theorem nu_p_oneThousandFiveHundredThirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1534) p = if p = 2 ∨ p ∣ 1534 then 1 else 2 :=
  nu_p_evenPair (by decide : (1534 : ℕ) ≠ 0) (by decide : Even 1534) hp

theorem nu_p_oneThousandFiveHundredThirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1536) p = if p = 2 ∨ p ∣ 1536 then 1 else 2 :=
  nu_p_evenPair (by decide : (1536 : ℕ) ≠ 0) (by decide : Even 1536) hp

theorem nu_p_oneThousandFiveHundredThirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1538) p = if p = 2 ∨ p ∣ 1538 then 1 else 2 :=
  nu_p_evenPair (by decide : (1538 : ℕ) ≠ 0) (by decide : Even 1538) hp

theorem nu_p_oneThousandFiveHundredForty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1540) p = if p = 2 ∨ p ∣ 1540 then 1 else 2 :=
  nu_p_evenPair (by decide : (1540 : ℕ) ≠ 0) (by decide : Even 1540) hp

theorem nu_p_oneThousandFiveHundredThirtyTwo_two : nu_p (evenPair 1532) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1532)

theorem localFactor_oneThousandFiveHundredThirtyTwo_two : localFactor (evenPair 1532) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1532 : ℕ) ≠ 0) (by decide : Even 1532)

theorem nu_p_oneThousandFiveHundredForty_two : nu_p (evenPair 1540) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1540)

theorem localFactor_oneThousandFiveHundredForty_two : localFactor (evenPair 1540) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1540 : ℕ) ≠ 0) (by decide : Even 1540)

end Brockian.SingularSeries.Gaps15321540
