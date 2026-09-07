/-
  Brockian/SingularSeriesGaps16421650.lean — even binary gaps n ∈ {1642, 1644, 1646, 1648, 1650}.

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

namespace Brockian.SingularSeries.Gaps16421650

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSixHundredFortyTwo : (evenPair 1642).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1642 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredFortyFour : (evenPair 1644).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1644 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredFortySix : (evenPair 1646).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1646 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredFortyEight : (evenPair 1648).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1648 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSixHundredFifty : (evenPair 1650).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1650 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSixHundredFortyTwo : IsAdmissible (evenPair 1642) :=
  isAdmissible_evenPair (by decide : Even 1642)

theorem isAdmissible_evenPair_oneThousandSixHundredFortyFour : IsAdmissible (evenPair 1644) :=
  isAdmissible_evenPair (by decide : Even 1644)

theorem isAdmissible_evenPair_oneThousandSixHundredFortySix : IsAdmissible (evenPair 1646) :=
  isAdmissible_evenPair (by decide : Even 1646)

theorem isAdmissible_evenPair_oneThousandSixHundredFortyEight : IsAdmissible (evenPair 1648) :=
  isAdmissible_evenPair (by decide : Even 1648)

theorem isAdmissible_evenPair_oneThousandSixHundredFifty : IsAdmissible (evenPair 1650) :=
  isAdmissible_evenPair (by decide : Even 1650)

theorem singular_series_pos_evenPair_oneThousandSixHundredFortyTwo : 0 < singularSeries (evenPair 1642) :=
  singular_series_pos_evenPair (by decide : Even 1642)

theorem singular_series_pos_evenPair_oneThousandSixHundredFortyFour : 0 < singularSeries (evenPair 1644) :=
  singular_series_pos_evenPair (by decide : Even 1644)

theorem singular_series_pos_evenPair_oneThousandSixHundredFortySix : 0 < singularSeries (evenPair 1646) :=
  singular_series_pos_evenPair (by decide : Even 1646)

theorem singular_series_pos_evenPair_oneThousandSixHundredFortyEight : 0 < singularSeries (evenPair 1648) :=
  singular_series_pos_evenPair (by decide : Even 1648)

theorem singular_series_pos_evenPair_oneThousandSixHundredFifty : 0 < singularSeries (evenPair 1650) :=
  singular_series_pos_evenPair (by decide : Even 1650)

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1642) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1642) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1644) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1644) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1646) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1646) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1648) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1648) P

theorem singular_series_finite_pos_evenPair_oneThousandSixHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1650) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1650) P

theorem nu_p_oneThousandSixHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1642) p = if p = 2 ∨ p ∣ 1642 then 1 else 2 :=
  nu_p_evenPair (by decide : (1642 : ℕ) ≠ 0) (by decide : Even 1642) hp

theorem nu_p_oneThousandSixHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1644) p = if p = 2 ∨ p ∣ 1644 then 1 else 2 :=
  nu_p_evenPair (by decide : (1644 : ℕ) ≠ 0) (by decide : Even 1644) hp

theorem nu_p_oneThousandSixHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1646) p = if p = 2 ∨ p ∣ 1646 then 1 else 2 :=
  nu_p_evenPair (by decide : (1646 : ℕ) ≠ 0) (by decide : Even 1646) hp

theorem nu_p_oneThousandSixHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1648) p = if p = 2 ∨ p ∣ 1648 then 1 else 2 :=
  nu_p_evenPair (by decide : (1648 : ℕ) ≠ 0) (by decide : Even 1648) hp

theorem nu_p_oneThousandSixHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1650) p = if p = 2 ∨ p ∣ 1650 then 1 else 2 :=
  nu_p_evenPair (by decide : (1650 : ℕ) ≠ 0) (by decide : Even 1650) hp

theorem nu_p_oneThousandSixHundredFortyTwo_two : nu_p (evenPair 1642) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1642)

theorem localFactor_oneThousandSixHundredFortyTwo_two : localFactor (evenPair 1642) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1642 : ℕ) ≠ 0) (by decide : Even 1642)

theorem nu_p_oneThousandSixHundredFifty_two : nu_p (evenPair 1650) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1650)

theorem localFactor_oneThousandSixHundredFifty_two : localFactor (evenPair 1650) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1650 : ℕ) ≠ 0) (by decide : Even 1650)

end Brockian.SingularSeries.Gaps16421650
