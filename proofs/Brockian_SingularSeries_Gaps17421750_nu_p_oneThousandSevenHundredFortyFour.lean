/-
  Brockian/SingularSeriesGaps17421750.lean — even binary gaps n ∈ {1742, 1744, 1746, 1748, 1750}.

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

namespace Brockian.SingularSeries.Gaps17421750

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSevenHundredFortyTwo : (evenPair 1742).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1742 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredFortyFour : (evenPair 1744).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1744 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredFortySix : (evenPair 1746).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1746 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredFortyEight : (evenPair 1748).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1748 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredFifty : (evenPair 1750).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1750 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSevenHundredFortyTwo : IsAdmissible (evenPair 1742) :=
  isAdmissible_evenPair (by decide : Even 1742)

theorem isAdmissible_evenPair_oneThousandSevenHundredFortyFour : IsAdmissible (evenPair 1744) :=
  isAdmissible_evenPair (by decide : Even 1744)

theorem isAdmissible_evenPair_oneThousandSevenHundredFortySix : IsAdmissible (evenPair 1746) :=
  isAdmissible_evenPair (by decide : Even 1746)

theorem isAdmissible_evenPair_oneThousandSevenHundredFortyEight : IsAdmissible (evenPair 1748) :=
  isAdmissible_evenPair (by decide : Even 1748)

theorem isAdmissible_evenPair_oneThousandSevenHundredFifty : IsAdmissible (evenPair 1750) :=
  isAdmissible_evenPair (by decide : Even 1750)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFortyTwo : 0 < singularSeries (evenPair 1742) :=
  singular_series_pos_evenPair (by decide : Even 1742)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFortyFour : 0 < singularSeries (evenPair 1744) :=
  singular_series_pos_evenPair (by decide : Even 1744)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFortySix : 0 < singularSeries (evenPair 1746) :=
  singular_series_pos_evenPair (by decide : Even 1746)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFortyEight : 0 < singularSeries (evenPair 1748) :=
  singular_series_pos_evenPair (by decide : Even 1748)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFifty : 0 < singularSeries (evenPair 1750) :=
  singular_series_pos_evenPair (by decide : Even 1750)

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1742) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1742) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1744) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1744) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1746) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1746) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1748) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1748) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1750) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1750) P

theorem nu_p_oneThousandSevenHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1742) p = if p = 2 ∨ p ∣ 1742 then 1 else 2 :=
  nu_p_evenPair (by decide : (1742 : ℕ) ≠ 0) (by decide : Even 1742) hp

theorem nu_p_oneThousandSevenHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1744) p = if p = 2 ∨ p ∣ 1744 then 1 else 2 :=
  nu_p_evenPair (by decide : (1744 : ℕ) ≠ 0) (by decide : Even 1744) hp

theorem nu_p_oneThousandSevenHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1746) p = if p = 2 ∨ p ∣ 1746 then 1 else 2 :=
  nu_p_evenPair (by decide : (1746 : ℕ) ≠ 0) (by decide : Even 1746) hp

theorem nu_p_oneThousandSevenHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1748) p = if p = 2 ∨ p ∣ 1748 then 1 else 2 :=
  nu_p_evenPair (by decide : (1748 : ℕ) ≠ 0) (by decide : Even 1748) hp

theorem nu_p_oneThousandSevenHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1750) p = if p = 2 ∨ p ∣ 1750 then 1 else 2 :=
  nu_p_evenPair (by decide : (1750 : ℕ) ≠ 0) (by decide : Even 1750) hp

theorem nu_p_oneThousandSevenHundredFortyTwo_two : nu_p (evenPair 1742) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1742)

theorem localFactor_oneThousandSevenHundredFortyTwo_two : localFactor (evenPair 1742) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1742 : ℕ) ≠ 0) (by decide : Even 1742)

theorem nu_p_oneThousandSevenHundredFifty_two : nu_p (evenPair 1750) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1750)

theorem localFactor_oneThousandSevenHundredFifty_two : localFactor (evenPair 1750) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1750 : ℕ) ≠ 0) (by decide : Even 1750)

end Brockian.SingularSeries.Gaps17421750
