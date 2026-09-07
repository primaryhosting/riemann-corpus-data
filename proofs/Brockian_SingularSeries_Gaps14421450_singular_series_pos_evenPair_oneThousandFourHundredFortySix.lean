/-
  Brockian/SingularSeriesGaps14421450.lean — even binary gaps n ∈ {1442, 1444, 1446, 1448, 1450}.

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

namespace Brockian.SingularSeries.Gaps14421450

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandFourHundredFortyTwo : (evenPair 1442).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1442 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredFortyFour : (evenPair 1444).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1444 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredFortySix : (evenPair 1446).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1446 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredFortyEight : (evenPair 1448).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1448 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandFourHundredFifty : (evenPair 1450).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1450 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandFourHundredFortyTwo : IsAdmissible (evenPair 1442) :=
  isAdmissible_evenPair (by decide : Even 1442)

theorem isAdmissible_evenPair_oneThousandFourHundredFortyFour : IsAdmissible (evenPair 1444) :=
  isAdmissible_evenPair (by decide : Even 1444)

theorem isAdmissible_evenPair_oneThousandFourHundredFortySix : IsAdmissible (evenPair 1446) :=
  isAdmissible_evenPair (by decide : Even 1446)

theorem isAdmissible_evenPair_oneThousandFourHundredFortyEight : IsAdmissible (evenPair 1448) :=
  isAdmissible_evenPair (by decide : Even 1448)

theorem isAdmissible_evenPair_oneThousandFourHundredFifty : IsAdmissible (evenPair 1450) :=
  isAdmissible_evenPair (by decide : Even 1450)

theorem singular_series_pos_evenPair_oneThousandFourHundredFortyTwo : 0 < singularSeries (evenPair 1442) :=
  singular_series_pos_evenPair (by decide : Even 1442)

theorem singular_series_pos_evenPair_oneThousandFourHundredFortyFour : 0 < singularSeries (evenPair 1444) :=
  singular_series_pos_evenPair (by decide : Even 1444)

theorem singular_series_pos_evenPair_oneThousandFourHundredFortySix : 0 < singularSeries (evenPair 1446) :=
  singular_series_pos_evenPair (by decide : Even 1446)

theorem singular_series_pos_evenPair_oneThousandFourHundredFortyEight : 0 < singularSeries (evenPair 1448) :=
  singular_series_pos_evenPair (by decide : Even 1448)

theorem singular_series_pos_evenPair_oneThousandFourHundredFifty : 0 < singularSeries (evenPair 1450) :=
  singular_series_pos_evenPair (by decide : Even 1450)

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1442) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1442) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1444) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1444) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1446) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1446) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1448) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1448) P

theorem singular_series_finite_pos_evenPair_oneThousandFourHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1450) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1450) P

theorem nu_p_oneThousandFourHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1442) p = if p = 2 ∨ p ∣ 1442 then 1 else 2 :=
  nu_p_evenPair (by decide : (1442 : ℕ) ≠ 0) (by decide : Even 1442) hp

theorem nu_p_oneThousandFourHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1444) p = if p = 2 ∨ p ∣ 1444 then 1 else 2 :=
  nu_p_evenPair (by decide : (1444 : ℕ) ≠ 0) (by decide : Even 1444) hp

theorem nu_p_oneThousandFourHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1446) p = if p = 2 ∨ p ∣ 1446 then 1 else 2 :=
  nu_p_evenPair (by decide : (1446 : ℕ) ≠ 0) (by decide : Even 1446) hp

theorem nu_p_oneThousandFourHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1448) p = if p = 2 ∨ p ∣ 1448 then 1 else 2 :=
  nu_p_evenPair (by decide : (1448 : ℕ) ≠ 0) (by decide : Even 1448) hp

theorem nu_p_oneThousandFourHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1450) p = if p = 2 ∨ p ∣ 1450 then 1 else 2 :=
  nu_p_evenPair (by decide : (1450 : ℕ) ≠ 0) (by decide : Even 1450) hp

theorem nu_p_oneThousandFourHundredFortyTwo_two : nu_p (evenPair 1442) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1442)

theorem localFactor_oneThousandFourHundredFortyTwo_two : localFactor (evenPair 1442) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1442 : ℕ) ≠ 0) (by decide : Even 1442)

theorem nu_p_oneThousandFourHundredFifty_two : nu_p (evenPair 1450) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1450)

theorem localFactor_oneThousandFourHundredFifty_two : localFactor (evenPair 1450) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1450 : ℕ) ≠ 0) (by decide : Even 1450)

end Brockian.SingularSeries.Gaps14421450
