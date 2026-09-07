/-
  Brockian/SingularSeriesGaps17221730.lean — even binary gaps n ∈ {1722, 1724, 1726, 1728, 1730}.

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

namespace Brockian.SingularSeries.Gaps17221730

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSevenHundredTwentyTwo : (evenPair 1722).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1722 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredTwentyFour : (evenPair 1724).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1724 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredTwentySix : (evenPair 1726).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1726 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredTwentyEight : (evenPair 1728).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1728 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredThirty : (evenPair 1730).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1730 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSevenHundredTwentyTwo : IsAdmissible (evenPair 1722) :=
  isAdmissible_evenPair (by decide : Even 1722)

theorem isAdmissible_evenPair_oneThousandSevenHundredTwentyFour : IsAdmissible (evenPair 1724) :=
  isAdmissible_evenPair (by decide : Even 1724)

theorem isAdmissible_evenPair_oneThousandSevenHundredTwentySix : IsAdmissible (evenPair 1726) :=
  isAdmissible_evenPair (by decide : Even 1726)

theorem isAdmissible_evenPair_oneThousandSevenHundredTwentyEight : IsAdmissible (evenPair 1728) :=
  isAdmissible_evenPair (by decide : Even 1728)

theorem isAdmissible_evenPair_oneThousandSevenHundredThirty : IsAdmissible (evenPair 1730) :=
  isAdmissible_evenPair (by decide : Even 1730)

theorem singular_series_pos_evenPair_oneThousandSevenHundredTwentyTwo : 0 < singularSeries (evenPair 1722) :=
  singular_series_pos_evenPair (by decide : Even 1722)

theorem singular_series_pos_evenPair_oneThousandSevenHundredTwentyFour : 0 < singularSeries (evenPair 1724) :=
  singular_series_pos_evenPair (by decide : Even 1724)

theorem singular_series_pos_evenPair_oneThousandSevenHundredTwentySix : 0 < singularSeries (evenPair 1726) :=
  singular_series_pos_evenPair (by decide : Even 1726)

theorem singular_series_pos_evenPair_oneThousandSevenHundredTwentyEight : 0 < singularSeries (evenPair 1728) :=
  singular_series_pos_evenPair (by decide : Even 1728)

theorem singular_series_pos_evenPair_oneThousandSevenHundredThirty : 0 < singularSeries (evenPair 1730) :=
  singular_series_pos_evenPair (by decide : Even 1730)

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredTwentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1722) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1722) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredTwentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1724) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1724) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredTwentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1726) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1726) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredTwentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1728) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1728) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredThirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1730) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1730) P

theorem nu_p_oneThousandSevenHundredTwentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1722) p = if p = 2 ∨ p ∣ 1722 then 1 else 2 :=
  nu_p_evenPair (by decide : (1722 : ℕ) ≠ 0) (by decide : Even 1722) hp

theorem nu_p_oneThousandSevenHundredTwentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1724) p = if p = 2 ∨ p ∣ 1724 then 1 else 2 :=
  nu_p_evenPair (by decide : (1724 : ℕ) ≠ 0) (by decide : Even 1724) hp

theorem nu_p_oneThousandSevenHundredTwentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1726) p = if p = 2 ∨ p ∣ 1726 then 1 else 2 :=
  nu_p_evenPair (by decide : (1726 : ℕ) ≠ 0) (by decide : Even 1726) hp

theorem nu_p_oneThousandSevenHundredTwentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1728) p = if p = 2 ∨ p ∣ 1728 then 1 else 2 :=
  nu_p_evenPair (by decide : (1728 : ℕ) ≠ 0) (by decide : Even 1728) hp

theorem nu_p_oneThousandSevenHundredThirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1730) p = if p = 2 ∨ p ∣ 1730 then 1 else 2 :=
  nu_p_evenPair (by decide : (1730 : ℕ) ≠ 0) (by decide : Even 1730) hp

theorem nu_p_oneThousandSevenHundredTwentyTwo_two : nu_p (evenPair 1722) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1722)

theorem localFactor_oneThousandSevenHundredTwentyTwo_two : localFactor (evenPair 1722) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1722 : ℕ) ≠ 0) (by decide : Even 1722)

theorem nu_p_oneThousandSevenHundredThirty_two : nu_p (evenPair 1730) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1730)

theorem localFactor_oneThousandSevenHundredThirty_two : localFactor (evenPair 1730) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1730 : ℕ) ≠ 0) (by decide : Even 1730)

end Brockian.SingularSeries.Gaps17221730
