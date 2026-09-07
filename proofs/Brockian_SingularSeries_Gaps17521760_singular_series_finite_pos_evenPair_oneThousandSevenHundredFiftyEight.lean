/-
  Brockian/SingularSeriesGaps17521760.lean — even binary gaps n ∈ {1752, 1754, 1756, 1758, 1760}.

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

namespace Brockian.SingularSeries.Gaps17521760

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandSevenHundredFiftyTwo : (evenPair 1752).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1752 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredFiftyFour : (evenPair 1754).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1754 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredFiftySix : (evenPair 1756).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1756 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredFiftyEight : (evenPair 1758).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1758 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandSevenHundredSixty : (evenPair 1760).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1760 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandSevenHundredFiftyTwo : IsAdmissible (evenPair 1752) :=
  isAdmissible_evenPair (by decide : Even 1752)

theorem isAdmissible_evenPair_oneThousandSevenHundredFiftyFour : IsAdmissible (evenPair 1754) :=
  isAdmissible_evenPair (by decide : Even 1754)

theorem isAdmissible_evenPair_oneThousandSevenHundredFiftySix : IsAdmissible (evenPair 1756) :=
  isAdmissible_evenPair (by decide : Even 1756)

theorem isAdmissible_evenPair_oneThousandSevenHundredFiftyEight : IsAdmissible (evenPair 1758) :=
  isAdmissible_evenPair (by decide : Even 1758)

theorem isAdmissible_evenPair_oneThousandSevenHundredSixty : IsAdmissible (evenPair 1760) :=
  isAdmissible_evenPair (by decide : Even 1760)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFiftyTwo : 0 < singularSeries (evenPair 1752) :=
  singular_series_pos_evenPair (by decide : Even 1752)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFiftyFour : 0 < singularSeries (evenPair 1754) :=
  singular_series_pos_evenPair (by decide : Even 1754)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFiftySix : 0 < singularSeries (evenPair 1756) :=
  singular_series_pos_evenPair (by decide : Even 1756)

theorem singular_series_pos_evenPair_oneThousandSevenHundredFiftyEight : 0 < singularSeries (evenPair 1758) :=
  singular_series_pos_evenPair (by decide : Even 1758)

theorem singular_series_pos_evenPair_oneThousandSevenHundredSixty : 0 < singularSeries (evenPair 1760) :=
  singular_series_pos_evenPair (by decide : Even 1760)

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1752) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1752) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1754) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1754) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1756) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1756) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1758) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1758) P

theorem singular_series_finite_pos_evenPair_oneThousandSevenHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1760) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1760) P

theorem nu_p_oneThousandSevenHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1752) p = if p = 2 ∨ p ∣ 1752 then 1 else 2 :=
  nu_p_evenPair (by decide : (1752 : ℕ) ≠ 0) (by decide : Even 1752) hp

theorem nu_p_oneThousandSevenHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1754) p = if p = 2 ∨ p ∣ 1754 then 1 else 2 :=
  nu_p_evenPair (by decide : (1754 : ℕ) ≠ 0) (by decide : Even 1754) hp

theorem nu_p_oneThousandSevenHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1756) p = if p = 2 ∨ p ∣ 1756 then 1 else 2 :=
  nu_p_evenPair (by decide : (1756 : ℕ) ≠ 0) (by decide : Even 1756) hp

theorem nu_p_oneThousandSevenHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1758) p = if p = 2 ∨ p ∣ 1758 then 1 else 2 :=
  nu_p_evenPair (by decide : (1758 : ℕ) ≠ 0) (by decide : Even 1758) hp

theorem nu_p_oneThousandSevenHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1760) p = if p = 2 ∨ p ∣ 1760 then 1 else 2 :=
  nu_p_evenPair (by decide : (1760 : ℕ) ≠ 0) (by decide : Even 1760) hp

theorem nu_p_oneThousandSevenHundredFiftyTwo_two : nu_p (evenPair 1752) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1752)

theorem localFactor_oneThousandSevenHundredFiftyTwo_two : localFactor (evenPair 1752) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1752 : ℕ) ≠ 0) (by decide : Even 1752)

theorem nu_p_oneThousandSevenHundredSixty_two : nu_p (evenPair 1760) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1760)

theorem localFactor_oneThousandSevenHundredSixty_two : localFactor (evenPair 1760) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1760 : ℕ) ≠ 0) (by decide : Even 1760)

end Brockian.SingularSeries.Gaps17521760
