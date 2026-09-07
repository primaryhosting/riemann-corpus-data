/-
  Brockian/SingularSeriesGaps752760.lean — even binary gaps n ∈ {752, 754, 756, 758, 760}.

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

namespace Brockian.SingularSeries.Gaps752760

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sevenHundredFiftyTwo : (evenPair 752).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (752 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredFiftyFour : (evenPair 754).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (754 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredFiftySix : (evenPair 756).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (756 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredFiftyEight : (evenPair 758).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (758 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredSixty : (evenPair 760).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (760 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sevenHundredFiftyTwo : IsAdmissible (evenPair 752) :=
  isAdmissible_evenPair (by decide : Even 752)

theorem isAdmissible_evenPair_sevenHundredFiftyFour : IsAdmissible (evenPair 754) :=
  isAdmissible_evenPair (by decide : Even 754)

theorem isAdmissible_evenPair_sevenHundredFiftySix : IsAdmissible (evenPair 756) :=
  isAdmissible_evenPair (by decide : Even 756)

theorem isAdmissible_evenPair_sevenHundredFiftyEight : IsAdmissible (evenPair 758) :=
  isAdmissible_evenPair (by decide : Even 758)

theorem isAdmissible_evenPair_sevenHundredSixty : IsAdmissible (evenPair 760) :=
  isAdmissible_evenPair (by decide : Even 760)

theorem singular_series_pos_evenPair_sevenHundredFiftyTwo : 0 < singularSeries (evenPair 752) :=
  singular_series_pos_evenPair (by decide : Even 752)

theorem singular_series_pos_evenPair_sevenHundredFiftyFour : 0 < singularSeries (evenPair 754) :=
  singular_series_pos_evenPair (by decide : Even 754)

theorem singular_series_pos_evenPair_sevenHundredFiftySix : 0 < singularSeries (evenPair 756) :=
  singular_series_pos_evenPair (by decide : Even 756)

theorem singular_series_pos_evenPair_sevenHundredFiftyEight : 0 < singularSeries (evenPair 758) :=
  singular_series_pos_evenPair (by decide : Even 758)

theorem singular_series_pos_evenPair_sevenHundredSixty : 0 < singularSeries (evenPair 760) :=
  singular_series_pos_evenPair (by decide : Even 760)

theorem singular_series_finite_pos_evenPair_sevenHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 752) P :=
  singular_series_finite_pos_evenPair (by decide : Even 752) P

theorem singular_series_finite_pos_evenPair_sevenHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 754) P :=
  singular_series_finite_pos_evenPair (by decide : Even 754) P

theorem singular_series_finite_pos_evenPair_sevenHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 756) P :=
  singular_series_finite_pos_evenPair (by decide : Even 756) P

theorem singular_series_finite_pos_evenPair_sevenHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 758) P :=
  singular_series_finite_pos_evenPair (by decide : Even 758) P

theorem singular_series_finite_pos_evenPair_sevenHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 760) P :=
  singular_series_finite_pos_evenPair (by decide : Even 760) P

theorem nu_p_sevenHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 752) p = if p = 2 ∨ p ∣ 752 then 1 else 2 :=
  nu_p_evenPair (by decide : (752 : ℕ) ≠ 0) (by decide : Even 752) hp

theorem nu_p_sevenHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 754) p = if p = 2 ∨ p ∣ 754 then 1 else 2 :=
  nu_p_evenPair (by decide : (754 : ℕ) ≠ 0) (by decide : Even 754) hp

theorem nu_p_sevenHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 756) p = if p = 2 ∨ p ∣ 756 then 1 else 2 :=
  nu_p_evenPair (by decide : (756 : ℕ) ≠ 0) (by decide : Even 756) hp

theorem nu_p_sevenHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 758) p = if p = 2 ∨ p ∣ 758 then 1 else 2 :=
  nu_p_evenPair (by decide : (758 : ℕ) ≠ 0) (by decide : Even 758) hp

theorem nu_p_sevenHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 760) p = if p = 2 ∨ p ∣ 760 then 1 else 2 :=
  nu_p_evenPair (by decide : (760 : ℕ) ≠ 0) (by decide : Even 760) hp

theorem nu_p_sevenHundredFiftyTwo_two : nu_p (evenPair 752) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 752)

theorem localFactor_sevenHundredFiftyTwo_two : localFactor (evenPair 752) 2 = 2 :=
  localFactor_evenPair_two (by decide : (752 : ℕ) ≠ 0) (by decide : Even 752)

theorem nu_p_sevenHundredSixty_two : nu_p (evenPair 760) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 760)

theorem localFactor_sevenHundredSixty_two : localFactor (evenPair 760) 2 = 2 :=
  localFactor_evenPair_two (by decide : (760 : ℕ) ≠ 0) (by decide : Even 760)

end Brockian.SingularSeries.Gaps752760
