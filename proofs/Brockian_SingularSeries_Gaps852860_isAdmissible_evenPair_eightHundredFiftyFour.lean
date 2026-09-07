/-
  Brockian/SingularSeriesGaps852860.lean — even binary gaps n ∈ {852, 854, 856, 858, 860}.

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

namespace Brockian.SingularSeries.Gaps852860

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_eightHundredFiftyTwo : (evenPair 852).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (852 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredFiftyFour : (evenPair 854).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (854 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredFiftySix : (evenPair 856).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (856 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredFiftyEight : (evenPair 858).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (858 : ℕ) ≠ 0)

theorem evenPair_card_eightHundredSixty : (evenPair 860).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (860 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_eightHundredFiftyTwo : IsAdmissible (evenPair 852) :=
  isAdmissible_evenPair (by decide : Even 852)

theorem isAdmissible_evenPair_eightHundredFiftyFour : IsAdmissible (evenPair 854) :=
  isAdmissible_evenPair (by decide : Even 854)

theorem isAdmissible_evenPair_eightHundredFiftySix : IsAdmissible (evenPair 856) :=
  isAdmissible_evenPair (by decide : Even 856)

theorem isAdmissible_evenPair_eightHundredFiftyEight : IsAdmissible (evenPair 858) :=
  isAdmissible_evenPair (by decide : Even 858)

theorem isAdmissible_evenPair_eightHundredSixty : IsAdmissible (evenPair 860) :=
  isAdmissible_evenPair (by decide : Even 860)

theorem singular_series_pos_evenPair_eightHundredFiftyTwo : 0 < singularSeries (evenPair 852) :=
  singular_series_pos_evenPair (by decide : Even 852)

theorem singular_series_pos_evenPair_eightHundredFiftyFour : 0 < singularSeries (evenPair 854) :=
  singular_series_pos_evenPair (by decide : Even 854)

theorem singular_series_pos_evenPair_eightHundredFiftySix : 0 < singularSeries (evenPair 856) :=
  singular_series_pos_evenPair (by decide : Even 856)

theorem singular_series_pos_evenPair_eightHundredFiftyEight : 0 < singularSeries (evenPair 858) :=
  singular_series_pos_evenPair (by decide : Even 858)

theorem singular_series_pos_evenPair_eightHundredSixty : 0 < singularSeries (evenPair 860) :=
  singular_series_pos_evenPair (by decide : Even 860)

theorem singular_series_finite_pos_evenPair_eightHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 852) P :=
  singular_series_finite_pos_evenPair (by decide : Even 852) P

theorem singular_series_finite_pos_evenPair_eightHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 854) P :=
  singular_series_finite_pos_evenPair (by decide : Even 854) P

theorem singular_series_finite_pos_evenPair_eightHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 856) P :=
  singular_series_finite_pos_evenPair (by decide : Even 856) P

theorem singular_series_finite_pos_evenPair_eightHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 858) P :=
  singular_series_finite_pos_evenPair (by decide : Even 858) P

theorem singular_series_finite_pos_evenPair_eightHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 860) P :=
  singular_series_finite_pos_evenPair (by decide : Even 860) P

theorem nu_p_eightHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 852) p = if p = 2 ∨ p ∣ 852 then 1 else 2 :=
  nu_p_evenPair (by decide : (852 : ℕ) ≠ 0) (by decide : Even 852) hp

theorem nu_p_eightHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 854) p = if p = 2 ∨ p ∣ 854 then 1 else 2 :=
  nu_p_evenPair (by decide : (854 : ℕ) ≠ 0) (by decide : Even 854) hp

theorem nu_p_eightHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 856) p = if p = 2 ∨ p ∣ 856 then 1 else 2 :=
  nu_p_evenPair (by decide : (856 : ℕ) ≠ 0) (by decide : Even 856) hp

theorem nu_p_eightHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 858) p = if p = 2 ∨ p ∣ 858 then 1 else 2 :=
  nu_p_evenPair (by decide : (858 : ℕ) ≠ 0) (by decide : Even 858) hp

theorem nu_p_eightHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 860) p = if p = 2 ∨ p ∣ 860 then 1 else 2 :=
  nu_p_evenPair (by decide : (860 : ℕ) ≠ 0) (by decide : Even 860) hp

theorem nu_p_eightHundredFiftyTwo_two : nu_p (evenPair 852) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 852)

theorem localFactor_eightHundredFiftyTwo_two : localFactor (evenPair 852) 2 = 2 :=
  localFactor_evenPair_two (by decide : (852 : ℕ) ≠ 0) (by decide : Even 852)

theorem nu_p_eightHundredSixty_two : nu_p (evenPair 860) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 860)

theorem localFactor_eightHundredSixty_two : localFactor (evenPair 860) 2 = 2 :=
  localFactor_evenPair_two (by decide : (860 : ℕ) ≠ 0) (by decide : Even 860)

end Brockian.SingularSeries.Gaps852860
