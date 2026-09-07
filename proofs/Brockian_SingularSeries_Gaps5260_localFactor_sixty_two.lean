/-
  Brockian/SingularSeriesGaps5260.lean — even binary gaps n ∈ {52,54,56,58,60}.

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

namespace Brockian.SingularSeries.Gaps5260

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fiftyTwo : (evenPair 52).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (52 : ℕ) ≠ 0)

theorem evenPair_card_fiftyFour : (evenPair 54).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (54 : ℕ) ≠ 0)

theorem evenPair_card_fiftySix : (evenPair 56).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (56 : ℕ) ≠ 0)

theorem evenPair_card_fiftyEight : (evenPair 58).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (58 : ℕ) ≠ 0)

theorem evenPair_card_sixty : (evenPair 60).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (60 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fiftyTwo : IsAdmissible (evenPair 52) :=
  isAdmissible_evenPair (by decide : Even 52)

theorem isAdmissible_evenPair_fiftyFour : IsAdmissible (evenPair 54) :=
  isAdmissible_evenPair (by decide : Even 54)

theorem isAdmissible_evenPair_fiftySix : IsAdmissible (evenPair 56) :=
  isAdmissible_evenPair (by decide : Even 56)

theorem isAdmissible_evenPair_fiftyEight : IsAdmissible (evenPair 58) :=
  isAdmissible_evenPair (by decide : Even 58)

theorem isAdmissible_evenPair_sixty : IsAdmissible (evenPair 60) :=
  isAdmissible_evenPair (by decide : Even 60)

theorem singular_series_pos_evenPair_fiftyTwo : 0 < singularSeries (evenPair 52) :=
  singular_series_pos_evenPair (by decide : Even 52)

theorem singular_series_pos_evenPair_fiftyFour : 0 < singularSeries (evenPair 54) :=
  singular_series_pos_evenPair (by decide : Even 54)

theorem singular_series_pos_evenPair_fiftySix : 0 < singularSeries (evenPair 56) :=
  singular_series_pos_evenPair (by decide : Even 56)

theorem singular_series_pos_evenPair_fiftyEight : 0 < singularSeries (evenPair 58) :=
  singular_series_pos_evenPair (by decide : Even 58)

theorem singular_series_pos_evenPair_sixty : 0 < singularSeries (evenPair 60) :=
  singular_series_pos_evenPair (by decide : Even 60)

theorem singular_series_finite_pos_evenPair_fiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 52) P :=
  singular_series_finite_pos_evenPair (by decide : Even 52) P

theorem singular_series_finite_pos_evenPair_fiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 54) P :=
  singular_series_finite_pos_evenPair (by decide : Even 54) P

theorem singular_series_finite_pos_evenPair_fiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 56) P :=
  singular_series_finite_pos_evenPair (by decide : Even 56) P

theorem singular_series_finite_pos_evenPair_fiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 58) P :=
  singular_series_finite_pos_evenPair (by decide : Even 58) P

theorem singular_series_finite_pos_evenPair_sixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 60) P :=
  singular_series_finite_pos_evenPair (by decide : Even 60) P

theorem nu_p_fiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 52) p = if p = 2 ∨ p ∣ 52 then 1 else 2 :=
  nu_p_evenPair (by decide : (52 : ℕ) ≠ 0) (by decide : Even 52) hp

theorem nu_p_fiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 54) p = if p = 2 ∨ p ∣ 54 then 1 else 2 :=
  nu_p_evenPair (by decide : (54 : ℕ) ≠ 0) (by decide : Even 54) hp

theorem nu_p_fiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 56) p = if p = 2 ∨ p ∣ 56 then 1 else 2 :=
  nu_p_evenPair (by decide : (56 : ℕ) ≠ 0) (by decide : Even 56) hp

theorem nu_p_fiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 58) p = if p = 2 ∨ p ∣ 58 then 1 else 2 :=
  nu_p_evenPair (by decide : (58 : ℕ) ≠ 0) (by decide : Even 58) hp

theorem nu_p_sixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 60) p = if p = 2 ∨ p ∣ 60 then 1 else 2 :=
  nu_p_evenPair (by decide : (60 : ℕ) ≠ 0) (by decide : Even 60) hp

theorem nu_p_fiftyTwo_two : nu_p (evenPair 52) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 52)

theorem nu_p_sixty_two : nu_p (evenPair 60) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 60)

theorem localFactor_fiftyTwo_two : localFactor (evenPair 52) 2 = 2 :=
  localFactor_evenPair_two (by decide : (52 : ℕ) ≠ 0) (by decide : Even 52)

theorem localFactor_sixty_two : localFactor (evenPair 60) 2 = 2 :=
  localFactor_evenPair_two (by decide : (60 : ℕ) ≠ 0) (by decide : Even 60)

end Brockian.SingularSeries.Gaps5260
