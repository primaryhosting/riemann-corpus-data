/-
  Brockian/SingularSeriesGaps6270.lean — even binary gaps n ∈ {62,64,66,68,70}.

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

namespace Brockian.SingularSeries.Gaps6270

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sixtyTwo : (evenPair 62).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (62 : ℕ) ≠ 0)

theorem evenPair_card_sixtyFour : (evenPair 64).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (64 : ℕ) ≠ 0)

theorem evenPair_card_sixtySix : (evenPair 66).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (66 : ℕ) ≠ 0)

theorem evenPair_card_sixtyEight : (evenPair 68).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (68 : ℕ) ≠ 0)

theorem evenPair_card_seventy : (evenPair 70).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (70 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sixtyTwo : IsAdmissible (evenPair 62) :=
  isAdmissible_evenPair (by decide : Even 62)

theorem isAdmissible_evenPair_sixtyFour : IsAdmissible (evenPair 64) :=
  isAdmissible_evenPair (by decide : Even 64)

theorem isAdmissible_evenPair_sixtySix : IsAdmissible (evenPair 66) :=
  isAdmissible_evenPair (by decide : Even 66)

theorem isAdmissible_evenPair_sixtyEight : IsAdmissible (evenPair 68) :=
  isAdmissible_evenPair (by decide : Even 68)

theorem isAdmissible_evenPair_seventy : IsAdmissible (evenPair 70) :=
  isAdmissible_evenPair (by decide : Even 70)

theorem singular_series_pos_evenPair_sixtyTwo : 0 < singularSeries (evenPair 62) :=
  singular_series_pos_evenPair (by decide : Even 62)

theorem singular_series_pos_evenPair_sixtyFour : 0 < singularSeries (evenPair 64) :=
  singular_series_pos_evenPair (by decide : Even 64)

theorem singular_series_pos_evenPair_sixtySix : 0 < singularSeries (evenPair 66) :=
  singular_series_pos_evenPair (by decide : Even 66)

theorem singular_series_pos_evenPair_sixtyEight : 0 < singularSeries (evenPair 68) :=
  singular_series_pos_evenPair (by decide : Even 68)

theorem singular_series_pos_evenPair_seventy : 0 < singularSeries (evenPair 70) :=
  singular_series_pos_evenPair (by decide : Even 70)

theorem singular_series_finite_pos_evenPair_sixtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 62) P :=
  singular_series_finite_pos_evenPair (by decide : Even 62) P

theorem singular_series_finite_pos_evenPair_sixtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 64) P :=
  singular_series_finite_pos_evenPair (by decide : Even 64) P

theorem singular_series_finite_pos_evenPair_sixtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 66) P :=
  singular_series_finite_pos_evenPair (by decide : Even 66) P

theorem singular_series_finite_pos_evenPair_sixtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 68) P :=
  singular_series_finite_pos_evenPair (by decide : Even 68) P

theorem singular_series_finite_pos_evenPair_seventy (P : ℕ) :
    0 < singularSeriesFinite (evenPair 70) P :=
  singular_series_finite_pos_evenPair (by decide : Even 70) P

theorem nu_p_sixtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 62) p = if p = 2 ∨ p ∣ 62 then 1 else 2 :=
  nu_p_evenPair (by decide : (62 : ℕ) ≠ 0) (by decide : Even 62) hp

theorem nu_p_sixtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 64) p = if p = 2 ∨ p ∣ 64 then 1 else 2 :=
  nu_p_evenPair (by decide : (64 : ℕ) ≠ 0) (by decide : Even 64) hp

theorem nu_p_sixtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 66) p = if p = 2 ∨ p ∣ 66 then 1 else 2 :=
  nu_p_evenPair (by decide : (66 : ℕ) ≠ 0) (by decide : Even 66) hp

theorem nu_p_sixtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 68) p = if p = 2 ∨ p ∣ 68 then 1 else 2 :=
  nu_p_evenPair (by decide : (68 : ℕ) ≠ 0) (by decide : Even 68) hp

theorem nu_p_seventy (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 70) p = if p = 2 ∨ p ∣ 70 then 1 else 2 :=
  nu_p_evenPair (by decide : (70 : ℕ) ≠ 0) (by decide : Even 70) hp

theorem nu_p_sixtyTwo_two : nu_p (evenPair 62) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 62)

theorem nu_p_seventy_two : nu_p (evenPair 70) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 70)

theorem localFactor_sixtyTwo_two : localFactor (evenPair 62) 2 = 2 :=
  localFactor_evenPair_two (by decide : (62 : ℕ) ≠ 0) (by decide : Even 62)

theorem localFactor_seventy_two : localFactor (evenPair 70) 2 = 2 :=
  localFactor_evenPair_two (by decide : (70 : ℕ) ≠ 0) (by decide : Even 70)

end Brockian.SingularSeries.Gaps6270
