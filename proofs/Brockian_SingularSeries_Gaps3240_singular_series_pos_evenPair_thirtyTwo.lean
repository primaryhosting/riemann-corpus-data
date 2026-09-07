/-
  Brockian/SingularSeriesGaps3240.lean — even binary gaps n ∈ {32,34,36,38,40}.

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

namespace Brockian.SingularSeries.Gaps3240

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_thirtyTwo : (evenPair 32).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (32 : ℕ) ≠ 0)

theorem evenPair_card_thirtyFour : (evenPair 34).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (34 : ℕ) ≠ 0)

theorem evenPair_card_thirtySix : (evenPair 36).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (36 : ℕ) ≠ 0)

theorem evenPair_card_thirtyEight : (evenPair 38).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (38 : ℕ) ≠ 0)

theorem evenPair_card_forty : (evenPair 40).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (40 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_thirtyTwo : IsAdmissible (evenPair 32) :=
  isAdmissible_evenPair (by decide : Even 32)

theorem isAdmissible_evenPair_thirtyFour : IsAdmissible (evenPair 34) :=
  isAdmissible_evenPair (by decide : Even 34)

theorem isAdmissible_evenPair_thirtySix : IsAdmissible (evenPair 36) :=
  isAdmissible_evenPair (by decide : Even 36)

theorem isAdmissible_evenPair_thirtyEight : IsAdmissible (evenPair 38) :=
  isAdmissible_evenPair (by decide : Even 38)

theorem isAdmissible_evenPair_forty : IsAdmissible (evenPair 40) :=
  isAdmissible_evenPair (by decide : Even 40)

theorem singular_series_pos_evenPair_thirtyTwo : 0 < singularSeries (evenPair 32) :=
  singular_series_pos_evenPair (by decide : Even 32)

theorem singular_series_pos_evenPair_thirtyFour : 0 < singularSeries (evenPair 34) :=
  singular_series_pos_evenPair (by decide : Even 34)

theorem singular_series_pos_evenPair_thirtySix : 0 < singularSeries (evenPair 36) :=
  singular_series_pos_evenPair (by decide : Even 36)

theorem singular_series_pos_evenPair_thirtyEight : 0 < singularSeries (evenPair 38) :=
  singular_series_pos_evenPair (by decide : Even 38)

theorem singular_series_pos_evenPair_forty : 0 < singularSeries (evenPair 40) :=
  singular_series_pos_evenPair (by decide : Even 40)

theorem singular_series_finite_pos_evenPair_thirtyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 32) P :=
  singular_series_finite_pos_evenPair (by decide : Even 32) P

theorem singular_series_finite_pos_evenPair_thirtyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 34) P :=
  singular_series_finite_pos_evenPair (by decide : Even 34) P

theorem singular_series_finite_pos_evenPair_thirtySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 36) P :=
  singular_series_finite_pos_evenPair (by decide : Even 36) P

theorem singular_series_finite_pos_evenPair_thirtyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 38) P :=
  singular_series_finite_pos_evenPair (by decide : Even 38) P

theorem singular_series_finite_pos_evenPair_forty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 40) P :=
  singular_series_finite_pos_evenPair (by decide : Even 40) P

theorem nu_p_thirtyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 32) p = if p = 2 ∨ p ∣ 32 then 1 else 2 :=
  nu_p_evenPair (by decide : (32 : ℕ) ≠ 0) (by decide : Even 32) hp

theorem nu_p_thirtyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 34) p = if p = 2 ∨ p ∣ 34 then 1 else 2 :=
  nu_p_evenPair (by decide : (34 : ℕ) ≠ 0) (by decide : Even 34) hp

theorem nu_p_thirtySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 36) p = if p = 2 ∨ p ∣ 36 then 1 else 2 :=
  nu_p_evenPair (by decide : (36 : ℕ) ≠ 0) (by decide : Even 36) hp

theorem nu_p_thirtyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 38) p = if p = 2 ∨ p ∣ 38 then 1 else 2 :=
  nu_p_evenPair (by decide : (38 : ℕ) ≠ 0) (by decide : Even 38) hp

theorem nu_p_forty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 40) p = if p = 2 ∨ p ∣ 40 then 1 else 2 :=
  nu_p_evenPair (by decide : (40 : ℕ) ≠ 0) (by decide : Even 40) hp

theorem nu_p_thirtyTwo_two : nu_p (evenPair 32) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 32)

theorem nu_p_forty_two : nu_p (evenPair 40) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 40)

theorem localFactor_thirtyTwo_two : localFactor (evenPair 32) 2 = 2 :=
  localFactor_evenPair_two (by decide : (32 : ℕ) ≠ 0) (by decide : Even 32)

theorem localFactor_forty_two : localFactor (evenPair 40) 2 = 2 :=
  localFactor_evenPair_two (by decide : (40 : ℕ) ≠ 0) (by decide : Even 40)

end Brockian.SingularSeries.Gaps3240
