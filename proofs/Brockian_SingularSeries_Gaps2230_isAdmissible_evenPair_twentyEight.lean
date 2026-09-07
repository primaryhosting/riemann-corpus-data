/-
  Brockian/SingularSeriesGaps2230.lean — even binary gaps n ∈ {22,24,26,28,30}.

  HONEST SCOPE: finite/local singular-series arithmetic only.
  Does NOT claim twin-prime / HL asymptotics / Goldbach transfer / infinitude.
-/
import Mathlib
import Brockian.SingularSeries
import Brockian.SingularSeriesWire
import Brockian.SingularSeriesExamples
import Brockian.SingularSeriesMoreExamples
import Brockian.SingularSeriesEvenMore

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators Classical
open Real Finset
open Brockian.SingularSeries
open Brockian.SingularSeries.Wire
open Brockian.SingularSeries.Examples
open Brockian.SingularSeries.MoreExamples

namespace Brockian.SingularSeries.Gaps2230

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-! ## Cardinality of nonzero even pairs -/

theorem evenPair_card_twentyTwo : (evenPair 22).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (22 : ℕ) ≠ 0)

theorem evenPair_card_twentyFour : (evenPair 24).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (24 : ℕ) ≠ 0)

theorem evenPair_card_twentySix : (evenPair 26).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (26 : ℕ) ≠ 0)

theorem evenPair_card_twentyEight : (evenPair 28).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (28 : ℕ) ≠ 0)

theorem evenPair_card_thirty : (evenPair 30).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (30 : ℕ) ≠ 0)

/-! ## Admissibility -/

theorem isAdmissible_evenPair_twentyTwo : IsAdmissible (evenPair 22) :=
  isAdmissible_evenPair (by decide : Even 22)

theorem isAdmissible_evenPair_twentyFour : IsAdmissible (evenPair 24) :=
  isAdmissible_evenPair (by decide : Even 24)

theorem isAdmissible_evenPair_twentySix : IsAdmissible (evenPair 26) :=
  isAdmissible_evenPair (by decide : Even 26)

theorem isAdmissible_evenPair_twentyEight : IsAdmissible (evenPair 28) :=
  isAdmissible_evenPair (by decide : Even 28)

theorem isAdmissible_evenPair_thirty : IsAdmissible (evenPair 30) :=
  isAdmissible_evenPair (by decide : Even 30)

/-! ## Positive singular series (infinite product) -/

theorem singular_series_pos_evenPair_twentyTwo : 0 < singularSeries (evenPair 22) :=
  singular_series_pos_evenPair (by decide : Even 22)

theorem singular_series_pos_evenPair_twentyFour : 0 < singularSeries (evenPair 24) :=
  singular_series_pos_evenPair (by decide : Even 24)

theorem singular_series_pos_evenPair_twentySix : 0 < singularSeries (evenPair 26) :=
  singular_series_pos_evenPair (by decide : Even 26)

theorem singular_series_pos_evenPair_twentyEight : 0 < singularSeries (evenPair 28) :=
  singular_series_pos_evenPair (by decide : Even 28)

theorem singular_series_pos_evenPair_thirty : 0 < singularSeries (evenPair 30) :=
  singular_series_pos_evenPair (by decide : Even 30)

theorem singular_series_finite_pos_evenPair_twentyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 22) P :=
  singular_series_finite_pos_evenPair (by decide : Even 22) P

theorem singular_series_finite_pos_evenPair_twentyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 24) P :=
  singular_series_finite_pos_evenPair (by decide : Even 24) P

theorem singular_series_finite_pos_evenPair_twentySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 26) P :=
  singular_series_finite_pos_evenPair (by decide : Even 26) P

theorem singular_series_finite_pos_evenPair_twentyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 28) P :=
  singular_series_finite_pos_evenPair (by decide : Even 28) P

theorem singular_series_finite_pos_evenPair_thirty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 30) P :=
  singular_series_finite_pos_evenPair (by decide : Even 30) P

/-! ## Residue counts via general even-pair law -/

theorem nu_p_twentyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 22) p = if p = 2 ∨ p ∣ 22 then 1 else 2 :=
  nu_p_evenPair (by decide : (22 : ℕ) ≠ 0) (by decide : Even 22) hp

theorem nu_p_twentyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 24) p = if p = 2 ∨ p ∣ 24 then 1 else 2 :=
  nu_p_evenPair (by decide : (24 : ℕ) ≠ 0) (by decide : Even 24) hp

theorem nu_p_twentySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 26) p = if p = 2 ∨ p ∣ 26 then 1 else 2 :=
  nu_p_evenPair (by decide : (26 : ℕ) ≠ 0) (by decide : Even 26) hp

theorem nu_p_twentyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 28) p = if p = 2 ∨ p ∣ 28 then 1 else 2 :=
  nu_p_evenPair (by decide : (28 : ℕ) ≠ 0) (by decide : Even 28) hp

theorem nu_p_thirty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 30) p = if p = 2 ∨ p ∣ 30 then 1 else 2 :=
  nu_p_evenPair (by decide : (30 : ℕ) ≠ 0) (by decide : Even 30) hp

theorem nu_p_twentyTwo_two : nu_p (evenPair 22) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 22)

theorem nu_p_thirty_two : nu_p (evenPair 30) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 30)

theorem localFactor_twentyTwo_two : localFactor (evenPair 22) 2 = 2 :=
  localFactor_evenPair_two (by decide : (22 : ℕ) ≠ 0) (by decide : Even 22)

theorem localFactor_thirty_two : localFactor (evenPair 30) 2 = 2 :=
  localFactor_evenPair_two (by decide : (30 : ℕ) ≠ 0) (by decide : Even 30)

end Brockian.SingularSeries.Gaps2230
