/-
  Brockian/SingularSeriesGaps4250.lean — even binary gaps n ∈ {42,44,46,48,50}.

  HONEST SCOPE: finite/local singular-series arithmetic only.
  Does NOT claim twin-prime / HL asymptotics / Goldbach transfer / infinitude.
  Grok lane (board): non-colliding with Claude GoldbachSelectionRule / PentagonMultiplicities.
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

namespace Brockian.SingularSeries.Gaps4250

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_fortyTwo : (evenPair 42).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (42 : ℕ) ≠ 0)

theorem evenPair_card_fortyFour : (evenPair 44).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (44 : ℕ) ≠ 0)

theorem evenPair_card_fortySix : (evenPair 46).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (46 : ℕ) ≠ 0)

theorem evenPair_card_fortyEight : (evenPair 48).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (48 : ℕ) ≠ 0)

theorem evenPair_card_fifty : (evenPair 50).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (50 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_fortyTwo : IsAdmissible (evenPair 42) :=
  isAdmissible_evenPair (by decide : Even 42)

theorem isAdmissible_evenPair_fortyFour : IsAdmissible (evenPair 44) :=
  isAdmissible_evenPair (by decide : Even 44)

theorem isAdmissible_evenPair_fortySix : IsAdmissible (evenPair 46) :=
  isAdmissible_evenPair (by decide : Even 46)

theorem isAdmissible_evenPair_fortyEight : IsAdmissible (evenPair 48) :=
  isAdmissible_evenPair (by decide : Even 48)

theorem isAdmissible_evenPair_fifty : IsAdmissible (evenPair 50) :=
  isAdmissible_evenPair (by decide : Even 50)

theorem singular_series_pos_evenPair_fortyTwo : 0 < singularSeries (evenPair 42) :=
  singular_series_pos_evenPair (by decide : Even 42)

theorem singular_series_pos_evenPair_fortyFour : 0 < singularSeries (evenPair 44) :=
  singular_series_pos_evenPair (by decide : Even 44)

theorem singular_series_pos_evenPair_fortySix : 0 < singularSeries (evenPair 46) :=
  singular_series_pos_evenPair (by decide : Even 46)

theorem singular_series_pos_evenPair_fortyEight : 0 < singularSeries (evenPair 48) :=
  singular_series_pos_evenPair (by decide : Even 48)

theorem singular_series_pos_evenPair_fifty : 0 < singularSeries (evenPair 50) :=
  singular_series_pos_evenPair (by decide : Even 50)

theorem singular_series_finite_pos_evenPair_fortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 42) P :=
  singular_series_finite_pos_evenPair (by decide : Even 42) P

theorem singular_series_finite_pos_evenPair_fortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 44) P :=
  singular_series_finite_pos_evenPair (by decide : Even 44) P

theorem singular_series_finite_pos_evenPair_fortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 46) P :=
  singular_series_finite_pos_evenPair (by decide : Even 46) P

theorem singular_series_finite_pos_evenPair_fortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 48) P :=
  singular_series_finite_pos_evenPair (by decide : Even 48) P

theorem singular_series_finite_pos_evenPair_fifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 50) P :=
  singular_series_finite_pos_evenPair (by decide : Even 50) P

theorem nu_p_fortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 42) p = if p = 2 ∨ p ∣ 42 then 1 else 2 :=
  nu_p_evenPair (by decide : (42 : ℕ) ≠ 0) (by decide : Even 42) hp

theorem nu_p_fortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 44) p = if p = 2 ∨ p ∣ 44 then 1 else 2 :=
  nu_p_evenPair (by decide : (44 : ℕ) ≠ 0) (by decide : Even 44) hp

theorem nu_p_fortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 46) p = if p = 2 ∨ p ∣ 46 then 1 else 2 :=
  nu_p_evenPair (by decide : (46 : ℕ) ≠ 0) (by decide : Even 46) hp

theorem nu_p_fortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 48) p = if p = 2 ∨ p ∣ 48 then 1 else 2 :=
  nu_p_evenPair (by decide : (48 : ℕ) ≠ 0) (by decide : Even 48) hp

theorem nu_p_fifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 50) p = if p = 2 ∨ p ∣ 50 then 1 else 2 :=
  nu_p_evenPair (by decide : (50 : ℕ) ≠ 0) (by decide : Even 50) hp

theorem nu_p_fortyTwo_two : nu_p (evenPair 42) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 42)

theorem nu_p_fifty_two : nu_p (evenPair 50) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 50)

theorem localFactor_fortyTwo_two : localFactor (evenPair 42) 2 = 2 :=
  localFactor_evenPair_two (by decide : (42 : ℕ) ≠ 0) (by decide : Even 42)

theorem localFactor_fifty_two : localFactor (evenPair 50) 2 = 2 :=
  localFactor_evenPair_two (by decide : (50 : ℕ) ≠ 0) (by decide : Even 50)

end Brockian.SingularSeries.Gaps4250
