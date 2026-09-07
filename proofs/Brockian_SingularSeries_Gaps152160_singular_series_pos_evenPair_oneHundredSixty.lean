/-
  Brockian/SingularSeriesGaps152160.lean — even binary gaps n ∈ {152, 154, 156, 158, 160}.

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

namespace Brockian.SingularSeries.Gaps152160

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneHundredFiftyTwo : (evenPair 152).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (152 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredFiftyFour : (evenPair 154).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (154 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredFiftySix : (evenPair 156).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (156 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredFiftyEight : (evenPair 158).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (158 : ℕ) ≠ 0)

theorem evenPair_card_oneHundredSixty : (evenPair 160).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (160 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneHundredFiftyTwo : IsAdmissible (evenPair 152) :=
  isAdmissible_evenPair (by decide : Even 152)

theorem isAdmissible_evenPair_oneHundredFiftyFour : IsAdmissible (evenPair 154) :=
  isAdmissible_evenPair (by decide : Even 154)

theorem isAdmissible_evenPair_oneHundredFiftySix : IsAdmissible (evenPair 156) :=
  isAdmissible_evenPair (by decide : Even 156)

theorem isAdmissible_evenPair_oneHundredFiftyEight : IsAdmissible (evenPair 158) :=
  isAdmissible_evenPair (by decide : Even 158)

theorem isAdmissible_evenPair_oneHundredSixty : IsAdmissible (evenPair 160) :=
  isAdmissible_evenPair (by decide : Even 160)

theorem singular_series_pos_evenPair_oneHundredFiftyTwo : 0 < singularSeries (evenPair 152) :=
  singular_series_pos_evenPair (by decide : Even 152)

theorem singular_series_pos_evenPair_oneHundredFiftyFour : 0 < singularSeries (evenPair 154) :=
  singular_series_pos_evenPair (by decide : Even 154)

theorem singular_series_pos_evenPair_oneHundredFiftySix : 0 < singularSeries (evenPair 156) :=
  singular_series_pos_evenPair (by decide : Even 156)

theorem singular_series_pos_evenPair_oneHundredFiftyEight : 0 < singularSeries (evenPair 158) :=
  singular_series_pos_evenPair (by decide : Even 158)

theorem singular_series_pos_evenPair_oneHundredSixty : 0 < singularSeries (evenPair 160) :=
  singular_series_pos_evenPair (by decide : Even 160)

theorem singular_series_finite_pos_evenPair_oneHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 152) P :=
  singular_series_finite_pos_evenPair (by decide : Even 152) P

theorem singular_series_finite_pos_evenPair_oneHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 154) P :=
  singular_series_finite_pos_evenPair (by decide : Even 154) P

theorem singular_series_finite_pos_evenPair_oneHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 156) P :=
  singular_series_finite_pos_evenPair (by decide : Even 156) P

theorem singular_series_finite_pos_evenPair_oneHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 158) P :=
  singular_series_finite_pos_evenPair (by decide : Even 158) P

theorem singular_series_finite_pos_evenPair_oneHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 160) P :=
  singular_series_finite_pos_evenPair (by decide : Even 160) P

theorem nu_p_oneHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 152) p = if p = 2 ∨ p ∣ 152 then 1 else 2 :=
  nu_p_evenPair (by decide : (152 : ℕ) ≠ 0) (by decide : Even 152) hp

theorem nu_p_oneHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 154) p = if p = 2 ∨ p ∣ 154 then 1 else 2 :=
  nu_p_evenPair (by decide : (154 : ℕ) ≠ 0) (by decide : Even 154) hp

theorem nu_p_oneHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 156) p = if p = 2 ∨ p ∣ 156 then 1 else 2 :=
  nu_p_evenPair (by decide : (156 : ℕ) ≠ 0) (by decide : Even 156) hp

theorem nu_p_oneHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 158) p = if p = 2 ∨ p ∣ 158 then 1 else 2 :=
  nu_p_evenPair (by decide : (158 : ℕ) ≠ 0) (by decide : Even 158) hp

theorem nu_p_oneHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 160) p = if p = 2 ∨ p ∣ 160 then 1 else 2 :=
  nu_p_evenPair (by decide : (160 : ℕ) ≠ 0) (by decide : Even 160) hp

theorem nu_p_oneHundredFiftyTwo_two : nu_p (evenPair 152) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 152)

theorem localFactor_oneHundredFiftyTwo_two : localFactor (evenPair 152) 2 = 2 :=
  localFactor_evenPair_two (by decide : (152 : ℕ) ≠ 0) (by decide : Even 152)

theorem nu_p_oneHundredSixty_two : nu_p (evenPair 160) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 160)

theorem localFactor_oneHundredSixty_two : localFactor (evenPair 160) 2 = 2 :=
  localFactor_evenPair_two (by decide : (160 : ℕ) ≠ 0) (by decide : Even 160)

end Brockian.SingularSeries.Gaps152160
