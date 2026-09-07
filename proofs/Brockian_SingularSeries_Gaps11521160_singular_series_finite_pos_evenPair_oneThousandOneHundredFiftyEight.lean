/-
  Brockian/SingularSeriesGaps11521160.lean — even binary gaps n ∈ {1152, 1154, 1156, 1158, 1160}.

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

namespace Brockian.SingularSeries.Gaps11521160

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandOneHundredFiftyTwo : (evenPair 1152).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1152 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredFiftyFour : (evenPair 1154).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1154 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredFiftySix : (evenPair 1156).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1156 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredFiftyEight : (evenPair 1158).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1158 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredSixty : (evenPair 1160).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1160 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandOneHundredFiftyTwo : IsAdmissible (evenPair 1152) :=
  isAdmissible_evenPair (by decide : Even 1152)

theorem isAdmissible_evenPair_oneThousandOneHundredFiftyFour : IsAdmissible (evenPair 1154) :=
  isAdmissible_evenPair (by decide : Even 1154)

theorem isAdmissible_evenPair_oneThousandOneHundredFiftySix : IsAdmissible (evenPair 1156) :=
  isAdmissible_evenPair (by decide : Even 1156)

theorem isAdmissible_evenPair_oneThousandOneHundredFiftyEight : IsAdmissible (evenPair 1158) :=
  isAdmissible_evenPair (by decide : Even 1158)

theorem isAdmissible_evenPair_oneThousandOneHundredSixty : IsAdmissible (evenPair 1160) :=
  isAdmissible_evenPair (by decide : Even 1160)

theorem singular_series_pos_evenPair_oneThousandOneHundredFiftyTwo : 0 < singularSeries (evenPair 1152) :=
  singular_series_pos_evenPair (by decide : Even 1152)

theorem singular_series_pos_evenPair_oneThousandOneHundredFiftyFour : 0 < singularSeries (evenPair 1154) :=
  singular_series_pos_evenPair (by decide : Even 1154)

theorem singular_series_pos_evenPair_oneThousandOneHundredFiftySix : 0 < singularSeries (evenPair 1156) :=
  singular_series_pos_evenPair (by decide : Even 1156)

theorem singular_series_pos_evenPair_oneThousandOneHundredFiftyEight : 0 < singularSeries (evenPair 1158) :=
  singular_series_pos_evenPair (by decide : Even 1158)

theorem singular_series_pos_evenPair_oneThousandOneHundredSixty : 0 < singularSeries (evenPair 1160) :=
  singular_series_pos_evenPair (by decide : Even 1160)

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1152) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1152) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1154) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1154) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1156) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1156) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1158) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1158) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1160) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1160) P

theorem nu_p_oneThousandOneHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1152) p = if p = 2 ∨ p ∣ 1152 then 1 else 2 :=
  nu_p_evenPair (by decide : (1152 : ℕ) ≠ 0) (by decide : Even 1152) hp

theorem nu_p_oneThousandOneHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1154) p = if p = 2 ∨ p ∣ 1154 then 1 else 2 :=
  nu_p_evenPair (by decide : (1154 : ℕ) ≠ 0) (by decide : Even 1154) hp

theorem nu_p_oneThousandOneHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1156) p = if p = 2 ∨ p ∣ 1156 then 1 else 2 :=
  nu_p_evenPair (by decide : (1156 : ℕ) ≠ 0) (by decide : Even 1156) hp

theorem nu_p_oneThousandOneHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1158) p = if p = 2 ∨ p ∣ 1158 then 1 else 2 :=
  nu_p_evenPair (by decide : (1158 : ℕ) ≠ 0) (by decide : Even 1158) hp

theorem nu_p_oneThousandOneHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1160) p = if p = 2 ∨ p ∣ 1160 then 1 else 2 :=
  nu_p_evenPair (by decide : (1160 : ℕ) ≠ 0) (by decide : Even 1160) hp

theorem nu_p_oneThousandOneHundredFiftyTwo_two : nu_p (evenPair 1152) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1152)

theorem localFactor_oneThousandOneHundredFiftyTwo_two : localFactor (evenPair 1152) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1152 : ℕ) ≠ 0) (by decide : Even 1152)

theorem nu_p_oneThousandOneHundredSixty_two : nu_p (evenPair 1160) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1160)

theorem localFactor_oneThousandOneHundredSixty_two : localFactor (evenPair 1160) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1160 : ℕ) ≠ 0) (by decide : Even 1160)

end Brockian.SingularSeries.Gaps11521160
