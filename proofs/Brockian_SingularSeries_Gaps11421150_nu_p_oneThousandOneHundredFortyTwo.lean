/-
  Brockian/SingularSeriesGaps11421150.lean — even binary gaps n ∈ {1142, 1144, 1146, 1148, 1150}.

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

namespace Brockian.SingularSeries.Gaps11421150

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandOneHundredFortyTwo : (evenPair 1142).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1142 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredFortyFour : (evenPair 1144).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1144 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredFortySix : (evenPair 1146).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1146 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredFortyEight : (evenPair 1148).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1148 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandOneHundredFifty : (evenPair 1150).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1150 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandOneHundredFortyTwo : IsAdmissible (evenPair 1142) :=
  isAdmissible_evenPair (by decide : Even 1142)

theorem isAdmissible_evenPair_oneThousandOneHundredFortyFour : IsAdmissible (evenPair 1144) :=
  isAdmissible_evenPair (by decide : Even 1144)

theorem isAdmissible_evenPair_oneThousandOneHundredFortySix : IsAdmissible (evenPair 1146) :=
  isAdmissible_evenPair (by decide : Even 1146)

theorem isAdmissible_evenPair_oneThousandOneHundredFortyEight : IsAdmissible (evenPair 1148) :=
  isAdmissible_evenPair (by decide : Even 1148)

theorem isAdmissible_evenPair_oneThousandOneHundredFifty : IsAdmissible (evenPair 1150) :=
  isAdmissible_evenPair (by decide : Even 1150)

theorem singular_series_pos_evenPair_oneThousandOneHundredFortyTwo : 0 < singularSeries (evenPair 1142) :=
  singular_series_pos_evenPair (by decide : Even 1142)

theorem singular_series_pos_evenPair_oneThousandOneHundredFortyFour : 0 < singularSeries (evenPair 1144) :=
  singular_series_pos_evenPair (by decide : Even 1144)

theorem singular_series_pos_evenPair_oneThousandOneHundredFortySix : 0 < singularSeries (evenPair 1146) :=
  singular_series_pos_evenPair (by decide : Even 1146)

theorem singular_series_pos_evenPair_oneThousandOneHundredFortyEight : 0 < singularSeries (evenPair 1148) :=
  singular_series_pos_evenPair (by decide : Even 1148)

theorem singular_series_pos_evenPair_oneThousandOneHundredFifty : 0 < singularSeries (evenPair 1150) :=
  singular_series_pos_evenPair (by decide : Even 1150)

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1142) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1142) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1144) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1144) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1146) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1146) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1148) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1148) P

theorem singular_series_finite_pos_evenPair_oneThousandOneHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1150) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1150) P

theorem nu_p_oneThousandOneHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1142) p = if p = 2 ∨ p ∣ 1142 then 1 else 2 :=
  nu_p_evenPair (by decide : (1142 : ℕ) ≠ 0) (by decide : Even 1142) hp

theorem nu_p_oneThousandOneHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1144) p = if p = 2 ∨ p ∣ 1144 then 1 else 2 :=
  nu_p_evenPair (by decide : (1144 : ℕ) ≠ 0) (by decide : Even 1144) hp

theorem nu_p_oneThousandOneHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1146) p = if p = 2 ∨ p ∣ 1146 then 1 else 2 :=
  nu_p_evenPair (by decide : (1146 : ℕ) ≠ 0) (by decide : Even 1146) hp

theorem nu_p_oneThousandOneHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1148) p = if p = 2 ∨ p ∣ 1148 then 1 else 2 :=
  nu_p_evenPair (by decide : (1148 : ℕ) ≠ 0) (by decide : Even 1148) hp

theorem nu_p_oneThousandOneHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1150) p = if p = 2 ∨ p ∣ 1150 then 1 else 2 :=
  nu_p_evenPair (by decide : (1150 : ℕ) ≠ 0) (by decide : Even 1150) hp

theorem nu_p_oneThousandOneHundredFortyTwo_two : nu_p (evenPair 1142) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1142)

theorem localFactor_oneThousandOneHundredFortyTwo_two : localFactor (evenPair 1142) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1142 : ℕ) ≠ 0) (by decide : Even 1142)

theorem nu_p_oneThousandOneHundredFifty_two : nu_p (evenPair 1150) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1150)

theorem localFactor_oneThousandOneHundredFifty_two : localFactor (evenPair 1150) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1150 : ℕ) ≠ 0) (by decide : Even 1150)

end Brockian.SingularSeries.Gaps11421150
