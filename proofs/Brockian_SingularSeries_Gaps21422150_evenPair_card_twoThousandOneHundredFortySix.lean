/-
  Brockian/SingularSeriesGaps21422150.lean — even binary gaps n ∈ {2142, 2144, 2146, 2148, 2150}.

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

namespace Brockian.SingularSeries.Gaps21422150

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandOneHundredFortyTwo : (evenPair 2142).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2142 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredFortyFour : (evenPair 2144).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2144 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredFortySix : (evenPair 2146).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2146 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredFortyEight : (evenPair 2148).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2148 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredFifty : (evenPair 2150).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2150 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandOneHundredFortyTwo : IsAdmissible (evenPair 2142) :=
  isAdmissible_evenPair (by decide : Even 2142)

theorem isAdmissible_evenPair_twoThousandOneHundredFortyFour : IsAdmissible (evenPair 2144) :=
  isAdmissible_evenPair (by decide : Even 2144)

theorem isAdmissible_evenPair_twoThousandOneHundredFortySix : IsAdmissible (evenPair 2146) :=
  isAdmissible_evenPair (by decide : Even 2146)

theorem isAdmissible_evenPair_twoThousandOneHundredFortyEight : IsAdmissible (evenPair 2148) :=
  isAdmissible_evenPair (by decide : Even 2148)

theorem isAdmissible_evenPair_twoThousandOneHundredFifty : IsAdmissible (evenPair 2150) :=
  isAdmissible_evenPair (by decide : Even 2150)

theorem singular_series_pos_evenPair_twoThousandOneHundredFortyTwo : 0 < singularSeries (evenPair 2142) :=
  singular_series_pos_evenPair (by decide : Even 2142)

theorem singular_series_pos_evenPair_twoThousandOneHundredFortyFour : 0 < singularSeries (evenPair 2144) :=
  singular_series_pos_evenPair (by decide : Even 2144)

theorem singular_series_pos_evenPair_twoThousandOneHundredFortySix : 0 < singularSeries (evenPair 2146) :=
  singular_series_pos_evenPair (by decide : Even 2146)

theorem singular_series_pos_evenPair_twoThousandOneHundredFortyEight : 0 < singularSeries (evenPair 2148) :=
  singular_series_pos_evenPair (by decide : Even 2148)

theorem singular_series_pos_evenPair_twoThousandOneHundredFifty : 0 < singularSeries (evenPair 2150) :=
  singular_series_pos_evenPair (by decide : Even 2150)

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFortyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2142) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2142) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFortyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2144) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2144) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFortySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2146) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2146) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFortyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2148) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2148) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFifty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2150) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2150) P

theorem nu_p_twoThousandOneHundredFortyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2142) p = if p = 2 ∨ p ∣ 2142 then 1 else 2 :=
  nu_p_evenPair (by decide : (2142 : ℕ) ≠ 0) (by decide : Even 2142) hp

theorem nu_p_twoThousandOneHundredFortyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2144) p = if p = 2 ∨ p ∣ 2144 then 1 else 2 :=
  nu_p_evenPair (by decide : (2144 : ℕ) ≠ 0) (by decide : Even 2144) hp

theorem nu_p_twoThousandOneHundredFortySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2146) p = if p = 2 ∨ p ∣ 2146 then 1 else 2 :=
  nu_p_evenPair (by decide : (2146 : ℕ) ≠ 0) (by decide : Even 2146) hp

theorem nu_p_twoThousandOneHundredFortyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2148) p = if p = 2 ∨ p ∣ 2148 then 1 else 2 :=
  nu_p_evenPair (by decide : (2148 : ℕ) ≠ 0) (by decide : Even 2148) hp

theorem nu_p_twoThousandOneHundredFifty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2150) p = if p = 2 ∨ p ∣ 2150 then 1 else 2 :=
  nu_p_evenPair (by decide : (2150 : ℕ) ≠ 0) (by decide : Even 2150) hp

theorem nu_p_twoThousandOneHundredFortyTwo_two : nu_p (evenPair 2142) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2142)

theorem localFactor_twoThousandOneHundredFortyTwo_two : localFactor (evenPair 2142) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2142 : ℕ) ≠ 0) (by decide : Even 2142)

theorem nu_p_twoThousandOneHundredFifty_two : nu_p (evenPair 2150) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2150)

theorem localFactor_twoThousandOneHundredFifty_two : localFactor (evenPair 2150) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2150 : ℕ) ≠ 0) (by decide : Even 2150)

end Brockian.SingularSeries.Gaps21422150
