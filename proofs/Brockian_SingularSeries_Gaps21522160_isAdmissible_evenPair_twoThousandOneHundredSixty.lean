/-
  Brockian/SingularSeriesGaps21522160.lean — even binary gaps n ∈ {2152, 2154, 2156, 2158, 2160}.

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

namespace Brockian.SingularSeries.Gaps21522160

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandOneHundredFiftyTwo : (evenPair 2152).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2152 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredFiftyFour : (evenPair 2154).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2154 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredFiftySix : (evenPair 2156).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2156 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredFiftyEight : (evenPair 2158).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2158 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandOneHundredSixty : (evenPair 2160).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2160 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandOneHundredFiftyTwo : IsAdmissible (evenPair 2152) :=
  isAdmissible_evenPair (by decide : Even 2152)

theorem isAdmissible_evenPair_twoThousandOneHundredFiftyFour : IsAdmissible (evenPair 2154) :=
  isAdmissible_evenPair (by decide : Even 2154)

theorem isAdmissible_evenPair_twoThousandOneHundredFiftySix : IsAdmissible (evenPair 2156) :=
  isAdmissible_evenPair (by decide : Even 2156)

theorem isAdmissible_evenPair_twoThousandOneHundredFiftyEight : IsAdmissible (evenPair 2158) :=
  isAdmissible_evenPair (by decide : Even 2158)

theorem isAdmissible_evenPair_twoThousandOneHundredSixty : IsAdmissible (evenPair 2160) :=
  isAdmissible_evenPair (by decide : Even 2160)

theorem singular_series_pos_evenPair_twoThousandOneHundredFiftyTwo : 0 < singularSeries (evenPair 2152) :=
  singular_series_pos_evenPair (by decide : Even 2152)

theorem singular_series_pos_evenPair_twoThousandOneHundredFiftyFour : 0 < singularSeries (evenPair 2154) :=
  singular_series_pos_evenPair (by decide : Even 2154)

theorem singular_series_pos_evenPair_twoThousandOneHundredFiftySix : 0 < singularSeries (evenPair 2156) :=
  singular_series_pos_evenPair (by decide : Even 2156)

theorem singular_series_pos_evenPair_twoThousandOneHundredFiftyEight : 0 < singularSeries (evenPair 2158) :=
  singular_series_pos_evenPair (by decide : Even 2158)

theorem singular_series_pos_evenPair_twoThousandOneHundredSixty : 0 < singularSeries (evenPair 2160) :=
  singular_series_pos_evenPair (by decide : Even 2160)

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2152) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2152) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2154) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2154) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2156) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2156) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2158) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2158) P

theorem singular_series_finite_pos_evenPair_twoThousandOneHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2160) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2160) P

theorem nu_p_twoThousandOneHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2152) p = if p = 2 ∨ p ∣ 2152 then 1 else 2 :=
  nu_p_evenPair (by decide : (2152 : ℕ) ≠ 0) (by decide : Even 2152) hp

theorem nu_p_twoThousandOneHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2154) p = if p = 2 ∨ p ∣ 2154 then 1 else 2 :=
  nu_p_evenPair (by decide : (2154 : ℕ) ≠ 0) (by decide : Even 2154) hp

theorem nu_p_twoThousandOneHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2156) p = if p = 2 ∨ p ∣ 2156 then 1 else 2 :=
  nu_p_evenPair (by decide : (2156 : ℕ) ≠ 0) (by decide : Even 2156) hp

theorem nu_p_twoThousandOneHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2158) p = if p = 2 ∨ p ∣ 2158 then 1 else 2 :=
  nu_p_evenPair (by decide : (2158 : ℕ) ≠ 0) (by decide : Even 2158) hp

theorem nu_p_twoThousandOneHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2160) p = if p = 2 ∨ p ∣ 2160 then 1 else 2 :=
  nu_p_evenPair (by decide : (2160 : ℕ) ≠ 0) (by decide : Even 2160) hp

theorem nu_p_twoThousandOneHundredFiftyTwo_two : nu_p (evenPair 2152) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2152)

theorem localFactor_twoThousandOneHundredFiftyTwo_two : localFactor (evenPair 2152) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2152 : ℕ) ≠ 0) (by decide : Even 2152)

theorem nu_p_twoThousandOneHundredSixty_two : nu_p (evenPair 2160) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2160)

theorem localFactor_twoThousandOneHundredSixty_two : localFactor (evenPair 2160) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2160 : ℕ) ≠ 0) (by decide : Even 2160)

end Brockian.SingularSeries.Gaps21522160
