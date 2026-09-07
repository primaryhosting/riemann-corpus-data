/-
  Brockian/SingularSeriesGaps19521960.lean — even binary gaps n ∈ {1952, 1954, 1956, 1958, 1960}.

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

namespace Brockian.SingularSeries.Gaps19521960

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_oneThousandNineHundredFiftyTwo : (evenPair 1952).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1952 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredFiftyFour : (evenPair 1954).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1954 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredFiftySix : (evenPair 1956).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1956 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredFiftyEight : (evenPair 1958).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1958 : ℕ) ≠ 0)

theorem evenPair_card_oneThousandNineHundredSixty : (evenPair 1960).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (1960 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_oneThousandNineHundredFiftyTwo : IsAdmissible (evenPair 1952) :=
  isAdmissible_evenPair (by decide : Even 1952)

theorem isAdmissible_evenPair_oneThousandNineHundredFiftyFour : IsAdmissible (evenPair 1954) :=
  isAdmissible_evenPair (by decide : Even 1954)

theorem isAdmissible_evenPair_oneThousandNineHundredFiftySix : IsAdmissible (evenPair 1956) :=
  isAdmissible_evenPair (by decide : Even 1956)

theorem isAdmissible_evenPair_oneThousandNineHundredFiftyEight : IsAdmissible (evenPair 1958) :=
  isAdmissible_evenPair (by decide : Even 1958)

theorem isAdmissible_evenPair_oneThousandNineHundredSixty : IsAdmissible (evenPair 1960) :=
  isAdmissible_evenPair (by decide : Even 1960)

theorem singular_series_pos_evenPair_oneThousandNineHundredFiftyTwo : 0 < singularSeries (evenPair 1952) :=
  singular_series_pos_evenPair (by decide : Even 1952)

theorem singular_series_pos_evenPair_oneThousandNineHundredFiftyFour : 0 < singularSeries (evenPair 1954) :=
  singular_series_pos_evenPair (by decide : Even 1954)

theorem singular_series_pos_evenPair_oneThousandNineHundredFiftySix : 0 < singularSeries (evenPair 1956) :=
  singular_series_pos_evenPair (by decide : Even 1956)

theorem singular_series_pos_evenPair_oneThousandNineHundredFiftyEight : 0 < singularSeries (evenPair 1958) :=
  singular_series_pos_evenPair (by decide : Even 1958)

theorem singular_series_pos_evenPair_oneThousandNineHundredSixty : 0 < singularSeries (evenPair 1960) :=
  singular_series_pos_evenPair (by decide : Even 1960)

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1952) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1952) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1954) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1954) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1956) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1956) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1958) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1958) P

theorem singular_series_finite_pos_evenPair_oneThousandNineHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 1960) P :=
  singular_series_finite_pos_evenPair (by decide : Even 1960) P

theorem nu_p_oneThousandNineHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1952) p = if p = 2 ∨ p ∣ 1952 then 1 else 2 :=
  nu_p_evenPair (by decide : (1952 : ℕ) ≠ 0) (by decide : Even 1952) hp

theorem nu_p_oneThousandNineHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1954) p = if p = 2 ∨ p ∣ 1954 then 1 else 2 :=
  nu_p_evenPair (by decide : (1954 : ℕ) ≠ 0) (by decide : Even 1954) hp

theorem nu_p_oneThousandNineHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1956) p = if p = 2 ∨ p ∣ 1956 then 1 else 2 :=
  nu_p_evenPair (by decide : (1956 : ℕ) ≠ 0) (by decide : Even 1956) hp

theorem nu_p_oneThousandNineHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1958) p = if p = 2 ∨ p ∣ 1958 then 1 else 2 :=
  nu_p_evenPair (by decide : (1958 : ℕ) ≠ 0) (by decide : Even 1958) hp

theorem nu_p_oneThousandNineHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 1960) p = if p = 2 ∨ p ∣ 1960 then 1 else 2 :=
  nu_p_evenPair (by decide : (1960 : ℕ) ≠ 0) (by decide : Even 1960) hp

theorem nu_p_oneThousandNineHundredFiftyTwo_two : nu_p (evenPair 1952) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1952)

theorem localFactor_oneThousandNineHundredFiftyTwo_two : localFactor (evenPair 1952) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1952 : ℕ) ≠ 0) (by decide : Even 1952)

theorem nu_p_oneThousandNineHundredSixty_two : nu_p (evenPair 1960) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 1960)

theorem localFactor_oneThousandNineHundredSixty_two : localFactor (evenPair 1960) 2 = 2 :=
  localFactor_evenPair_two (by decide : (1960 : ℕ) ≠ 0) (by decide : Even 1960)

end Brockian.SingularSeries.Gaps19521960
