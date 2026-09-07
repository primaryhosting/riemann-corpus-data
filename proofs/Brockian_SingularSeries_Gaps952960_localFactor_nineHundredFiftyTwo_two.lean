/-
  Brockian/SingularSeriesGaps952960.lean — even binary gaps n ∈ {952, 954, 956, 958, 960}.

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

namespace Brockian.SingularSeries.Gaps952960

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_nineHundredFiftyTwo : (evenPair 952).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (952 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredFiftyFour : (evenPair 954).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (954 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredFiftySix : (evenPair 956).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (956 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredFiftyEight : (evenPair 958).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (958 : ℕ) ≠ 0)

theorem evenPair_card_nineHundredSixty : (evenPair 960).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (960 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_nineHundredFiftyTwo : IsAdmissible (evenPair 952) :=
  isAdmissible_evenPair (by decide : Even 952)

theorem isAdmissible_evenPair_nineHundredFiftyFour : IsAdmissible (evenPair 954) :=
  isAdmissible_evenPair (by decide : Even 954)

theorem isAdmissible_evenPair_nineHundredFiftySix : IsAdmissible (evenPair 956) :=
  isAdmissible_evenPair (by decide : Even 956)

theorem isAdmissible_evenPair_nineHundredFiftyEight : IsAdmissible (evenPair 958) :=
  isAdmissible_evenPair (by decide : Even 958)

theorem isAdmissible_evenPair_nineHundredSixty : IsAdmissible (evenPair 960) :=
  isAdmissible_evenPair (by decide : Even 960)

theorem singular_series_pos_evenPair_nineHundredFiftyTwo : 0 < singularSeries (evenPair 952) :=
  singular_series_pos_evenPair (by decide : Even 952)

theorem singular_series_pos_evenPair_nineHundredFiftyFour : 0 < singularSeries (evenPair 954) :=
  singular_series_pos_evenPair (by decide : Even 954)

theorem singular_series_pos_evenPair_nineHundredFiftySix : 0 < singularSeries (evenPair 956) :=
  singular_series_pos_evenPair (by decide : Even 956)

theorem singular_series_pos_evenPair_nineHundredFiftyEight : 0 < singularSeries (evenPair 958) :=
  singular_series_pos_evenPair (by decide : Even 958)

theorem singular_series_pos_evenPair_nineHundredSixty : 0 < singularSeries (evenPair 960) :=
  singular_series_pos_evenPair (by decide : Even 960)

theorem singular_series_finite_pos_evenPair_nineHundredFiftyTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 952) P :=
  singular_series_finite_pos_evenPair (by decide : Even 952) P

theorem singular_series_finite_pos_evenPair_nineHundredFiftyFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 954) P :=
  singular_series_finite_pos_evenPair (by decide : Even 954) P

theorem singular_series_finite_pos_evenPair_nineHundredFiftySix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 956) P :=
  singular_series_finite_pos_evenPair (by decide : Even 956) P

theorem singular_series_finite_pos_evenPair_nineHundredFiftyEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 958) P :=
  singular_series_finite_pos_evenPair (by decide : Even 958) P

theorem singular_series_finite_pos_evenPair_nineHundredSixty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 960) P :=
  singular_series_finite_pos_evenPair (by decide : Even 960) P

theorem nu_p_nineHundredFiftyTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 952) p = if p = 2 ∨ p ∣ 952 then 1 else 2 :=
  nu_p_evenPair (by decide : (952 : ℕ) ≠ 0) (by decide : Even 952) hp

theorem nu_p_nineHundredFiftyFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 954) p = if p = 2 ∨ p ∣ 954 then 1 else 2 :=
  nu_p_evenPair (by decide : (954 : ℕ) ≠ 0) (by decide : Even 954) hp

theorem nu_p_nineHundredFiftySix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 956) p = if p = 2 ∨ p ∣ 956 then 1 else 2 :=
  nu_p_evenPair (by decide : (956 : ℕ) ≠ 0) (by decide : Even 956) hp

theorem nu_p_nineHundredFiftyEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 958) p = if p = 2 ∨ p ∣ 958 then 1 else 2 :=
  nu_p_evenPair (by decide : (958 : ℕ) ≠ 0) (by decide : Even 958) hp

theorem nu_p_nineHundredSixty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 960) p = if p = 2 ∨ p ∣ 960 then 1 else 2 :=
  nu_p_evenPair (by decide : (960 : ℕ) ≠ 0) (by decide : Even 960) hp

theorem nu_p_nineHundredFiftyTwo_two : nu_p (evenPair 952) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 952)

theorem localFactor_nineHundredFiftyTwo_two : localFactor (evenPair 952) 2 = 2 :=
  localFactor_evenPair_two (by decide : (952 : ℕ) ≠ 0) (by decide : Even 952)

theorem nu_p_nineHundredSixty_two : nu_p (evenPair 960) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 960)

theorem localFactor_nineHundredSixty_two : localFactor (evenPair 960) 2 = 2 :=
  localFactor_evenPair_two (by decide : (960 : ℕ) ≠ 0) (by decide : Even 960)

end Brockian.SingularSeries.Gaps952960
