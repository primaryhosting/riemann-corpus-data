/-
  Brockian/SingularSeriesGaps712720.lean — even binary gaps n ∈ {712, 714, 716, 718, 720}.

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

namespace Brockian.SingularSeries.Gaps712720

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_sevenHundredTwelve : (evenPair 712).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (712 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredFourteen : (evenPair 714).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (714 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredSixteen : (evenPair 716).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (716 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredEighteen : (evenPair 718).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (718 : ℕ) ≠ 0)

theorem evenPair_card_sevenHundredTwenty : (evenPair 720).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (720 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_sevenHundredTwelve : IsAdmissible (evenPair 712) :=
  isAdmissible_evenPair (by decide : Even 712)

theorem isAdmissible_evenPair_sevenHundredFourteen : IsAdmissible (evenPair 714) :=
  isAdmissible_evenPair (by decide : Even 714)

theorem isAdmissible_evenPair_sevenHundredSixteen : IsAdmissible (evenPair 716) :=
  isAdmissible_evenPair (by decide : Even 716)

theorem isAdmissible_evenPair_sevenHundredEighteen : IsAdmissible (evenPair 718) :=
  isAdmissible_evenPair (by decide : Even 718)

theorem isAdmissible_evenPair_sevenHundredTwenty : IsAdmissible (evenPair 720) :=
  isAdmissible_evenPair (by decide : Even 720)

theorem singular_series_pos_evenPair_sevenHundredTwelve : 0 < singularSeries (evenPair 712) :=
  singular_series_pos_evenPair (by decide : Even 712)

theorem singular_series_pos_evenPair_sevenHundredFourteen : 0 < singularSeries (evenPair 714) :=
  singular_series_pos_evenPair (by decide : Even 714)

theorem singular_series_pos_evenPair_sevenHundredSixteen : 0 < singularSeries (evenPair 716) :=
  singular_series_pos_evenPair (by decide : Even 716)

theorem singular_series_pos_evenPair_sevenHundredEighteen : 0 < singularSeries (evenPair 718) :=
  singular_series_pos_evenPair (by decide : Even 718)

theorem singular_series_pos_evenPair_sevenHundredTwenty : 0 < singularSeries (evenPair 720) :=
  singular_series_pos_evenPair (by decide : Even 720)

theorem singular_series_finite_pos_evenPair_sevenHundredTwelve (P : ℕ) :
    0 < singularSeriesFinite (evenPair 712) P :=
  singular_series_finite_pos_evenPair (by decide : Even 712) P

theorem singular_series_finite_pos_evenPair_sevenHundredFourteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 714) P :=
  singular_series_finite_pos_evenPair (by decide : Even 714) P

theorem singular_series_finite_pos_evenPair_sevenHundredSixteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 716) P :=
  singular_series_finite_pos_evenPair (by decide : Even 716) P

theorem singular_series_finite_pos_evenPair_sevenHundredEighteen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 718) P :=
  singular_series_finite_pos_evenPair (by decide : Even 718) P

theorem singular_series_finite_pos_evenPair_sevenHundredTwenty (P : ℕ) :
    0 < singularSeriesFinite (evenPair 720) P :=
  singular_series_finite_pos_evenPair (by decide : Even 720) P

theorem nu_p_sevenHundredTwelve (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 712) p = if p = 2 ∨ p ∣ 712 then 1 else 2 :=
  nu_p_evenPair (by decide : (712 : ℕ) ≠ 0) (by decide : Even 712) hp

theorem nu_p_sevenHundredFourteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 714) p = if p = 2 ∨ p ∣ 714 then 1 else 2 :=
  nu_p_evenPair (by decide : (714 : ℕ) ≠ 0) (by decide : Even 714) hp

theorem nu_p_sevenHundredSixteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 716) p = if p = 2 ∨ p ∣ 716 then 1 else 2 :=
  nu_p_evenPair (by decide : (716 : ℕ) ≠ 0) (by decide : Even 716) hp

theorem nu_p_sevenHundredEighteen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 718) p = if p = 2 ∨ p ∣ 718 then 1 else 2 :=
  nu_p_evenPair (by decide : (718 : ℕ) ≠ 0) (by decide : Even 718) hp

theorem nu_p_sevenHundredTwenty (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 720) p = if p = 2 ∨ p ∣ 720 then 1 else 2 :=
  nu_p_evenPair (by decide : (720 : ℕ) ≠ 0) (by decide : Even 720) hp

theorem nu_p_sevenHundredTwelve_two : nu_p (evenPair 712) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 712)

theorem localFactor_sevenHundredTwelve_two : localFactor (evenPair 712) 2 = 2 :=
  localFactor_evenPair_two (by decide : (712 : ℕ) ≠ 0) (by decide : Even 712)

theorem nu_p_sevenHundredTwenty_two : nu_p (evenPair 720) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 720)

theorem localFactor_sevenHundredTwenty_two : localFactor (evenPair 720) 2 = 2 :=
  localFactor_evenPair_two (by decide : (720 : ℕ) ≠ 0) (by decide : Even 720)

end Brockian.SingularSeries.Gaps712720
