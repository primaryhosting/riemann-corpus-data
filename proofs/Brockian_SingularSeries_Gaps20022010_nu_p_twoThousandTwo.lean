/-
  Brockian/SingularSeriesGaps20022010.lean — even binary gaps n ∈ {2002, 2004, 2006, 2008, 2010}.

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

namespace Brockian.SingularSeries.Gaps20022010

private instance fact_prime_two : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem evenPair_card_twoThousandTwo : (evenPair 2002).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2002 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandFour : (evenPair 2004).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2004 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandSix : (evenPair 2006).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2006 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandEight : (evenPair 2008).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2008 : ℕ) ≠ 0)

theorem evenPair_card_twoThousandTen : (evenPair 2010).card = 2 :=
  evenPair_card_of_ne_zero (by decide : (2010 : ℕ) ≠ 0)

theorem isAdmissible_evenPair_twoThousandTwo : IsAdmissible (evenPair 2002) :=
  isAdmissible_evenPair (by decide : Even 2002)

theorem isAdmissible_evenPair_twoThousandFour : IsAdmissible (evenPair 2004) :=
  isAdmissible_evenPair (by decide : Even 2004)

theorem isAdmissible_evenPair_twoThousandSix : IsAdmissible (evenPair 2006) :=
  isAdmissible_evenPair (by decide : Even 2006)

theorem isAdmissible_evenPair_twoThousandEight : IsAdmissible (evenPair 2008) :=
  isAdmissible_evenPair (by decide : Even 2008)

theorem isAdmissible_evenPair_twoThousandTen : IsAdmissible (evenPair 2010) :=
  isAdmissible_evenPair (by decide : Even 2010)

theorem singular_series_pos_evenPair_twoThousandTwo : 0 < singularSeries (evenPair 2002) :=
  singular_series_pos_evenPair (by decide : Even 2002)

theorem singular_series_pos_evenPair_twoThousandFour : 0 < singularSeries (evenPair 2004) :=
  singular_series_pos_evenPair (by decide : Even 2004)

theorem singular_series_pos_evenPair_twoThousandSix : 0 < singularSeries (evenPair 2006) :=
  singular_series_pos_evenPair (by decide : Even 2006)

theorem singular_series_pos_evenPair_twoThousandEight : 0 < singularSeries (evenPair 2008) :=
  singular_series_pos_evenPair (by decide : Even 2008)

theorem singular_series_pos_evenPair_twoThousandTen : 0 < singularSeries (evenPair 2010) :=
  singular_series_pos_evenPair (by decide : Even 2010)

theorem singular_series_finite_pos_evenPair_twoThousandTwo (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2002) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2002) P

theorem singular_series_finite_pos_evenPair_twoThousandFour (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2004) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2004) P

theorem singular_series_finite_pos_evenPair_twoThousandSix (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2006) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2006) P

theorem singular_series_finite_pos_evenPair_twoThousandEight (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2008) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2008) P

theorem singular_series_finite_pos_evenPair_twoThousandTen (P : ℕ) :
    0 < singularSeriesFinite (evenPair 2010) P :=
  singular_series_finite_pos_evenPair (by decide : Even 2010) P

theorem nu_p_twoThousandTwo (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2002) p = if p = 2 ∨ p ∣ 2002 then 1 else 2 :=
  nu_p_evenPair (by decide : (2002 : ℕ) ≠ 0) (by decide : Even 2002) hp

theorem nu_p_twoThousandFour (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2004) p = if p = 2 ∨ p ∣ 2004 then 1 else 2 :=
  nu_p_evenPair (by decide : (2004 : ℕ) ≠ 0) (by decide : Even 2004) hp

theorem nu_p_twoThousandSix (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2006) p = if p = 2 ∨ p ∣ 2006 then 1 else 2 :=
  nu_p_evenPair (by decide : (2006 : ℕ) ≠ 0) (by decide : Even 2006) hp

theorem nu_p_twoThousandEight (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2008) p = if p = 2 ∨ p ∣ 2008 then 1 else 2 :=
  nu_p_evenPair (by decide : (2008 : ℕ) ≠ 0) (by decide : Even 2008) hp

theorem nu_p_twoThousandTen (p : ℕ) (hp : Nat.Prime p) :
    nu_p (evenPair 2010) p = if p = 2 ∨ p ∣ 2010 then 1 else 2 :=
  nu_p_evenPair (by decide : (2010 : ℕ) ≠ 0) (by decide : Even 2010) hp

theorem nu_p_twoThousandTwo_two : nu_p (evenPair 2002) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2002)

theorem localFactor_twoThousandTwo_two : localFactor (evenPair 2002) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2002 : ℕ) ≠ 0) (by decide : Even 2002)

theorem nu_p_twoThousandTen_two : nu_p (evenPair 2010) 2 = 1 :=
  nu_p_evenPair_two (by decide : Even 2010)

theorem localFactor_twoThousandTen_two : localFactor (evenPair 2010) 2 = 2 :=
  localFactor_evenPair_two (by decide : (2010 : ℕ) ≠ 0) (by decide : Even 2010)

end Brockian.SingularSeries.Gaps20022010
