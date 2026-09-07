import Mathlib
import Brockian.SingularSeries
import Brockian.SingularSeriesExamples
import Brockian.SingularSeriesMoreExamples

/-!
# Singular-series bridge: the twin local factor in Hardy–Littlewood closed form

The constellation-sieve confinement counts `p − ν_p` are the *admissibility* side of the classical
Hardy–Littlewood singular series

  `𝔖(H) = ∏_p (1 − ν_p/p) · (1 − 1/p)^{−k}`,   `k = |H|`,

which is exactly this repository's `Brockian.SingularSeries.localFactor`.  This module records the
**twin** pattern `{0,2}` local factor in the standard closed form number theorists write, tying our
verified objects to the literature (Hardy–Littlewood; Maynard–Tao admissible tuples):

* odd primes `p ≠ 2`:  `localFactor {0,2} p = (p − 2)·p / (p − 1)²`;
* `p = 2`:            `localFactor {0,2} 2 = 2`  (re-exported from `MoreExamples`).

Everything here is finite/algebraic.  It says **nothing** about the infinitude of twin primes — by
the parity problem of sieve theory (Tao, 2007) the admissibility/singular-series data alone cannot
cross to a lower bound on primes.
-/

namespace Brockian.SingularSeriesBridge

open Brockian.SingularSeries Brockian.SingularSeries.Examples Brockian.SingularSeries.MoreExamples

/-- **Twin odd-prime local factor, Hardy–Littlewood closed form.**
For an odd prime `p`, `localFactor {0,2} p = (1 − 2/p)/(1 − 1/p)² = (p − 2)·p/(p − 1)²`. -/
theorem localFactor_twinGap_odd (p : ℕ) [Fact (Nat.Prime p)] (h2 : p ≠ 2) :
    localFactor twinGap p = ((p : ℝ) - 2) * (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have hp : Nat.Prime p := Fact.out
  have hppos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt hppos
  have hlt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpm1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hlt1)
  have hdiv : ¬ p ∣ 2 := by
    intro h
    rcases (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h with rfl
    exact h2 rfl
  have hnu : nu_p twinGap p = 2 :=
    nu_p_evenPair_odd_of_not_dvd (by decide) hp h2 hdiv
  have hcard : twinGap.card = 2 := evenPair_card_of_ne_zero (by decide)
  unfold localFactor
  rw [hnu, hcard]
  field_simp
  ring

/-- The twin odd-prime local factor is strictly positive (`p ≥ 3`), the pointwise input to
singular-series positivity `singular_series_pos_twinGap`. -/
theorem localFactor_twinGap_odd_pos (p : ℕ) [Fact (Nat.Prime p)] (h2 : p ≠ 2) :
    0 < localFactor twinGap p := by
  have hp : Nat.Prime p := Fact.out
  have hppos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have h2r : (2 : ℝ) < (p : ℝ) := by
    have : 2 < p := lt_of_le_of_ne hp.two_le (fun h => h2 h.symm)
    exact_mod_cast this
  rw [localFactor_twinGap_odd p h2]
  have hnum : 0 < ((p : ℝ) - 2) * (p : ℝ) := mul_pos (by linarith) hppos
  have hden : 0 < ((p : ℝ) - 1) ^ 2 := by
    have : 0 < (p : ℝ) - 1 := by linarith
    positivity
  exact div_pos hnum hden

end Brockian.SingularSeriesBridge
