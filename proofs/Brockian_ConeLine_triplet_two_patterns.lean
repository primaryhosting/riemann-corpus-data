import Mathlib

/-!
# Triplet Two Patterns
Category: Cone Line
Target: Brockian.ConeLine.triplet_two_patterns
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.ConeLine

/-- A prime `q` greater than `5` is not divisible by `5`, i.e. `q % 5 ≠ 0`. -/
lemma mod_five_ne_zero_of_prime {q : ℕ} (hq : q.Prime) (hq5 : 5 < q) : q % 5 ≠ 0 := by
  intro h
  rcases hq.eq_one_or_self_of_dvd 5 (Nat.dvd_iff_mod_eq_zero.mpr h) with h1 | h2
  · omega
  · omega

/-- A prime triplet `(p, p+2, p+6)` with `p > 5` has exactly two possible ray
patterns modulo `5`: `(1, 3, 2)` or `(2, 4, 3)`. -/
theorem triplet_two_patterns {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime)
    (hp6 : (p + 6).Prime) (h5 : 5 < p) :
    (p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2) ∨
      (p % 5 = 2 ∧ (p + 2) % 5 = 4 ∧ (p + 6) % 5 = 3) := by
  have h0 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime hp h5
  have h2 : (p + 2) % 5 ≠ 0 := mod_five_ne_zero_of_prime hp2 (by omega)
  have h6 : (p + 6) % 5 ≠ 0 := mod_five_ne_zero_of_prime hp6 (by omega)
  omega

end Brockian.ConeLine

