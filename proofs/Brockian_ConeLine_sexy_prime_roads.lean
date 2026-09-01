/-
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- A prime `q` greater than `5` is not divisible by `5`. -/
lemma not_five_dvd_of_prime_gt_five {q : ℕ} (hq : q.Prime) (h : 5 < q) : q % 5 ≠ 0 := by
  intro h0
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h0
  rcases hq.eq_one_or_self_of_dvd 5 hdvd with h1 | h1 <;> omega

/-- **Sexy prime roads.** If `p` and `p + 6` are both prime and `p > 5`, then the pair of
residues `(p % 5, (p + 6) % 5)` is one of `(1, 2)`, `(2, 3)`, `(3, 4)`; in particular
`p + 6 ≡ p + 1 [MOD 5]` and neither endpoint lies on the ray `0`. -/
theorem sexy_prime_roads {p : ℕ} (hp : p.Prime) (hq : (p + 6).Prime) (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have h1 : p % 5 ≠ 0 := not_five_dvd_of_prime_gt_five hp h5
  have h2 : (p + 6) % 5 ≠ 0 := not_five_dvd_of_prime_gt_five hq (by omega)
  have h3 : p % 5 = 1 ∧ (p + 6) % 5 = 2 ∨ p % 5 = 2 ∧ (p + 6) % 5 = 3 ∨
      p % 5 = 3 ∧ (p + 6) % 5 = 4 := by omega
  rcases h3 with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b]

end Brockian.ConeLine

