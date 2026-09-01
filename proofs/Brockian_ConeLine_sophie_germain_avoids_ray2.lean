/-
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`. -/
theorem not_five_dvd_of_prime_gt_five {q : ℕ} (hq : q.Prime) (h5 : 5 < q) : ¬ (5 ∣ q) := by
  intro hdvd
  have := (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd)
  omega

/-- A Sophie Germain prime `p > 5` never sits on ray 2 (`p % 5 ≠ 2`), and the pair of
residues `(p % 5, (2p+1) % 5)` is one of `(1,3)`, `(3,2)`, `(4,4)`. -/
theorem sophie_germain_avoids_ray2 {p : ℕ} (hp : p.Prime) (hq : (2 * p + 1).Prime)
    (h5 : 5 < p) :
    p % 5 ≠ 2 ∧
      ((p % 5, (2 * p + 1) % 5) = (1, 3) ∨ (p % 5, (2 * p + 1) % 5) = (3, 2) ∨
        (p % 5, (2 * p + 1) % 5) = (4, 4)) := by
  have hpd : ¬ (5 ∣ p) := not_five_dvd_of_prime_gt_five hp h5
  have hqd : ¬ (5 ∣ 2 * p + 1) := not_five_dvd_of_prime_gt_five hq (by omega)
  rw [Nat.dvd_iff_mod_eq_zero] at hpd hqd
  refine ⟨by omega, ?_⟩
  have h1 : p % 5 = 1 ∨ p % 5 = 3 ∨ p % 5 = 4 := by omega
  simp only [Prod.mk.injEq]
  rcases h1 with h | h | h
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr (Or.inl ⟨h, by omega⟩)
  · exact Or.inr (Or.inr ⟨h, by omega⟩)

end Brockian.ConeLine

