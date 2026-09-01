import Mathlib

/-!
# Square Ray Primes Mod 20
Category: Cone Line
Target: Brockian.ConeLine.square_ray_primes_mod20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- A prime `p > 5` with `p ≡ 1` or `4 (mod 5)` satisfies `p % 20 ∈ {1, 9, 11, 19}`.

The proof uses `Nat.Prime.odd_of_ne_two` (Mathlib) to get `p % 2 = 1`, after which
`omega` handles the arithmetic combining the residues mod 2 and mod 5 into mod 20. -/
theorem square_ray_primes_mod20 (p : ℕ) (hp : p.Prime) (h5 : 5 < p)
    (h : p % 5 = 1 ∨ p % 5 = 4) :
    p % 20 = 1 ∨ p % 20 = 9 ∨ p % 20 = 11 ∨ p % 20 = 19 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  omega

end Brockian.ConeLine

