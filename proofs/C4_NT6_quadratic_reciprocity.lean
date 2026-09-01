import Mathlib
namespace C4.NT6

/-- Quadratic reciprocity for distinct odd primes: this is
`legendreSym.quadratic_reciprocity` up to commutativity of multiplication. -/
theorem quadratic_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p/2) * (q/2)) := by
  rw [mul_comm]
  exact legendreSym.quadratic_reciprocity hp hq hpq

/-- Euler's criterion: a nonzero residue mod an odd prime `p` is a square iff
`a ^ ((p-1)/2) = 1`. -/
theorem euler_criterion (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a : ZMod p) (ha : a ≠ 0) :
    IsSquare a ↔ a ^ ((p-1)/2) = 1 := by
  have hodd : Odd p := (Nat.Prime.odd_of_ne_two Fact.out hp)
  obtain ⟨k, hk⟩ := hodd
  have h1 : (p - 1) / 2 = p / 2 := by omega
  rw [h1]
  exact ZMod.euler_criterion p ha

/-- There are infinitely many primes. -/
theorem infinitude_primes6 : {p : ℕ | p.Prime}.Infinite :=
  Nat.infinite_setOf_prime

end C4.NT6

