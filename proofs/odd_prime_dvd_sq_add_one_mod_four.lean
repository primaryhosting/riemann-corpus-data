import Mathlib

/-- Landau's fourth problem (**OPEN**), recorded as an unproven `def`:
infinitely many `n` have `n ^ 2 + 1` prime. -/
def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- Every odd prime divisor `p` of `n ^ 2 + 1` satisfies `p % 4 = 1`:
in `ZMod p` the element `n` squares to `-1`, so `-1` is a quadratic residue,
which forces `p % 4 ≠ 3`; oddness then leaves only `p % 4 = 1`. -/
theorem odd_prime_dvd_sq_add_one_mod_four {n p : ℕ}
    (hp : Nat.Prime p) (hodd : Odd p) (h : p ∣ n ^ 2 + 1) :
    p % 4 = 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h0 : ((n ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr h
  push_cast at h0
  have hsq : IsSquare (-1 : ZMod p) := ⟨(n : ZMod p), by linear_combination -h0⟩
  have h3 := (ZMod.exists_sq_eq_neg_one_iff (p := p)).mp hsq
  have hp2 : p % 2 = 1 := Nat.odd_iff.mp hodd
  omega

