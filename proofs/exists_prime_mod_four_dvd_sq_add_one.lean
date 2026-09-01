import Mathlib

def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- For even `n > 1`, the odd number `n ^ 2 + 1` exceeds `1`, so it has an odd prime factor,
and every odd prime factor of `n ^ 2 + 1` is congruent to `1` mod `4` (since `-1` is a square
mod such a prime). -/
theorem exists_prime_mod_four_dvd_sq_add_one {n : ℕ} (hn : 1 < n) (he : Even n) :
    ∃ p, Nat.Prime p ∧ p % 4 = 1 ∧ p ∣ n ^ 2 + 1 := by
  have hm1 : n ^ 2 + 1 ≠ 1 := by nlinarith
  have hpp : (n ^ 2 + 1).minFac.Prime := Nat.minFac_prime hm1
  have hdvd : (n ^ 2 + 1).minFac ∣ n ^ 2 + 1 := Nat.minFac_dvd _
  have hodd : ¬ (2 ∣ n ^ 2 + 1) := by
    obtain ⟨k, hk⟩ := he
    have hsq : n ^ 2 = 2 * (2 * k ^ 2) := by subst hk; ring
    omega
  have hp2 : (n ^ 2 + 1).minFac ≠ 2 := by
    intro h
    rw [h] at hdvd
    exact hodd hdvd
  haveI : Fact (n ^ 2 + 1).minFac.Prime := ⟨hpp⟩
  have hsq : IsSquare (-1 : ZMod (n ^ 2 + 1).minFac) := by
    refine ⟨(n : ZMod (n ^ 2 + 1).minFac), ?_⟩
    have h0 : ((n ^ 2 + 1 : ℕ) : ZMod (n ^ 2 + 1).minFac) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at h0
    linear_combination -h0
  have h4 : (n ^ 2 + 1).minFac % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.1 hsq
  have hodd' : (n ^ 2 + 1).minFac % 2 = 1 := Nat.odd_iff.1 (hpp.odd_of_ne_two hp2)
  exact ⟨_, hpp, by omega, hdvd⟩

#print axioms exists_prime_mod_four_dvd_sq_add_one

