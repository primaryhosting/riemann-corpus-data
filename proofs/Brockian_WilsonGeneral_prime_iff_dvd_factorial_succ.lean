import Mathlib
namespace Brockian.WilsonGeneral
/-- Wilson: n ≥ 2 is prime iff (n-1)! ≡ -1 (mod n), i.e. n ∣ ((n-1)! + 1). Prove the full iff
    at the ℕ level; axiom-clean, no sorry. -/
theorem prime_iff_dvd_factorial_succ {n : ℕ} (hn : 2 ≤ n) :
    n.Prime ↔ n ∣ (Nat.factorial (n - 1) + 1) := by
  have hn1 : n ≠ 1 := by omega
  rw [Nat.prime_iff_fac_equiv_neg_one hn1]
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  exact eq_neg_iff_add_eq_zero
end Brockian.WilsonGeneral
