import Mathlib
namespace Brockian.LucasTheorem
/-- Lucas' theorem (recursive form): C(m,n) ≡ C(m/p, n/p)·C(m%p, n%p) mod p, for p prime. -/
theorem lucas (p : ℕ) (hp : p.Prime) (m n : ℕ) :
    Nat.choose m n ≡ Nat.choose (m / p) (n / p) * Nat.choose (m % p) (n % p) [MOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa [Nat.mul_comm] using
    (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := m) (k := n) (p := p))
end Brockian.LucasTheorem

