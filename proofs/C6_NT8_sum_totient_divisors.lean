import Mathlib
namespace C6.NT8

/-- Gauss's identity: the sum of `φ(d)` over the divisors `d` of `n` equals `n`.
The hypothesis `0 < n` is part of the requested statement; it turns out to be
unnecessary, since Mathlib's `Nat.sum_totient` also covers `n = 0`. -/
theorem sum_totient_divisors (n : ℕ) (hn : 0 < n) : ∑ d ∈ Nat.divisors n, Nat.totient d = n :=
  Nat.sum_totient n

/-- A prime `p ≤ n` divides `n !`. -/
theorem prime_dvd_factorial (p n : ℕ) (hp : p.Prime) (h : p ≤ n) : p ∣ n.factorial :=
  Nat.dvd_factorial hp.pos h

/-- Euler's theorem: if `a` is coprime to `n`, then `a ^ φ(n) ≡ 1 [MOD n]`. -/
theorem coprime_totient (n : ℕ) (a : ℕ) (h : Nat.Coprime a n) : a^(Nat.totient n) ≡ 1 [MOD n] :=
  Nat.ModEq.pow_totient h

end C6.NT8

