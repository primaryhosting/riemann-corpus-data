import Mathlib
namespace C2.Crypto2

/-- The one-time pad encryption map `k ↦ m ^^^ k` is a bijection on `BitVec n`,
since XOR-ing with a fixed mask is an involution. -/
theorem otp_bij (n : ℕ) (m : BitVec n) : Function.Bijective (fun k : BitVec n => m ^^^ k) := by
  have hinv : Function.Involutive (fun k : BitVec n => m ^^^ k) := by
    intro k
    simp only
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  exact hinv.bijective

/-- RSA correctness: if `e * d ≡ 1 [MOD φ n]` and `m` is coprime to `n`, then
decryption inverts encryption, i.e. `(m ^ e) ^ d ≡ m [MOD n]`. -/
theorem rsa_correct (n e d m : ℕ) (hn : 0 < n) (h : e*d % (Nat.totient n) = 1 % (Nat.totient n))
    (hm : Nat.Coprime m n) : (m^e)^d % n = m % n := by
  have ht : 0 < Nat.totient n := Nat.totient_pos.2 hn
  -- Split the exponent `e * d` as `φ n * q + (1 % φ n)` and use Euler's theorem.
  have key : m ^ (e*d) ≡ m ^ (1 % Nat.totient n) [MOD n] := by
    conv_lhs => rw [← Nat.div_add_mod (e*d) (Nat.totient n)]
    rw [pow_add, pow_mul, h]
    calc (m ^ Nat.totient n) ^ (e*d/Nat.totient n) * m ^ (1 % Nat.totient n)
        ≡ 1 ^ (e*d/Nat.totient n) * m ^ (1 % Nat.totient n) [MOD n] :=
          Nat.ModEq.mul (Nat.ModEq.pow _ (Nat.ModEq.pow_totient hm)) (Nat.ModEq.refl _)
      _ = m ^ (1 % Nat.totient n) := by rw [one_pow, one_mul]
  have final : m ^ (1 % Nat.totient n) ≡ m [MOD n] := by
    rcases Nat.lt_or_ge (Nat.totient n) 2 with h2 | h2
    · -- `φ n = 1`, so `n = 1` or `n = 2`; both are handled directly.
      have ht1 : Nat.totient n = 1 := by omega
      rcases Nat.totient_eq_one_iff.1 ht1 with hn1 | hn2
      · subst hn1; exact Nat.modEq_one
      · subst hn2
        have hmm : m % 2 = 1 := Nat.odd_iff.1 (Nat.Coprime.odd_of_left (by simpa using hm))
        norm_num [Nat.ModEq, hmm]
    · rw [Nat.mod_eq_of_lt h2, pow_one]
  rw [← pow_mul]
  exact key.trans final

/-- XOR of a bit vector with itself is zero. -/
theorem xor_self (n : ℕ) (a : BitVec n) : a ^^^ a = 0 := BitVec.xor_self

end C2.Crypto2

