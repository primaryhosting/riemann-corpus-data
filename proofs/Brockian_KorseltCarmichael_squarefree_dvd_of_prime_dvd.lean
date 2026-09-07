import Mathlib

namespace Brockian.KorseltCarmichael

/-- A squarefree natural number divides any natural number divisible by all of its prime factors. -/
lemma squarefree_dvd_of_prime_dvd {n m : ℕ} (hn : n ≠ 0) (hsqf : Squarefree n)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ n → p ∣ m) : n ∣ m := by
  by_cases hm : m = 0
  · subst m
    exact Nat.dvd_zero n
  rw [← Nat.factorization_le_iff_dvd hn hm]
  intro p
  by_cases hp : p.Prime
  · by_cases hpn : p ∣ n
    · exact le_trans ((Nat.squarefree_iff_factorization_le_one hn).mp hsqf p)
        ((hp.dvd_iff_one_le_factorization hm).mp (hprime p hp hpn))
    · simp [Nat.factorization_eq_zero_of_not_dvd hpn]
  · simp [Nat.factorization_eq_zero_of_not_prime n hp]

/-- The local Fermat step used in Korselt's criterion. -/
lemma pow_modEq_self_of_prime_sub_one_dvd {p n a : ℕ} (hp : p.Prime)
    (hcop : a.Coprime p) (hdiv : p - 1 ∣ n - 1) (hn : 1 ≤ n) :
    a ^ n ≡ a [MOD p] := by
  obtain ⟨k, hk⟩ := hdiv
  have hnrep : n = (p - 1) * k + 1 := by omega
  rw [hnrep, pow_add, pow_mul]
  simpa using
    (Nat.ModEq.pow_card_sub_one_eq_one hp hcop).pow k |>.mul (Nat.ModEq.refl a)

/-- Korselt criterion (hard direction): if n is composite, squarefree, and (p-1) | (n-1) for every
    prime p | n, then n is a Fermat pseudoprime to every base coprime to n: a^n ≡ a (mod n).
    Prove; axiom-clean, no sorry. -/
theorem korselt_carmichael {n : ℕ} (h1 : 1 < n) (hcomp : ¬ n.Prime) (hsqf : Squarefree n)
    (hk : ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)) :
    ∀ a : ℕ, Nat.Coprime a n → a ^ n ≡ a [MOD n] := by
  by_cases hnprime : n.Prime
  · exact (hcomp hnprime).elim
  intro a ha
  have hn0 : n ≠ 0 := by omega
  have hle : a ≤ a ^ n := Nat.le_pow (by omega)
  apply Nat.ModEq.symm
  rw [Nat.modEq_iff_dvd' hle]
  apply squarefree_dvd_of_prime_dvd hn0 hsqf
  intro p hp hpn
  rw [← Nat.modEq_iff_dvd' hle]
  exact (pow_modEq_self_of_prime_sub_one_dvd hp (ha.of_dvd_right hpn)
    (hk p hp hpn) (by omega)).symm

end Brockian.KorseltCarmichael
