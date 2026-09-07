import Mathlib

/-!
# Necessary conditions on a counterexample to Lehmer's totient problem

**Lehmer's totient problem** (D. H. Lehmer, 1932) asks whether `φ(n) ∣ (n − 1)` forces
`n` to be prime.  It is **OPEN**: no composite `n` with `φ(n) ∣ (n − 1)` is known, and
none has been proved to exist.  A *Lehmer number* is exactly such a hypothetical
composite counterexample.

This file does **not** resolve Lehmer's problem.  It proves genuine, unconditional
*necessary conditions*: true theorems of the shape

> IF a Lehmer number exists, THEN it must satisfy `P`.

Every result here is a real proof.  Nothing here asserts either the existence or the
non-existence of a Lehmer number.

We write `φ = Nat.totient`.

## Main results

* `lehmer_odd`        — a Lehmer number is odd.
* `lehmer_squarefree` — **flagship**: a Lehmer number is squarefree.
* `lehmer_three_primes` — **stretch**: a Lehmer number has at least three distinct
  prime factors.
-/

namespace Brockian.LehmerTotient

open Finset

/-- A **Lehmer number**: a composite `n > 1` (i.e. not prime) with `φ(n) ∣ (n − 1)`.
Whether any such number exists is Lehmer's open totient problem. -/
def Lehmer (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime ∧ Nat.totient n ∣ (n - 1)

/-! ### (1) A Lehmer number is odd -/

/-- **Necessary condition (1).** A Lehmer number is odd.

If `n` were even it would be `≥ 4` (it is `> 1` and composite, so `n ≠ 2`); then
`φ(n)` is even (`Nat.totient_even`), so `2 ∣ φ(n) ∣ (n − 1)`, making `n − 1` even and
hence `n` odd — contradicting evenness. -/
theorem lehmer_odd {n : ℕ} (h : Lehmer n) : Odd n := by
  obtain ⟨hn1, hnp, hdvd⟩ := h
  rw [Nat.odd_iff]
  by_contra hne
  -- `n` is even.
  have heven : n % 2 = 0 := by omega
  have h2dvd : 2 ∣ n := Nat.dvd_of_mod_eq_zero heven
  -- `n ≠ 2` since `2` is prime but `n` is not; with `n` even and `> 1`, get `2 < n`.
  have hne2 : n ≠ 2 := by rintro rfl; exact hnp Nat.prime_two
  have h2lt : 2 < n := by omega
  -- `φ(n)` is even, and `φ(n) ∣ (n − 1)`, so `2 ∣ (n − 1)`.
  have hφeven : 2 ∣ Nat.totient n := (Nat.totient_even h2lt).two_dvd
  have h2n1 : 2 ∣ (n - 1) := hφeven.trans hdvd
  -- `2 ∣ n` and `2 ∣ (n − 1)` with `n > 1` force `2 ∣ 1`, impossible.
  omega

/-! ### (2) Flagship: a Lehmer number is squarefree -/

/-- **Flagship necessary condition (2).** A Lehmer number is squarefree.

If a prime `p` had `p² ∣ n`, then `φ(p²) ∣ φ(n)` (`Nat.totient_dvd_of_dvd`) and
`φ(p²) = p·(p−1)` (`Nat.totient_prime_pow`), so `p ∣ φ(n) ∣ (n − 1)`.  But `p ∣ n`,
and `p` cannot divide two consecutive numbers `n` and `n − 1`.  Contradiction. -/
theorem lehmer_squarefree {n : ℕ} (h : Lehmer n) : Squarefree n := by
  obtain ⟨hn1, hnp, hdvd⟩ := h
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hpnat hpp
  -- Inside `namespace Nat`, `Prime` in the characterization is `Nat.Prime`; `p² ∣ n`.
  have hp2 : p ^ 2 ∣ n := by rw [pow_two]; exact hpp
  -- `φ(p²) ∣ φ(n)`, and `p ∣ φ(p²)`.
  have hφ : Nat.totient (p ^ 2) ∣ Nat.totient n := Nat.totient_dvd_of_dvd hp2
  have hpφp2 : p ∣ Nat.totient (p ^ 2) := by
    rw [Nat.totient_prime_pow hpnat (by norm_num : 0 < 2)]
    exact (dvd_pow_self p (by norm_num : (2 - 1) ≠ 0)).mul_right (p - 1)
  -- Hence `p ∣ φ(n) ∣ (n − 1)`, and also `p ∣ n`.
  have hpn1 : p ∣ (n - 1) := (hpφp2.trans hφ).trans hdvd
  have hpn : p ∣ n := (dvd_mul_right p p).trans hpp
  -- `p` divides the consecutive numbers `n` and `n − 1`, hence divides `1`.
  have hn' : n = (n - 1) + 1 := by omega
  rw [hn'] at hpn
  have hp1 : p ∣ 1 := (Nat.dvd_add_right hpn1).mp hpn
  have := Nat.le_of_dvd one_pos hp1
  have := hpnat.two_le
  omega

/-! ### (3) A Lehmer number has at least three distinct prime factors -/

/-- **Necessary condition (3).** A Lehmer number has at least three distinct prime
factors.

Being composite and squarefree it is neither `1`, a prime, nor a prime power, so it has
`≥ 2` prime factors.  If it had exactly two, then `n = p·q` for distinct odd primes and
`φ(n) = (p−1)(q−1) ∣ (n − 1) = pq − 1`.  Writing `p = a+1, q = b+1` this reads
`ab ∣ (ab + a + b)`, hence `ab ∣ (a+b)` and so `ab ≤ a+b`; but `a, b ≥ 2` with `a ≠ b`
force `ab > a+b`.  Contradiction. -/
theorem lehmer_three_primes {n : ℕ} (h : Lehmer n) : 3 ≤ n.primeFactors.card := by
  have hodd := lehmer_odd h
  have hsqf := lehmer_squarefree h
  obtain ⟨hn1, hnp, hdvd⟩ := h
  have hn0 : n ≠ 0 := by omega
  by_contra hlt
  have hcases : n.primeFactors.card = 0 ∨ n.primeFactors.card = 1 ∨
      n.primeFactors.card = 2 := by omega
  rcases hcases with hc | hc | hc
  · -- card = 0 : then `n = 1`, contradicting `n > 1`.
    rw [Finset.card_eq_zero] at hc
    rw [← Nat.prod_primeFactors_of_squarefree hsqf, hc, Finset.prod_empty] at hn1
    omega
  · -- card = 1 : squarefree with one prime factor ⇒ `n` is prime, contradiction.
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hpmem : p ∈ n.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hnp' : n = p := by
      rw [← Nat.prod_primeFactors_of_squarefree hsqf, hp, Finset.prod_singleton]
    exact hnp (hnp' ▸ hprime)
  · -- card = 2 : `n = p * q`, distinct odd primes; the totient bound is contradictory.
    obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc
    have hpmem : p ∈ n.primeFactors := by rw [hset]; exact Finset.mem_insert_self p {q}
    have hqmem : q ∈ n.primeFactors := by
      rw [hset]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self q)
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hqmem
    have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
    have hqdvd : q ∣ n := Nat.dvd_of_mem_primeFactors hqmem
    have hnpq : n = p * q := by
      rw [← Nat.prod_primeFactors_of_squarefree hsqf, hset, Finset.prod_pair hpq]
    -- both primes are odd (they divide the odd `n`), hence `≥ 3`.
    have hnmod : n % 2 = 1 := Nat.odd_iff.mp hodd
    have hp3 : 3 ≤ p := by
      have h2 := hpp.two_le
      have : p ≠ 2 := by rintro rfl; omega
      omega
    have hq3 : 3 ≤ q := by
      have h2 := hqp.two_le
      have : q ≠ 2 := by rintro rfl; omega
      omega
    -- `φ(n) = (p−1)(q−1)` and `φ(n) ∣ n − 1`.
    have hcop : p.Coprime q := (Nat.coprime_primes hpp hqp).mpr hpq
    have htot : Nat.totient n = (p - 1) * (q - 1) := by
      rw [hnpq, Nat.totient_mul hcop, Nat.totient_prime hpp, Nat.totient_prime hqp]
    have hdvd2 : (p - 1) * (q - 1) ∣ (p * q - 1) := by
      rw [← htot, ← hnpq]; exact hdvd
    -- substitute `p = a+1`, `q = b+1`.
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 1 := ⟨p - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hdvd2
    -- `a*b ∣ (a+1)(b+1) − 1 = a*b + a + b`.
    have hmul : (a + 1) * (b + 1) = a * b + a + b + 1 := by ring
    rw [hmul] at hdvd2
    have hsub : a * b + a + b + 1 - 1 = a * b + (a + b) := by omega
    rw [hsub] at hdvd2
    -- hence `a*b ∣ (a+b)`, so `a*b ≤ a+b`.
    have hab : a * b ∣ (a + b) := (Nat.dvd_add_right (dvd_refl (a * b))).mp hdvd2
    have ha2 : 2 ≤ a := by omega
    have hb2 : 2 ≤ b := by omega
    have hle : a * b ≤ a + b := Nat.le_of_dvd (by omega) hab
    have hx1 : 2 * b ≤ a * b := by nlinarith
    have hx2 : 2 * a ≤ a * b := by nlinarith
    omega

end Brockian.LehmerTotient
