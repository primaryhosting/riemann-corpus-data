/-
  Brockian/DivisorCountStructure.lean — general structural theorems for the
  divisor-count function τ.

  These are GENERAL τ-structure theorems (not concrete numerical instances):
  they pin down the qualitative behaviour of the number-of-divisors function
  `τ n = n.divisors.card` (the cardinality of the finite set `Nat.divisors n`).
  Every concrete divisor count is an instance of facts like these.

  Contents:
    * `tau_odd_iff_isSquare`   — **FLAGSHIP.** `τ n` is odd iff `n` is a perfect
        square (for `n > 0`). Proved here via the multiplicative formula
        `τ n = ∏_{p ∣ n} (v_p(n) + 1)`: this product is odd iff every exponent
        `v_p(n)` is even, which is exactly the condition for `n` to be a square.
        (Not found as a single named lemma in Mathlib at this toolchain; proved
        from `Nat.card_divisors` + a `IsSquare ↔ even factorization` bridge.)
    * `isSquare_iff_even_factorization` — the bridge lemma used by the flagship:
        `n` is a square iff every prime exponent in its factorization is even.
    * `tau_eq_two_iff_prime`   — `τ n = 2 ⇔ n` is prime.
    * `tau_eq_one_iff`         — `τ n = 1 ⇔ n = 1`.
    * `tau_pos_iff`            — `0 < τ n ⇔ 0 < n`.
    * `tau_prime_pow`          — `τ (p ^ k) = k + 1` for `p` prime.

  Verification:
    - AXLE independent : verified @ lean-4.32.0
  No `sorry`, `admit`, `native_decide`, or `axiom` is used anywhere in this file.
-/
import Mathlib

open Finset

namespace Brockian.DivisorCountStructure

/-- **Square ⇔ even factorization.** A positive natural number `n` is a perfect
square iff every prime in its factorization occurs to an even power. Forward:
`n = r * r` doubles each exponent. Backward: `∏ p ^ (v_p(n) / 2)` squares to `n`
when every `v_p(n)` is even. -/
theorem isSquare_iff_even_factorization {n : ℕ} (hn : n ≠ 0) :
    IsSquare n ↔ ∀ p ∈ n.primeFactors, Even (n.factorization p) := by
  constructor
  · rintro ⟨r, rfl⟩
    have hr : r ≠ 0 := by rintro rfl; simp at hn
    intro p _
    rw [Nat.factorization_mul hr hr, Finsupp.add_apply]
    exact ⟨r.factorization p, rfl⟩
  · intro h
    refine ⟨n.factorization.prod (fun p k => p ^ (k / 2)), ?_⟩
    have e1 : n.factorization.prod (fun p k => p ^ (k / 2))
            * n.factorization.prod (fun p k => p ^ (k / 2))
            = n.factorization.prod (fun p k => p ^ k) := by
      simp only [Finsupp.prod]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x hx => ?_
      rw [← pow_add]
      obtain ⟨m, hm⟩ := h x (by rwa [Nat.support_factorization] at hx)
      congr 1
      omega
    rw [e1, Nat.prod_factorization_pow_eq_self hn]

/-- **FLAGSHIP — τ is odd iff `n` is a perfect square.** For `n > 0`, the number
of divisors `τ n = n.divisors.card` is odd precisely when `n` is a perfect
square. Divisors pair off as `d ↔ n / d`; this pairing has a fixed point (forcing
odd parity) exactly when some `d² = n`. The proof below realises this via the
multiplicative divisor-count formula `τ n = ∏_{p ∣ n} (v_p(n) + 1)`, which is odd
iff every exponent `v_p(n)` is even — the square condition. -/
theorem tau_odd_iff_isSquare {n : ℕ} (hn : 0 < n) :
    Odd (n.divisors.card) ↔ IsSquare n := by
  have hn0 : n ≠ 0 := hn.ne'
  rw [isSquare_iff_even_factorization hn0, Nat.card_divisors hn0,
      ← Nat.not_even_iff_odd, even_iff_two_dvd,
      (Nat.prime_two.prime).dvd_finsetProd_iff]
  push_neg
  refine ⟨fun H p hp => ?_, fun H p hp => ?_⟩
  · have hd := H p hp
    rw [← even_iff_two_dvd, Nat.even_add_one, not_not] at hd
    exact hd
  · have he := H p hp
    rw [← even_iff_two_dvd, Nat.even_add_one, not_not]
    exact he

/-- **Exactly two divisors ⇔ prime.** `τ n = 2` characterises the primes: `n` must
be `≥ 2` (it is neither `0` nor `1`), and then having only the two forced divisors
`{1, n}` is exactly primality. -/
theorem tau_eq_two_iff_prime {n : ℕ} : n.divisors.card = 2 ↔ n.Prime := by
  constructor
  · intro h
    have hn0 : n ≠ 0 := by rintro rfl; simp at h
    have hn1 : n ≠ 1 := by rintro rfl; simp at h
    have h1 : (1 : ℕ) ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
    have hnn : n ∈ n.divisors := Nat.mem_divisors_self n hn0
    have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact h1
      · exact hnn
    have hcard2 : ({1, n} : Finset ℕ).card = 2 := Finset.card_pair (by omega)
    have heq : n.divisors = ({1, n} : Finset ℕ) :=
      (Finset.eq_of_subset_of_card_le hsub (Nat.le_of_eq (by rw [h, hcard2]))).symm
    rw [Nat.prime_def_lt]
    refine ⟨by omega, ?_⟩
    intro m hmlt hmdvd
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [Nat.zero_dvd] at hmdvd
      exact hn0 hmdvd
    have hmem : m ∈ n.divisors := Nat.mem_divisors.mpr ⟨hmdvd, hn0⟩
    rw [heq] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl
    · rfl
    · omega
  · intro hp
    rw [Nat.Prime.divisors hp, Finset.card_pair hp.one_lt.ne]

/-- **One divisor ⇔ `n = 1`.** The only number with a single divisor is `1`
(recall `0` has an empty divisor set, hence count `0`). -/
theorem tau_eq_one_iff {n : ℕ} : n.divisors.card = 1 ↔ n = 1 :=
  Nat.divisors_card_eq_one_iff n

/-- **Positive divisor count ⇔ positive `n`.** The divisor set is nonempty exactly
when `n ≠ 0`. -/
theorem tau_pos_iff {n : ℕ} : 0 < n.divisors.card ↔ 0 < n := by
  rw [Finset.card_pos, Nat.nonempty_divisors, Nat.pos_iff_ne_zero]

/-- **Divisor count of a prime power.** `τ (p ^ k) = k + 1`: the divisors of
`p ^ k` are exactly `1, p, …, p ^ k`. This is the base case of τ-multiplicativity. -/
theorem tau_prime_pow {p k : ℕ} (hp : p.Prime) :
    (p ^ k).divisors.card = k + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

end Brockian.DivisorCountStructure
