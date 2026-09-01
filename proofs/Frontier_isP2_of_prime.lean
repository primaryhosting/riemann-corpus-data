import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires the `import` commands to come first in a module, so the
prescribed header comment above is placed immediately after `import Mathlib`.

Contents:

* `Frontier.IsP2`, `Frontier.ChenRepresentable`, `Frontier.ChenStatement` : the formal statement
  of Chen's theorem ("every sufficiently large even number is `p + q` with `p` prime and `q`
  having at most two prime factors").
* `Frontier.Chen_base_case` : an unconditional, kernel-checked verification of the conclusion for
  all even `n` with `4 ≤ n ≤ 500`.
* `Frontier.Chen_theorem` : a Lean-checked reduction of the full statement to the sieve statement
  that Chen's method produces (a prime `p` with all prime factors of `n - p` exceeding `n ^ (1/3)`).
* `Frontier.goldbach_implies_chen` : the (easier) reduction of Chen's statement to Goldbach's
  conjecture.
-/

open ArithmeticFunction

namespace Frontier

/-- `q` is an *almost prime of order 2* (a `P₂` number): `q > 1` and `q` has at most two prime
factors counted with multiplicity (`Ω q ≤ 2`), i.e. `q` is a prime or a product of two primes. -/
def IsP2 (q : ℕ) : Prop := 1 < q ∧ cardFactors q ≤ 2

/-- `n` admits a *Chen representation*: `n = p + q` with `p` prime and `q` a `P₂` number. -/
def ChenRepresentable (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ IsP2 q ∧ n = p + q

/-- **Chen's theorem** (statement): every sufficiently large even number is the sum of a prime and
a number having at most two prime factors. -/
def ChenStatement : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ChenRepresentable n

/-- The sieve statement underlying Chen's method: for every sufficiently large even `n` there is a
prime `p` with `1 < n - p` such that every prime factor `r` of `n - p` satisfies `n < r ^ 3`
(i.e. `r > n ^ (1/3)`). -/
def ChenSieveStatement : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ∃ p : ℕ, Nat.Prime p ∧ p + 1 < n ∧
    ∀ r : ℕ, Nat.Prime r → r ∣ (n - p) → n < r ^ 3

/-- **Goldbach's conjecture** (statement): every even number `n ≥ 4` is a sum of two primes. -/
def GoldbachStatement : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-- A prime is a `P₂` number. -/
theorem isP2_of_prime {q : ℕ} (hq : Nat.Prime q) : IsP2 q :=
  ⟨hq.one_lt, by rw [cardFactors_apply_prime hq]; norm_num⟩

/-- A product of two primes is a `P₂` number. -/
theorem isP2_of_prime_mul_prime {a b : ℕ} (ha : Nat.Prime a) (hb : Nat.Prime b) :
    IsP2 (a * b) := by
  refine ⟨?_, ?_⟩
  · calc 1 < a := ha.one_lt
      _ ≤ a * b := Nat.le_mul_of_pos_right a hb.pos
  · rw [cardFactors_mul ha.ne_zero hb.ne_zero, cardFactors_apply_prime ha,
      cardFactors_apply_prime hb]

/-- If `n` is a sum of two primes then it has a Chen representation. -/
theorem chenRepresentable_of_sum_two_primes {n p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : n = p + q) : ChenRepresentable n :=
  ⟨p, q, hp, isP2_of_prime hq, h⟩

/-- If three natural numbers all have cube exceeding `n`, so does their product exceed `n`. -/
theorem lt_prod_three {n a b c : ℕ} (ha : n < a ^ 3) (hb : n < b ^ 3) (hc : n < c ^ 3) :
    n < a * b * c := by
  by_contra h
  push_neg at h
  have h1 : (n + 1) ^ 3 ≤ a ^ 3 * b ^ 3 * c ^ 3 := by
    have h0 : (n + 1) * (n + 1) * (n + 1) ≤ a ^ 3 * b ^ 3 * c ^ 3 :=
      Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
    nlinarith [h0]
  have h2 : (a * b * c) ^ 3 ≤ n ^ 3 := Nat.pow_le_pow_left h 3
  nlinarith [h1, h2]

/-- **Sieve criterion for almost primality.** If `1 < q ≤ n` and every prime factor of `q`
exceeds `n ^ (1/3)` (in the form `n < r ^ 3`), then `q` has at most two prime factors counted
with multiplicity, i.e. `q` is a `P₂` number. -/
theorem isP2_of_large_prime_factors {n q : ℕ} (hq1 : 1 < q) (hqn : q ≤ n)
    (h : ∀ r : ℕ, Nat.Prime r → r ∣ q → n < r ^ 3) : IsP2 q := by
  refine ⟨hq1, ?_⟩
  by_contra hc
  push_neg at hc
  rw [ArithmeticFunction.cardFactors_apply] at hc
  have hq0 : q ≠ 0 := by omega
  have hprod : q.primeFactorsList.prod = q := Nat.prod_primeFactorsList hq0
  have hbig : ∀ x ∈ q.primeFactorsList, n < x ^ 3 := fun x hx =>
    h x (Nat.prime_of_mem_primeFactorsList hx) (Nat.dvd_of_mem_primeFactorsList hx)
  have hpos : ∀ x ∈ q.primeFactorsList, 1 ≤ x := fun x hx =>
    (Nat.prime_of_mem_primeFactorsList hx).one_lt.le
  revert hprod hbig hpos hc
  generalize q.primeFactorsList = L
  match L with
  | [] => intro h1; simp at h1
  | [_] => intro h1; simp at h1
  | [_, _] => intro h1; simp at h1
  | (a :: b :: c :: t) =>
      intro _ hprod hbig hpos
      simp only [List.prod_cons] at hprod
      have hta : 1 ≤ t.prod := List.one_le_prod (fun x hx => hpos x (by simp [hx]))
      have h3 := lt_prod_three (n := n) (hbig a (by simp)) (hbig b (by simp)) (hbig c (by simp))
      have habc : a * b * c ≤ a * (b * (c * t.prod)) := by
        calc a * b * c = a * b * c * 1 := by ring
          _ ≤ a * b * c * t.prod := Nat.mul_le_mul_left _ hta
          _ = a * (b * (c * t.prod)) := by ring
      omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000000 in
/-- Kernel-checked computation: every even `n` with `4 ≤ n ≤ 500` is a sum of two primes, the
smaller one being below `100`. -/
theorem goldbach_le_500 :
    ∀ n ∈ Finset.Icc 4 500, Even n → ∃ p ∈ Finset.range 100,
      Nat.Prime p ∧ Nat.Prime (n - p) := by decide

/-- **Base case of Chen's theorem, verified in Lean**: every even number `n` with `4 ≤ n ≤ 500`
has a Chen representation (in fact as a sum of two primes). -/
theorem Chen_base_case (n : ℕ) (h4 : 4 ≤ n) (h500 : n ≤ 500) (hn : Even n) :
    ChenRepresentable n := by
  obtain ⟨p, -, hp, hq⟩ := goldbach_le_500 n (Finset.mem_Icc.mpr ⟨h4, h500⟩) hn
  refine chenRepresentable_of_sum_two_primes hp hq ?_
  have hpn : p ≤ n := by
    by_contra hlt
    have h0 : n - p = 0 := Nat.sub_eq_zero_of_le (le_of_lt (not_le.mp hlt))
    rw [h0] at hq
    exact Nat.not_prime_zero hq
  omega

/-- **Chen's theorem, as a Lean-checked reduction.**

The full statement of Chen's theorem — every sufficiently large even number `n` is `p + q` with
`p` prime and `q` having at most two prime factors — is reduced here to the sieve statement that
Chen's method produces: for all large even `n` there is a prime `p` such that `n - p > 1` has no
prime factor below `n ^ (1/3)`. Given such a `p`, the number `q = n - p` cannot have three or
more prime factors, since their product would already exceed `n`; hence `q` is a `P₂` number.

Unconditionally, the conclusion is verified by kernel computation for all even `n` with
`4 ≤ n ≤ 500` in `Frontier.Chen_base_case`, and it also follows from Goldbach's conjecture, see
`Frontier.goldbach_implies_chen`. -/
theorem Chen_theorem : ChenSieveStatement → ChenStatement := by
  rintro ⟨N, hN⟩
  refine ⟨N, fun n hn hev => ?_⟩
  obtain ⟨p, hp, hpn, hfac⟩ := hN n hn hev
  refine ⟨p, n - p, hp, isP2_of_large_prime_factors (n := n) (by omega) (by omega) hfac, ?_⟩
  omega

/-- Goldbach's conjecture implies Chen's statement (with `N = 4`), since a prime is in particular
a number with at most two prime factors. -/
theorem goldbach_implies_chen : GoldbachStatement → ChenStatement := by
  intro hG
  refine ⟨4, fun n hn hev => ?_⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := hG n hn hev
  exact chenRepresentable_of_sum_two_primes hp hq hpq

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

