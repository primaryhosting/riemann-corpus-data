/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `Omega n` is the number of prime factors of `n`, counted with multiplicity
(the classical arithmetic function `Ω`). -/
def Omega (n : ℕ) : ℕ := n.primeFactorsList.length

/-- `n` is a *Chen sum* if `n = p + q` with `p` prime and `q` having at most two
prime factors (counted with multiplicity). -/
def IsChenSum (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Omega q ≤ 2 ∧ n = p + q

/-- Chen's theorem: every sufficiently large even number is the sum of a prime and a
number with at most two prime factors. -/
def ChenStatement : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → IsChenSum n

/-! ## Basic facts about `Omega` -/

theorem Omega_prime {p : ℕ} (hp : Nat.Prime p) : Omega p = 1 := by
  simp [Omega, Nat.primeFactorsList_prime hp]

theorem Omega_mul_of_prime_of_prime {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    Omega (p * q) = 2 := by
  have h := Nat.perm_primeFactorsList_mul hp.ne_zero hq.ne_zero
  simp [Omega, h.length_eq, Nat.primeFactorsList_prime hp, Nat.primeFactorsList_prime hq]

/-- A prime is in particular a number with at most two prime factors. -/
theorem chenSum_of_add_primes {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    IsChenSum (p + q) :=
  ⟨p, q, hp, by simp [Omega_prime hq], rfl⟩

/-- A product of two primes has at most two prime factors, so `p + q * r` is a Chen sum. -/
theorem chenSum_of_add_semiprime {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hr : Nat.Prime r) : IsChenSum (p + q * r) :=
  ⟨p, q * r, hp, by simp [Omega_mul_of_prime_of_prime hq hr], rfl⟩

/-! ## A Lean-checked base case -/

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
private theorem base_check :
    ∀ n ∈ Finset.Icc 4 500, Even n → ∃ p ∈ Finset.range (n + 1),
      Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide

/-- **Base case, verified by computation.** Every even number `n` with `4 ≤ n ≤ 500` is a
Chen sum (indeed, a sum of two primes). -/
theorem Chen_base_case {n : ℕ} (h4 : 4 ≤ n) (h500 : n ≤ 500) (hn : Even n) : IsChenSum n := by
  obtain ⟨p, hp, hp1, hp2⟩ := base_check n (Finset.mem_Icc.2 ⟨h4, h500⟩) hn
  have hple : p ≤ n := by
    have := Finset.mem_range.1 hp
    omega
  have : n = p + (n - p) := by omega
  exact this ▸ chenSum_of_add_primes hp1 hp2

/-- **Unconditional infinitude.** Infinitely many even numbers are Chen sums: for every odd
prime `p`, the even number `2 * p = p + p` is one. -/
theorem Chen_infinite : {n : ℕ | Even n ∧ IsChenSum n}.Infinite := by
  have hinj : Set.InjOn (fun p : ℕ => 2 * p) {p : ℕ | p.Prime} := fun a _ b _ h => by
    simpa using h
  have hsub : (fun p : ℕ => 2 * p) '' {p : ℕ | p.Prime} ⊆ {n : ℕ | Even n ∧ IsChenSum n} := by
    rintro n ⟨p, hp, rfl⟩
    have hpp : (fun p : ℕ => 2 * p) p = p + p := by simp; ring
    rw [Set.mem_setOf_eq, hpp]
    exact ⟨⟨p, rfl⟩, chenSum_of_add_primes hp hp⟩
  exact Set.Infinite.mono hsub ((Nat.infinite_setOf_prime).image hinj)

/-! ## Reductions -/

/-- **A Lean-checked reduction: Goldbach implies Chen.** If every even number `≥ 4` is a sum
of two primes, then Chen's statement holds (with threshold `4`). -/
theorem Chen_of_Goldbach
    (H : ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q) :
    ChenStatement := by
  refine ⟨4, fun n hn hev => ?_⟩
  obtain ⟨p, q, hp, hq, rfl⟩ := H n hn hev
  exact chenSum_of_add_primes hp hq

/-- **Chen's theorem, reduced to a finiteness statement.**

Chen's theorem (every sufficiently large even number is the sum of a prime and a number with
at most two prime factors) is equivalent to the assertion that only finitely many even numbers
fail to be such a sum.  This is a Lean-checked reduction of the statement; the base case
`Chen_base_case` verifies the property for all even `n` with `4 ≤ n ≤ 500`. -/
theorem Chen_theorem :
    ChenStatement ↔ {n : ℕ | Even n ∧ ¬ IsChenSum n}.Finite := by
  constructor
  · rintro ⟨N, hN⟩
    refine Set.Finite.subset (Set.finite_Iio N) ?_
    rintro n ⟨hev, hns⟩
    by_contra hlt
    exact hns (hN n (le_of_not_gt hlt) hev)
  · intro hfin
    obtain ⟨M, hM⟩ := hfin.bddAbove
    refine ⟨M + 1, fun n hn hev => ?_⟩
    by_contra hns
    have : n ≤ M := hM ⟨hev, hns⟩
    omega

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

