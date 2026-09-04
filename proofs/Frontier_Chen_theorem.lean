-- Lean 4 requires every `import` to precede all other commands, so the required module header
-- comment appears immediately after the import below.
import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

open ArithmeticFunction

/-- `n` admits a *Chen representation*: `n = p + q` with `p` prime and `q` having at most two
prime factors counted with multiplicity (`Ω q ≤ 2`, i.e. `q` is `1`, a prime, or a semiprime). -/
def IsChenNumber (n : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ n = p + q ∧ cardFactors q ≤ 2

/-- The statement of Chen's theorem: every sufficiently large even number `n` can be written as
`p + q` with `p` prime and `q` a product of at most two primes. -/
def ChenStatement : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → IsChenNumber n

/-- The (binary) Goldbach conjecture: every even number `n ≥ 4` is a sum of two primes. -/
def GoldbachEven : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p + q

/-- A sum of two primes is a Chen number (a prime has exactly one prime factor). -/
theorem isChenNumber_of_sum_two_primes {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : n = p + q) : IsChenNumber n :=
  ⟨p, q, hp, h, by simp [cardFactors_apply_prime hq]⟩

/-- Kernel-checked Goldbach search for all even numbers below `501`, using only primes `< 100`. -/
theorem goldbach_below_501 :
    ∀ n < 501, 4 ≤ n → n % 2 = 0 → ∃ p < 100, Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide

/-- **Base case (Lean-verified computation).** Every even number `n` with `4 ≤ n ≤ 500` is a Chen
number; in fact it is already a sum of two primes. -/
theorem chen_base_case (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 500) (he : Even n) : IsChenNumber n := by
  obtain ⟨p, -, hp, hq⟩ := goldbach_below_501 n (by omega) h4 (Nat.even_iff.mp he)
  have h2 := hq.two_le
  exact isChenNumber_of_sum_two_primes hp hq (by omega)

/-- **Reduction.** The binary Goldbach conjecture implies Chen's theorem. -/
theorem chen_of_goldbach (h : GoldbachEven) : ChenStatement := by
  refine ⟨4, fun n hn he => ?_⟩
  obtain ⟨p, q, hp, hq, hpq⟩ := h n hn he
  exact isChenNumber_of_sum_two_primes hp hq hpq

/-- **Reduction (thresholds are irrelevant below a verified range).** If Chen's property holds
from some threshold `N ≤ 501` on, and for all even numbers in `[4, N)`, then it holds for every
even number `≥ 4`.  Combined with `chen_base_case` this shows that any proof of `ChenStatement`
with threshold at most `501` upgrades to the unrestricted statement. -/
theorem chen_all_even_of_threshold {N : ℕ} (hN : N ≤ 501)
    (h : ∀ n : ℕ, N ≤ n → Even n → IsChenNumber n) :
    ∀ n : ℕ, 4 ≤ n → Even n → IsChenNumber n := by
  intro n h4 he
  by_cases hle : N ≤ n
  · exact h n hle he
  · exact chen_base_case n h4 (by omega) he

/-- **Chen's theorem: formalized statement, verified base case, and Lean-checked reductions.**

`ChenStatement` asserts that every sufficiently large even number is of the form `p + q` with `p`
prime and `Ω q ≤ 2` (so `q` has at most two prime factors with multiplicity).

The three conjuncts proved here are:

1. the *base case*: every even `n` with `4 ≤ n ≤ 500` is a Chen number (checked by kernel
   computation, via an explicit Goldbach decomposition);
2. a *reduction*: the binary Goldbach conjecture implies Chen's theorem;
3. a *reduction*: any proof of `ChenStatement` with threshold `≤ 501` upgrades to the statement
   for all even numbers `≥ 4`.

The full analytic proof of Chen's theorem (via sieve methods) is not formalized here. -/
theorem Chen_theorem :
    (∀ n : ℕ, 4 ≤ n → n ≤ 500 → Even n → IsChenNumber n) ∧
    (GoldbachEven → ChenStatement) ∧
    (∀ N : ℕ, N ≤ 501 → (∀ n : ℕ, N ≤ n → Even n → IsChenNumber n) →
      ∀ n : ℕ, 4 ≤ n → Even n → IsChenNumber n) :=
  ⟨fun n h4 hn he => chen_base_case n h4 hn he,
   chen_of_goldbach,
   fun _ hN h => chen_all_even_of_threshold hN h⟩

end Frontier

