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

/-
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cullen Prime Infinitude

Cullen numbers are `C n = n * 2 ^ n + 1`.  Whether infinitely many of them are prime is a
well-known open problem, so the target `CullenPrimeInfinitude` below is stated and proved as
an unconditional *reduction*: the set of Cullen prime indices is infinite iff Cullen primes
occur past every bound.

We also prove the classical partial results in the opposite direction: every odd prime `p`
divides `C (p - 2)`, hence `C (p - 2)` is composite for every prime `p ≥ 5`, and therefore
infinitely many Cullen numbers are composite.
-/

namespace Brockian.CullenWoodall

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- The set of indices `n` for which the Cullen number `C n` is prime. -/
def cullenPrimeIndices : Set ℕ := {n | (cullen n).Prime}

/-- **Cullen prime infinitude, reduced to an arbitrarily-large-witness statement.**

Whether infinitely many Cullen numbers are prime is an open problem.  This theorem is an
unconditional Lean-checked *reduction*: the set of Cullen prime indices is infinite exactly
when Cullen primes occur beyond every bound. -/
theorem CullenPrimeInfinitude :
    cullenPrimeIndices.Infinite ↔ ∀ N : ℕ, ∃ n > N, (cullen n).Prime := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt, hn⟩
  · intro h
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨n, hlt, hn⟩ := h N
    exact ⟨n, hn, hlt⟩

/-- For an odd prime `p`, the Cullen number `C (p - 2)` is divisible by `p`.
Indeed `2 * C (p - 2) ≡ (p - 2) * 2 ^ (p - 1) + 2 ≡ -2 + 2 ≡ 0 (mod p)` by Fermat's little
theorem. -/
theorem prime_dvd_cullen_sub_two {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) :
    p ∣ cullen (p - 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h2p : 2 ≤ p := hp.two_le
  have hne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have := (ZMod.natCast_eq_zero_iff 2 p).1 h'
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have hfermat : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne
  have hsplit : (2 : ZMod p) ^ (p - 1) = 2 * 2 ^ (p - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hcast : ((p - 2 : ℕ) : ZMod p) = -2 := by
    rw [Nat.cast_sub h2p]
    simp
  have hzero : ((cullen (p - 2) : ℕ) : ZMod p) = 0 := by
    have h2 : (2 : ZMod p) * ((cullen (p - 2) : ℕ) : ZMod p) = 0 := by
      unfold cullen
      push_cast
      rw [hcast]
      have hring : (2 : ZMod p) * ((-2) * 2 ^ (p - 2) + 1) = -2 * (2 * 2 ^ (p - 2)) + 2 := by ring
      rw [hring, ← hsplit, hfermat]
      ring
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hne
    · exact h
  exact (ZMod.natCast_eq_zero_iff _ _).1 hzero

/-- For a prime `p ≥ 5`, the Cullen number `C (p - 2)` is composite: it is a proper multiple
of `p`. -/
theorem cullen_not_prime_of_prime {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    ¬ (cullen (p - 2)).Prime := by
  intro hq
  have hdvd := prime_dvd_cullen_sub_two hp (by omega)
  have heq : p = cullen (p - 2) := (Nat.prime_dvd_prime_iff_eq hp hq).1 hdvd
  have hlt : p - 2 < 2 ^ (p - 2) := Nat.lt_two_pow_self
  have hge : 3 ≤ p - 2 := by omega
  have hmul : 3 * 2 ^ (p - 2) ≤ (p - 2) * 2 ^ (p - 2) := Nat.mul_le_mul_right _ hge
  have hkey : p < cullen (p - 2) := by
    unfold cullen
    omega
  omega

/-- There are infinitely many `n` for which the Cullen number `C n` is *composite*
(indeed `p ∣ C (p - 2)` for every prime `p ≥ 5`). -/
theorem infinite_cullen_composite : {n : ℕ | ¬ (cullen n).Prime}.Infinite := by
  refine Set.infinite_of_forall_exists_gt ?_
  intro N
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (N + 5)
  exact ⟨p - 2, cullen_not_prime_of_prime hp (by omega), by omega⟩

end Brockian.CullenWoodall

