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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: `Brockian.PolignacPrimes.PolignacConjecture`
Provenance: Aristotle theorem prover (Harmonic)

Polignac's conjecture ("for every even `n` there are infinitely many primes `p` with `p + n`
prime") is an open problem, so what is proved here is a *conditional reduction* together with
unconditional partial results:

* `PolignacConjecture` : Dickson's conjecture (stated as an explicit hypothesis) implies
  Polignac's conjecture.
* `admissible_pair_of_even` : for even `n` the shift pair `{0, n}` is admissible (this is the
  arithmetic content of the reduction).
* `polignacPairs_zero_infinite` : the case `n = 0` unconditionally (infinitude of primes).
* `polignacPairs_odd_subsingleton` / `polignacPairs_finite_of_odd` : for odd `n` the set of
  such primes is contained in `{2}`, so the evenness hypothesis is necessary.
* `twin_primes_of_dickson` : Dickson's conjecture implies the twin prime conjecture.
-/

namespace Brockian.PolignacPrimes

open Set

/-- The set of primes `p` such that `p + n` is also prime. -/
def PolignacPairs (n : ℕ) : Set ℕ := {p : ℕ | p.Prime ∧ (p + n).Prime}

/-- A finite set `B` of shifts is *admissible* if for every prime `q` there is an `r` such that
no `r + b`, `b ∈ B`, is divisible by `q`. -/
def Admissible (B : Finset ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → ∃ r : ℕ, ∀ b ∈ B, ¬ (q ∣ r + b)

/-- **Dickson's conjecture** for the linear forms `x + b`, `b ∈ B`: every admissible finite set
of shifts is simultaneously prime infinitely often. This is an open conjecture and is used here
only as an explicit hypothesis. -/
def DicksonConjecture : Prop :=
  ∀ B : Finset ℕ, Admissible B → {x : ℕ | ∀ b ∈ B, (x + b).Prime}.Infinite

/-- For even `n`, the pair of shifts `{0, n}` is admissible. -/
theorem admissible_pair_of_even {n : ℕ} (hn : Even n) : Admissible {0, n} := by
  intro q hq
  have hq2 : 2 ≤ q := hq.two_le
  rcases Nat.Prime.eq_two_or_odd' hq with rfl | hodd
  · -- `q = 2` : take `r = 1`; both `1` and `1 + n` are odd.
    refine ⟨1, ?_⟩
    intro b hb
    obtain ⟨k, hk⟩ := hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with rfl | rfl
    · omega
    · subst hk
      omega
  · -- odd `q` : one of `r = 1`, `r = 2` works, since `q ≥ 3` leaves a free residue class.
    obtain ⟨m, hm⟩ := hodd
    have hq3 : 3 ≤ q := by omega
    by_cases h : q ∣ 1 + n
    · refine ⟨2, ?_⟩
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · intro hdvd
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega
      · intro hdvd
        have hsub := Nat.dvd_sub hdvd h
        have he : (2 + b) - (1 + b) = 1 := by omega
        rw [he] at hsub
        have := Nat.le_of_dvd one_pos hsub
        omega
    · refine ⟨1, ?_⟩
      intro b hb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl
      · intro hdvd
        have := Nat.le_of_dvd one_pos (by simpa using hdvd)
        omega
      · exact h

/-- The set cut out by the shift pair `{0, n}` is exactly `PolignacPairs n`. -/
theorem setOf_pair_eq (n : ℕ) :
    {x : ℕ | ∀ b ∈ ({0, n} : Finset ℕ), (x + b).Prime} = PolignacPairs n := by
  ext x
  simp only [Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton, PolignacPairs]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (Or.inl rfl), h n (Or.inr rfl)⟩
  · rintro ⟨h0, hn⟩ b (rfl | rfl)
    · simpa using h0
    · exact hn

/-- **Conditional reduction: Dickson's conjecture implies Polignac's conjecture.**
Assuming Dickson's conjecture, for every even `n` there are infinitely many primes `p` such
that `p + n` is also prime. -/
theorem PolignacConjecture (H : DicksonConjecture) :
    ∀ n : ℕ, Even n → (PolignacPairs n).Infinite := by
  intro n hn
  have h := H {0, n} (admissible_pair_of_even hn)
  rwa [setOf_pair_eq n] at h

/-- Dickson's conjecture implies the twin prime conjecture. -/
theorem twin_primes_of_dickson (H : DicksonConjecture) :
    {p : ℕ | p.Prime ∧ (p + 2).Prime}.Infinite :=
  PolignacConjecture H 2 (by decide)

/-- Unconditionally, the case `n = 0` of Polignac's conjecture holds: it is the infinitude of
the primes. -/
theorem polignacPairs_zero_infinite : (PolignacPairs 0).Infinite := by
  have : PolignacPairs 0 = {p : ℕ | p.Prime} := by
    ext p; simp [PolignacPairs]
  rw [this]
  exact Nat.infinite_setOf_prime

/-- For odd `n`, the only possible member of `PolignacPairs n` is `p = 2`. -/
theorem polignacPairs_odd_subsingleton {n : ℕ} (hn : Odd n) : PolignacPairs n ⊆ {2} := by
  rintro p ⟨hp, hpn⟩
  by_contra hne
  simp only [Set.mem_singleton_iff] at hne
  have hpodd : Odd p := hp.odd_of_ne_two hne
  obtain ⟨a, ha⟩ := hpodd
  obtain ⟨b, hb⟩ := hn
  have h2 : 2 ∣ p + n := ⟨a + b + 1, by omega⟩
  have := (Nat.Prime.eq_one_or_self_of_dvd hpn 2 h2)
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- Hence for odd `n` there are only finitely many such primes: evenness is necessary in
Polignac's conjecture. -/
theorem polignacPairs_finite_of_odd {n : ℕ} (hn : Odd n) : (PolignacPairs n).Finite :=
  Set.Finite.subset (Set.finite_singleton 2) (polignacPairs_odd_subsingleton hn)

end Brockian.PolignacPrimes

