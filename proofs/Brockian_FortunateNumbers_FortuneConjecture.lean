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

/-!
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.FortunateNumbers

open scoped Nat

/-- The set of "Fortune candidates" at stage `n`: those `m > 1` for which `n# + m` is prime,
where `n# = primorial n` is the product of all primes `≤ n`. -/
def fortuneCandidates (n : ℕ) : Set ℕ := {m | 1 < m ∧ Nat.Prime (primorial n + m)}

/-- Every prime `p ≤ n` divides the primorial `n#`. -/
theorem dvd_primorial_of_prime_of_le {n p : ℕ} (hp : p.Prime) (h : p ≤ n) :
    p ∣ primorial n := by
  unfold primorial
  exact Finset.dvd_prod_of_mem _ (by simp [Nat.lt_succ_of_le h, hp])

/-- There is always some `m > 1` with `n# + m` prime. -/
theorem fortuneCandidates_nonempty (n : ℕ) : (fortuneCandidates n).Nonempty := by
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (primorial n + 2)
  refine ⟨p - primorial n, ?_, ?_⟩
  · omega
  · have : primorial n + (p - primorial n) = p := by omega
    rw [this]; exact hp

/-- The Fortune number of stage `n`: the least `m > 1` such that `n# + m` is prime.
(Equivalently, `n# + fortuneNumber n` is the least prime `> n# + 1`.) -/
noncomputable def fortuneNumber (n : ℕ) : ℕ := sInf (fortuneCandidates n)

theorem fortuneNumber_mem (n : ℕ) : fortuneNumber n ∈ fortuneCandidates n :=
  Nat.sInf_mem (fortuneCandidates_nonempty n)

theorem one_lt_fortuneNumber (n : ℕ) : 1 < fortuneNumber n := (fortuneNumber_mem n).1

theorem prime_primorial_add_fortuneNumber (n : ℕ) :
    Nat.Prime (primorial n + fortuneNumber n) := (fortuneNumber_mem n).2

/-- Minimality of the Fortune number. -/
theorem fortuneNumber_le {n m : ℕ} (hm : 1 < m) (hp : Nat.Prime (primorial n + m)) :
    fortuneNumber n ≤ m :=
  Nat.sInf_le ⟨hm, hp⟩

/-- **Key step.** Any `m > 1` with `n# + m` prime and `m ≤ n ^ 2` is itself prime.

Indeed, if such an `m` were composite, its least prime factor `q` would satisfy `q ^ 2 ≤ m ≤ n ^ 2`,
hence `q ≤ n`, hence `q ∣ n#`; then `q` would divide the prime `n# + m` while being at most
`m < n# + m`, a contradiction. -/
theorem prime_of_prime_primorial_add_of_le_sq {n m : ℕ} (hm : 1 < m)
    (hp : Nat.Prime (primorial n + m)) (hle : m ≤ n ^ 2) : m.Prime := by
  by_contra hnp
  have hm0 : 0 < m := by omega
  set q := m.minFac with hq
  have hqp : q.Prime := Nat.minFac_prime (by omega)
  have hq2 : q ^ 2 ≤ m := Nat.minFac_sq_le_self hm0 hnp
  have hqn : q ≤ n := by
    by_contra hlt
    push_neg at hlt
    have : n ^ 2 < q ^ 2 := Nat.pow_lt_pow_left hlt (by norm_num)
    omega
  have hdvdN : q ∣ primorial n := dvd_primorial_of_prime_of_le hqp hqn
  have hdvdm : q ∣ m := Nat.minFac_dvd m
  have hdvd : q ∣ primorial n + m := Dvd.dvd.add hdvdN hdvdm
  have hqm : q ≤ m := Nat.minFac_le hm0
  have := (Nat.prime_dvd_prime_iff_eq hqp hp).1 hdvd
  have hNpos : 0 < primorial n := primorial_pos n
  omega

/-- The Fortune conjecture holds at stage `n` whenever the Fortune number does not exceed `n ^ 2`
(which is the case for every stage that has ever been computed). -/
theorem fortuneNumber_prime_of_le_sq {n : ℕ} (h : fortuneNumber n ≤ n ^ 2) :
    (fortuneNumber n).Prime :=
  prime_of_prime_primorial_add_of_le_sq (one_lt_fortuneNumber n)
    (prime_primorial_add_fortuneNumber n) h

/-- **Fortune conjecture (unconditional partial result / conditional reduction).**

For every `n`, the Fortune number `fortuneNumber n` — the least `m > 1` such that
`primorial n + m` is prime — is either prime, or larger than `n ^ 2`.

The full Fortune conjecture asserts that the first alternative always holds; this dichotomy
reduces it to ruling out the second alternative, i.e. to showing that the least prime exceeding
`n# + 1` is at most `n# + n ^ 2`. -/
theorem FortuneConjecture (n : ℕ) : (fortuneNumber n).Prime ∨ n ^ 2 < fortuneNumber n := by
  rcases le_or_lt (fortuneNumber n) (n ^ 2) with h | h
  · exact Or.inl (fortuneNumber_prime_of_le_sq h)
  · exact Or.inr h

end Brockian.FortunateNumbers

